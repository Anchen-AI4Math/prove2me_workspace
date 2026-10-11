"""Prepare versioned author controls from actual parser/graph facts; no Lean."""
import json, re, sys
sys.dont_write_bytecode = True
import prepare as p
import execute_oracles as e

HELPER = r'''
open Lean Meta
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def emitAuthorDefinition (name : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected actual definition: {name}"
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "definition_full_expression"),
    ("declaration",Json.str name.toString),
    ("level_parameters",toJson (d.levelParams.map Name.toString)),
    ("type_expression_repr",Json.str (reprStr d.type)),
    ("full_value_expression_repr",Json.str (reprStr d.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def emitAuthorProof (name : Name) (kind : String := "proof_full_type") : MetaM Unit := do
  let ci ← getConstInfo name
  unless ← isProp ci.type do throwError "Expected proof declaration: {name}"
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str kind),
    ("declaration",Json.str name.toString),
    ("full_type_expression_repr",Json.str (reprStr ci.type)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkAuthorWholeDefinition (name aliasName : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected actual definition"
  let .defnInfo a ← getConstInfo aliasName | throwError "Expected native-source byte alias"
  let typeEq ← isDefEq d.type a.type
  let valueEq ← isDefEq d.value a.value
  let typeRaw := Expr.equal d.type a.type
  let valueRaw := Expr.equal d.value a.value
  unless typeEq && valueEq && typeRaw && valueRaw do
    throwError "Full definition equality failed: {name}"
  let axs ← Lean.collectAxioms aliasName
  IO.println (Json.mkObj [("kind",Json.str "definition_whole_kernel_and_expr_equal"),
    ("declaration",Json.str name.toString),("alias",Json.str aliasName.toString),
    ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson valueEq),
    ("type_Expr_equal",toJson typeRaw),("full_value_Expr_equal",toJson valueRaw),
    ("original_type_expression_repr",Json.str (reprStr d.type)),
    ("alias_type_expression_repr",Json.str (reprStr a.type)),
    ("original_full_value_expression_repr",Json.str (reprStr d.value)),
    ("alias_full_value_expression_repr",Json.str (reprStr a.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkAuthorExactType (name expected : Name) : MetaM Unit := do
  let a ← getConstInfo name
  let b ← getConstInfo expected
  let eq ← isDefEq a.type b.type
  unless eq do throwError "Exact forall endpoint mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson eq),
    ("actual_type_repr",Json.str (reprStr a.type)),
    ("explicit_type_repr",Json.str (reprStr b.type))]).compress

private def emitAuthorPrivateHelpers (modules : List String) : MetaM Unit := do
  let env ← getEnv
  let mut names : List Name := []
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if modules.contains moduleName.toString && (name.isInternal || (privateToUserName? name).isSome) then
        names := name :: names
  for name in names do
    let ci ← getConstInfo name
    if ← isProp ci.type then
      emitAuthorProof name "private_helper_full_type"
    else if let .defnInfo _ := ci then
      emitAuthorDefinition name
  IO.println (Json.mkObj [("kind",Json.str "private_helper_inventory"),
    ("modules",toJson modules),("names",toJson (names.map Name.toString))]).compress
'''

EXACT = [r'''theorem exact_forall_polynomial : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → A = numeratorPartialNumerator m A :=
  @ENDPOINT@
''',r'''theorem exact_forall_global : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → ∀ (t : ℚ), (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  @ENDPOINT@
''',r'''theorem exact_forall_injective : ∀ (m : ℕ) (A B : ℚ[X]),
    A.natDegree < 9 * (m + 1) → B.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) → A = B :=
  @ENDPOINT@
''']
OPENS = '''set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapNumeratorPartialFractions
'''

def save(label, text):
    p.write(p.OUT/(label+'.lean'),text)
    p.write(p.PROJECT/(label+'.lean'),text)

def main():
    assert p.sha(p.OUT/'preparation-verification.json') == '2dddbef40532b0a7c423fae9d310423456ce4d2f2562223b95edff1869eea606'
    provenance = p.load(p.OUT/'integration-provenance.json')
    graph = e.rows(p.OUT/'decl_graph.jsonl')
    byname = {r['name']:r for r in graph}
    defs = [r['name'] for r in provenance['spanful_reached_records'] if r['kind']=='def']
    proofs = [r['name'] for r in provenance['spanful_reached_records'] if r['kind']=='theorem']
    auxiliary = [n for n in provenance['reached_names'] if n not in defs+proofs]
    assert len(defs)==11 and len(proofs)==34 and len(auxiliary)==1
    assert auxiliary[0].endswith('numeratorPartialBlock.eq_1')
    targets = [p.NS+'.'+n for n in p.TARGETS]
    newdefs = provenance['new_definition_names']
    aliases = []
    alias_records = []
    for name in newdefs:
        row = byname[name]
        parser = row['module'].rsplit('.',1)[1]
        source = (p.OUT/(parser+'-oracle-input.lean')).read_bytes()
        facts = e.rows(p.OUT/(parser+'-sketch_info.jsonl'))
        fact = next(f for f in facts if f['kind']=='decl' and f['declStart']['line']<=row['startLine']<=f['declEnd']['line'])
        a,b = fact['declStart']['offset'],fact['declEnd']['offset']
        # Keep native canonical dependencies: aliases share their surrounding
        # namespace, so unqualified references would otherwise resolve to
        # aliases emitted earlier rather than to the actual native constants.
        edits = []
        for ref in facts:
            if ref['kind']=='ref' and fact['valStart']['offset']<=ref['start']['offset']<b and ref['const'].startswith('ZetaNine.'):
                edits.append((ref['start']['offset']-a,ref['end']['offset']-a,ref['const'].encode()))
        snippet = source[a:b]
        for x,y,value in sorted(set(edits),reverse=True):
            snippet=snippet[:x]+value+snippet[y:]
        text = snippet.decode()
        leaf = name.rsplit('.',1)[1]
        renamed, count = re.subn(r'\bdef\s+'+re.escape(leaf)+r'\b','def '+leaf,text,count=1)
        assert count==1
        aliases.append(renamed)
        alias_records.append(dict(declaration=name,source_fact=fact,source=p.binding(p.OUT/(parser+'-oracle-input.lean')),
            canonical_reference_edits=[(x,y,v.decode()) for x,y,v in edits]))
    alias_source = '\nnamespace NativeSourceByteAliases\n'+'\n'.join(aliases)+'\nend NativeSourceByteAliases\n'
    rfls = ''.join('theorem whole_function_rfl_'+n.rsplit('.',1)[1]+' : '+n+' = NativeSourceByteAliases.'+n.rsplit('.',1)[1]+' := by rfl\n' for n in newdefs)
    native = 'PlatformNumeratorPFNativeReachableV1'
    block = '\nrun_meta do\n'+''.join('  emitAuthorDefinition `'+n+'\n' for n in defs)
    block += ''.join('  emitAuthorProof `'+n+'\n' for n in proofs)
    block += ''.join('  emitAuthorProof `'+n+' "generated_helper_full_type"\n' for n in auxiliary)
    save(native,'import '+p.NATIVE+'\nimport Lean\n'+HELPER+block)
    boundary = (p.PROJECT/'NativeNumeratorPFAuthorBoundaryControl.lean').read_text(encoding='utf-8-sig')
    boundary = boundary[boundary.index('theorem checked_zero_actual_jet'):boundary.index('theorem checked_n1_q1_actual_shifted_remainder')]
    boundaries = re.findall(r'^theorem (\w+)',boundary,re.M)
    assert len(boundaries)==10
    plan = p.load(p.OUT/'target-plan.json')
    staged=[]
    for i,target in enumerate(plan['targets']):
        suffix=p.SUFFIXES[i]
        label='PlatformNumeratorPFStaged_'+suffix+'_V1'
        checked=p.NS+'.checked_'+p.TARGETS[i]
        actual_targets=[checked if j==i else n for j,n in enumerate(targets)]
        named_proofs=[checked if n==targets[i] else n for n in proofs]
        control_boundary=boundary.replace(p.TARGETS[i],'checked_'+p.TARGETS[i])
        exact=''.join(text.replace('@ENDPOINT@',n) for text,n in zip(EXACT,actual_targets))
        text='import '+target['local_solution'].removesuffix('.lean').replace('/','.')+'\nimport Lean\n'+OPENS
        text+=alias_source+rfls+exact+control_boundary+HELPER+'\nrun_meta do\n'
        text+=''.join('  emitAuthorDefinition `'+n+'\n' for n in defs)
        text+=''.join('  emitAuthorProof `'+n+'\n' for n in named_proofs+['solution'])
        text+=''.join('  emitAuthorProof `'+n+' "generated_helper_full_type"\n' for n in auxiliary)
        text+=''.join('  checkAuthorWholeDefinition `'+n+' `NativeSourceByteAliases.'+n.rsplit('.',1)[1]+'\n' for n in newdefs)
        text+=''.join('  emitAuthorProof `whole_function_rfl_'+n.rsplit('.',1)[1]+' "whole_function_rfl"\n' for n in newdefs)
        text+=''.join('  emitAuthorProof `exact_forall_'+s+' "exact_forall_endpoint_proof"\n' for s in p.SUFFIXES)
        text+=''.join('  checkAuthorExactType `'+n+' `exact_forall_'+s+'\n' for n,s in zip(actual_targets,p.SUFFIXES))
        text+='  checkAuthorExactType `solution `exact_forall_'+suffix+'\n'
        text+=''.join('  emitAuthorProof `'+n+' "closed_boundary_proof"\n' for n in boundaries)
        helper_modules=[target['local_solution'].removesuffix('.lean').replace('/','.'),
                        'Definitions.Def_ZetaNine_CoefficientMapNumeratorPF']
        text+='  emitAuthorPrivateHelpers ['+', '.join(json.dumps(x) for x in helper_modules)+']\n'
        save(label,text)
        staged.append(dict(label=label,solution=target['local_solution'],renamed_actual=checked,
            named_proof_count=35,generated_auxiliary_count=1,definitions_count=11,
            exact_forall_count=3,kernel_endpoint_count=4,new_definition_alias_kernel_count=5,
            whole_function_rfl_count=5,boundary_count=10))
    p.dump(p.OUT/'author-controls-plan-2026-10-07.json',dict(
        role='same batch resumed platform AUTHOR',Lean_executed=False,native_control=native,
        native_definitions=defs,native_proofs=proofs,generated_auxiliaries=auxiliary,
        native_source_alias_spans=alias_records,staged_controls=staged,
        excluded_Data_Connection_boundaries=['checked_n1_q1_actual_shifted_remainder','checked_n1_q1_actual_remainder_reconstruction'],
        reason='Their definitions are excluded from actual three-endpoint declaration reachability; original native controls remain frozen.',
        raw_full_expressions_used=True,DAG_used=False))
    print('Prepared 1 native and 3 staged author controls; no Lean execution.')

if __name__=='__main__': main()

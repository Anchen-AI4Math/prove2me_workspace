"""Future actual graph/parser-driven constructor closure; no import-time Lean calls.

This module deliberately refuses absent oracle facts. Its functions are prepared,
not executed. The caller must have actual successful source/graph/parser/header
receipts and explicitly allocated serial Lean execution before using them.
"""

NS='ZetaNine.CoefficientMapConnection'
ALIAS_NS=NS+'ValueComparison'
PROOF_DEF='connectionLinearMap'
HELPERS=['coefficientPolynomial_add','coefficientPolynomial_smul','connectionOperator_add','connectionOperator_smul']

def prefix(c,namespace,native=False):
 imports=([c['NATIVE']] if native else [])+c['MATHLIB']
 return '\n'.join('import '+m for m in imports)+(
  '\n\nset_option autoImplicit false\nnoncomputable section\nopen Polynomial\n\nnamespace '+namespace+'\n\n')

def helper_binding(c,full):
 d=c['declaration'](full);a,v=d['declStart']['offset'],d['valStart']['offset']
 bindings=[r for r in c['refs'] if r['const']==full and a<=r['start']['offset']<v]
 assert len(bindings)==1 and d['docstring'] is None and d['privateTok'] is None
 binding=bindings[0]
 assert c['source'][a:binding['start']['offset']].decode().strip()=='theorem'
 assert c['source'][binding['start']['offset']:binding['end']['offset']].decode()==full.rsplit('.',1)[1]
 return d,binding

def create_type_oracle(c,helpers):
 assert c.get('serial_Lean_lane_allocated') is True, 'A parent allocated serial Lean lane is required.'
 # Eleven original data Def spans suffices for the actual four helper types.
 # The constructor is intentionally excluded until its real proof refs close.
 ordinary=[(name,d) for name,d in zip(c['DEFS'],c['def_facts']) if name!=PROOF_DEF]
 assert len(ordinary)==11
 code=prefix(c,ALIAS_NS,True)+'\n\n'.join(c['source'][d['declStart']['offset']:d['declEnd']['offset']].decode() for _,d in ordinary)
 code+='\n\nend '+ALIAS_NS+'\n\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\n\n'
 code+='''private def remapConnectionName (n : Name) : Name :=
  if n == `ZetaNine.CoefficientMapConnection then
    `ZetaNine.CoefficientMapConnectionValueComparison
  else match n with
    | .str p s => .str (remapConnectionName p) s
    | .num p i => .num (remapConnectionName p) i
    | .anonymous => .anonymous

run_meta do
  for name in ['''+', '.join('`'+n for n in helpers)+'''] do
    let ci ← getConstInfo name
    let type ← ppExpr ci.type
    let aliasExpr := ci.type.replace fun e => match e with
      | .const n ls =>
          if (`ZetaNine.CoefficientMapConnection).isPrefixOf n then
            some (.const (remapConnectionName n) ls)
          else none
      | _ => none
    let aliasType ← ppExpr aliasExpr
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("original_type",Json.str type.pretty),("alias_type",Json.str aliasType.pretty),
      ("original_type_expression_repr",Json.str (reprStr ci.type)),
      ("remapped_type_expression_repr",Json.str (reprStr aliasExpr)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 for p in [c['OUT']/'embedded-types.lean',c['PROJECT']/'embedded-types.lean']:c['write'](p,code)
 c['run']('embedded-types',['lake','env','lean','embedded-types.lean'])
 return {r['declaration']:r for r in c['rows'](c['OUT']/'embedded-types.log')}

def create_definitions(c):
 assert c.get('serial_Lean_lane_allocated') is True, 'A parent allocated serial Lean lane is required.'
 assert c['actual_oracles_successful'] is True, 'No generation from placeholders or regex facts.'
 assert c['NS']==NS and c['ALIAS_NS']==ALIAS_NS
 helpers=set()
 closures={}
 for name in HELPERS:
  full=NS+'.'+name
  reached=c['closure']([full])
  declarations=[c['byname'][n] for n in reached if c['byname'][n]['module']==c['NATIVE']
                and c['byname'][n]['kind']=='theorem' and c['byname'][n]['startLine']>0]
  declarations.sort(key=lambda d:d['startLine'])
  closures[full]=[d['name'] for d in declarations]
  helpers.update(closures[full])
 assert helpers=={NS+'.'+n for n in HELPERS}, 'Unexpected actual constructor proof dependency.'
 assert not any('bijective' in n or 'kernel_zero' in n for n in helpers)
 typereport=create_type_oracle(c,sorted(helpers))
 assert set(typereport)==helpers
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in typereport.values())
 definitions={};provenance=[]
 for alias,namespace in [(False,NS),(True,ALIAS_NS)]:
  chunks=[]
  for name,d in zip(c['DEFS'],c['def_facts']):
   a,b=d['declStart']['offset'],d['declEnd']['offset'];edits=[]
   if name==PROOF_DEF:
    for helper in HELPERS:
     full=NS+'.'+helper
     occurrences=[r for r in c['refs'] if r['const']==full and a<=r['start']['offset']<r['end']['offset']<=b]
     assert occurrences
     for occurrence in occurrences:
      localchunks=[];localfacts=[]
      for h in closures[full]:
       hd,binding=helper_binding(c,h);hs,he=hd['declStart']['offset'],hd['declEnd']['offset']
       end=binding['start']['offset']
       snippet=c['edit'](c['source'][hs:he],[(0,end-hs,b'have ')]).decode()
       localchunks.append('\n'.join('    '+line for line in snippet.splitlines()))
       localfacts.append({'name':h,'declaration_fact':hd,'binding_fact':binding,
                          'only_prefix_edit':{'start':hs,'end':end,'replacement':'have '}})
      typ=typereport[full]['alias_type' if alias else 'original_type']
      term='((by\n'+'\n'.join(localchunks)+'\n    exact '+helper+') :\n    ('+typ.replace('\n','\n    ')+'))'
      x,y=occurrence['start']['offset'],occurrence['end']['offset']
      assert c['source'][x:y].decode()==helper
      edits.append((x-a,y-a,term.encode()))
      if not alias:provenance.append({'definition':NS+'.'+name,'actual_proof_callee':full,
        'reference_fact':occurrence,'helper_names':closures[full],'helper_facts':localfacts,
        'actual_original_type':typereport[full]['original_type'],
        'actual_semantically_remapped_alias_type':typereport[full]['alias_type'],
        'replacement_proof_term':term,'data_fields_edited':False})
   chunks.append(c['edit'](c['source'][a:b],edits).decode())
  definitions[alias]=prefix(c,namespace,alias)+'\n\n'.join(chunks)+'\n\nend '+namespace+'\n'
 c['dump'](c['OUT']/'embedded-field-provenance.json',{
  'actual_reference_count':len(provenance),'actual_helper_names':sorted(helpers),
  'ordinary_data_Definitions':11,'proof_bearing_Definitions':1,'new_global_helper_theorems':[],
  'actual_parser_spans_only':True,'fields':provenance,'full_native_kernel_comparison_pending':True})
 return definitions[False],definitions[True],provenance

def create_value_comparison(c):
 code='import NativeValueComparisonDefinition\nimport Lean\n\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\n\n'
 for name in c['DEFS']:
  code+='theorem native_value_'+name+'_eq : '+ALIAS_NS+'.'+name+' = '+NS+'.'+name+' := rfl\n\n'
 code+='theorem native_data_connectionLinearMap (n : Nat) (c : Fin 15 → Rat) (i : Fin 15) :\n  '+ALIAS_NS+'.connectionLinearMap n c i = ('+NS+'.connectionOperator n ('+NS+'.inputP c) ('+NS+'.inputQ c)).coeff (2 * i.val) := rfl\n\n'
 code+='run_meta do\n  for (name,aliasName) in ['+', '.join('(`'+NS+'.'+n+', `'+ALIAS_NS+'.'+n+')' for n in c['DEFS'])+'] do\n'
 code+='''    let .defnInfo d ← getConstInfo name | throwError "Native constant is not a def"
    let .defnInfo a ← getConstInfo aliasName | throwError "Alias constant is not a def"
    let typeEq ← isDefEq d.type a.type
    let valueEq ← isDefEq d.value a.value
    unless typeEq && valueEq do throwError "Actual native/alias whole definition differs: {name}"
    let nv ← ppExpr d.value
    let av ← ppExpr a.value
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "native_alias_full_kernel_equality"),
      ("declaration",Json.str name.toString),("alias_declaration",Json.str aliasName.toString),
      ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson valueEq),
      ("original_expression_repr",Json.str (reprStr d.value)),
      ("alias_expression_repr",Json.str (reprStr a.value)),
      ("original_value_pp_with_proofs",Json.str nv.pretty),
      ("alias_value_pp_with_proofs",Json.str av.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 names=['native_value_'+n+'_eq' for n in c['DEFS']]+['native_data_connectionLinearMap']
 code+='  for name in ['+', '.join('`'+n for n in names)+'] do\n'
 code+='''    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "rfl_or_data_equality"),
      ("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 for p in [c['OUT']/'native-value-comparison.lean',c['PROJECT']/'native-value-comparison.lean']:c['write'](p,code)

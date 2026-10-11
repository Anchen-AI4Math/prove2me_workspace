"""Pure Outputs author source-only preparation. Never invokes Lean or Lake."""
from pathlib import Path
import hashlib,json,sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/oa1'
NATIVE='missions.zeta9.formalization.CoefficientMapFormalTransportOutputs'
NS='ZetaNine.CoefficientMapFormalTransportOutputs'
CANDIDATE=TASK/'formalization/CoefficientMapFormalTransportOutputs.lean'
VERIFIED_JETS=TASK/'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04/JetsVerifiedSource.lean'
JETS_SHA='ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE_SHA=hashlib.sha256(CANDIDATE.read_bytes()).hexdigest()


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while block:=f.read(8*1024*1024):h.update(block)
    return h.hexdigest()


def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))


def write(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(data if isinstance(data,bytes) else data.encode('utf-8'))


def dump(path,doc):write(path,json.dumps(doc,ensure_ascii=False,indent=2)+'\n')


def binding(path):return dict(task_relative=path.relative_to(TASK).as_posix(),bytes=path.stat().st_size,sha256=sha(path))


def statement_headers(raw):
    """Static exact text inventory only; not actual Lean parser/type evidence."""
    records=[]
    lines=raw.decode('utf-8-sig').splitlines(keepends=True)
    for i,line in enumerate(lines):
        if line.startswith('theorem '):
            text=''.join(lines[i:]);assert ':=' in text
            header=text.split(':=',1)[0].rstrip()
            name=line.split()[1]
            records.append(dict(name=name,header=header))
    return records


def native_gate():
    inputs=load(OUT/'source-inputs.json')
    for r in inputs['sources']:
        path=Path(r['origin_absolute'])
        assert path.stat().st_size==r['bytes'] and sha(path)==r['sha256']
    assert sha(VERIFIED_JETS)==JETS_SHA
    for r in inputs['prior_freeze_descriptors']:
        path=TASK/r['task_relative']
        assert path.stat().st_size==r['bytes'] and sha(path)==r['sha256']
    return inputs


ARGS={
 'weightedR_eval_one_zero':'n hn W','quartic_properMultiplier':'n W hW',
 'weighted_boundary_sum_zero':'n hn W hW','remainder_boundary_sum_zero':'n hn q hq',
 'sum_extendedOldCoefficient_harmonic':'n s P','sum_extendedRemainderCoefficient_harmonic':'n s q',
 'sum_previousRemainderCoefficient_harmonic':'n s q','sum_harmonic_succ':'N s f',
 'actual_chosen_harmonic_order_transport':'n hn r s hs1 hs9',
 'actual_chosen_constantTerm_correction':'n hn r','actual_chosen_constantTerm_transport':'n hn r',
 'actual_chosen_five_output_transport':'n hn r','actual_chosen_Gamma_row_transport':'n hn r',
 'actual_five_output_matrix_transport':'n hn','n_one_five_output_transport':'r','n_one_matrix_transport':''}

OPENS='''open ZetaNine
open ZetaNine.HarmonicStability ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapFormalTransportBounds
open ZetaNine.CoefficientMapFormalTransportOutputs
'''


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not PROJECT.exists(),'New own project must be absent before pure creation.'
    assert not (OUT/'preparation-verification.json').exists()
    assert sha(VERIFIED_JETS)==JETS_SHA
    old_author=VERIFIED_JETS.parent/'author-audit.json'
    assert sha(old_author)=='8b3f2da6d46de5f320ce2d6033535502e72dc79c46703c321211f646f6ccd3f3'
    assert load(old_author)['verdict']=='PASS'
    copied=[];done=set()
    def visit(module):
        if module in done:return
        done.add(module)
        origin=VERIFIED_JETS if module.endswith('.CoefficientMapFormalTransportJets') else ROOT/(module.replace('.','/')+'.lean')
        assert origin.is_file(),module
        raw=origin.read_bytes()
        for line in raw.decode('utf-8-sig').splitlines():
            if line.startswith('import '):
                for dep in line.removeprefix('import ').split():
                    if dep.startswith('missions.zeta9.') or dep.startswith('Definitions.'):
                        visit(dep)
                    else:assert dep.startswith('Mathlib.') or dep in ['Mathlib','Lean']
        relative=module.replace('.','/')+'.lean'
        target=PROJECT/relative
        snapshot=PROJECT/'s'/('i'+str(len(copied)).zfill(3))
        write(target,raw);write(snapshot,raw)
        copied.append(dict(module=module,project_relative=relative,origin_absolute=str(origin),
            bytes=len(raw),sha256=sha(origin),initial_project_copy=binding(target),
            immutable_initial_snapshot=binding(snapshot)))
    visit(NATIVE)
    assert len(copied)==21 and copied[-1]['module']==NATIVE
    assert all(r['sha256']==JETS_SHA for r in copied if r['module'].endswith('.CoefficientMapFormalTransportJets'))
    inventory=statement_headers(CANDIDATE.read_bytes())
    assert len(inventory)==16 and {r['name'] for r in inventory}==set(ARGS)
    dump(OUT/'static-original-header-inventory.json',dict(role='UNCOMPILED exact source text inventory, not graph',records=inventory))
    dump(OUT/'endpoint-contracts.json',dict(status='UNCOMPILED_EXACT_SOURCE_ENDPOINT_CONTRACTS',
        primary_endpoints=[r for r in inventory if r['name'] in
            ['actual_chosen_constantTerm_transport','actual_chosen_five_output_transport','actual_five_output_matrix_transport']],
        all16_contracts=inventory,domain='Every n>=1 and all actual chosen r:Fin5',
        actual_matrix_direction='actualFMatrix (n+2) = connectionGamma n * actualFMatrix n',
        PF_properness_derived_from_genuine_P_degree4_and_q_degree9=True,
        new_transport_PF_zeta_independence_invertibility_or_Even_assumptions=False,
        statements_actually_parsed_or_compiled=False))
    controls=[]
    for module,expected in [('IndependentExprDagV3','1322612913bdc66d360720f64f9c72fa6047234e0717024ebb01a6c1303044e7'),
        ('IndependentExprDagValidationV3','5c8ef7f4dc5c512497479b47ec4cd50280042febcc7ed45ed793360ad75ab693')]:
        source=TASK/'.rt/ni1'/(module+'.lean');assert sha(source)==expected
        immutable=OUT/'controls'/(module+'.lean');write(immutable,source.read_bytes())
        target=PROJECT/(module+'.lean');write(target,source.read_bytes())
        controls.append(dict(module=module,project_relative=module+'.lean',
            immutable_source=binding(immutable),initial_project_copy=binding(target)))
    prefix='import '+NATIVE+'\nimport IndependentExprDagV3\nimport Lean\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n'+OPENS
    body=prefix+'\nnamespace OutputsAuthorExpected\n'
    for r in inventory:
        body+=r['header'].replace('theorem '+r['name'],'theorem expected_'+r['name'],1)+' := by\n  exact '+NS+'.'+r['name']+' '+ARGS[r['name']]+'\n\n'
    body+='end OutputsAuthorExpected\nopen Lean Meta\nset_option maxHeartbeats 0\nset_option maxRecDepth 20000\nrun_meta do\n'
    pairs=', '.join('(`'+NS+'.'+r['name']+', `OutputsAuthorExpected.expected_'+r['name']+')' for r in inventory)
    body+='  for (actual,expected) in ['+pairs+'] do\n'+'''    let .thmInfo a ← getConstInfo actual | throwError "Actual declaration is not a theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Expected declaration is not a theorem: {expected}"
    let same ← isDefEq a.type b.type
    unless same do throwError "Original complete type mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard theorem axioms: {actual}"
    let sourceDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let expectedDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_and_proof_expression_dag",sourceDag),
      ("full_expected_type_and_proof_expression_dag",expectedDag),
      ("all_fields_Expr_equal_roundtrip",toJson true),("type_kernel_equal",toJson same),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
'''
    boundary=prefix+'\nnamespace OutputsAuthorBoundary\n'+(OUT/'boundary.template.lean').read_text(encoding='utf-8-sig')+'\nend OutputsAuthorBoundary\n'
    bnames=[r['name'] for r in statement_headers(boundary.encode())]
    assert len(bnames)==9
    boundary+='open Lean Meta\nset_option maxHeartbeats 0\nrun_meta do\n  for actual in ['+', '.join('`OutputsAuthorBoundary.'+n for n in bnames)+'] do\n'+'''    let .thmInfo a ← getConstInfo actual | throwError "Boundary declaration is not a theorem"
    let aa ← collectAxioms actual
    unless aa.toList.all (fun n => [`propext,`Classical.choice,`Quot.sound].contains n) do
      throwError "Nonstandard boundary axioms"
    let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_closed_boundary"),
      ("declaration",Json.str actual.toString),("complete_type_and_proof_expression_dag",payload),
      ("all_fields_Expr_equal_roundtrip",toJson true),
      ("axioms",toJson (aa.toList.map Name.toString))]).compress
'''
    for module,text in [('OutputsFullTypeAudit',body),('OutputsBoundaryAudit',boundary)]:
        immutable=OUT/'controls'/(module+'.lean');write(immutable,text)
        target=PROJECT/(module+'.lean');write(target,text)
        controls.append(dict(module=module,project_relative=module+'.lean',
            immutable_source=binding(immutable),initial_project_copy=binding(target)))
    helper=TASK/'.rt/ja1/lean_call.py'
    write(PROJECT/'lean_call.py',helper.read_bytes())
    for name in ['lake-manifest.json','lean-toolchain']:write(PROJECT/name,(ROOT/name).read_bytes())
    assert next(r for r in load(PROJECT/'lake-manifest.json')['packages'] if r['name']=='mathlib')['rev']==REV
    globs=', '.join('.one `'+r['module'] for r in copied if not r['module'].startswith('Definitions.'))
    cnames=', '.join('`'+r['module'] for r in controls)
    write(PROJECT/'lakefile.lean','import Lake\nopen Lake DSL\npackage zeta9OutputsNativeAuthor where\n  buildDir := "b"\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'+REV+'"\nlean_lib Native where\n  roots := #[`'+NATIVE+']\n  globs := #['+globs+']\nlean_lib Definitions\nlean_lib Controls where\n  roots := #['+cnames+']\n  globs := #['+', '.join('.one '+x for x in cnames.split(', '))+']\n')
    modules=copied+controls
    write(PROJECT/'resolver.lean','import Lean\nopen Lean\nrun_meta do\n  for name in ['+', '.join('`'+r['module'] for r in modules)+'] do\n    let path ← findOLean name\n    IO.println (Json.mkObj [("module",Json.str name.toString),("olean",Json.str path.toString)]).compress\n')
    paths=[dict(module=r['module'],path=str((PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()),
        path_plus_64=len(str((PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()))+64) for r in modules]
    for r in paths:r['passed']=r['path_plus_64']<=259
    assert all(r['passed'] for r in paths)
    prior=[binding(path) for path in [old_author,VERIFIED_JETS,
        TASK/'formalization/CoefficientMapFormalTransportJets.lean',
        TASK/'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04/preparation-verification.json',
        TASK/'verification/formalization-coefficient-map-formal-transport-jets-preparation-2026-10-04/preparation-manifest.json']]
    dump(OUT/'source-inputs.json',dict(sources=copied,prior_freeze_descriptors=prior,
        verified_Jets_override_sha256=JETS_SHA,shared_initial_Jets_never_used_as_compiler_input=True,
        source_import_schedule_not_actual_Lean_graph=True,objects_borrowed=False))
    dump(OUT/'preparation-state.json',dict(status='PURE_NATIVE_AUTHOR_PREPARATION',Lean_invocations=0,
        project_absent_before_creation=True,build_cache_initially_absent=True,package_junction_initially_absent=True,
        source=copied,controls=controls,path_checks=paths,original_exact_headers=inventory,boundary_names=bnames,
        future_actual_calls=dict(runtime=1,fresh_native_sources=21,controls=4,resolver=1,total=27),
        actual_PASS_claimed=False,Root_API_scope_credentials_modified=False))
    native_gate()
    assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
    print(json.dumps(dict(status='PURE_SOURCE_ONLY_PREPARATION',native_sources=21,
        static_headers=16,closed_boundary_candidates=9,controls=4,planned_actual_calls=27,
        max_path_plus64=max(r['path_plus_64'] for r in paths),candidate_sha256=sha(CANDIDATE),Lean_invocations=0)))


if __name__=='__main__':main()

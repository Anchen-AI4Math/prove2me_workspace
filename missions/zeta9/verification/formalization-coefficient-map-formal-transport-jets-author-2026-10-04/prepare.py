"""Pure fresh Jets author setup; importing this module runs no Lean/Lake."""
from pathlib import Path
import hashlib,json,sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ja1'
PREP=TASK/'verification/formalization-coefficient-map-formal-transport-jets-preparation-2026-10-04'
PREP_SHA='ae88f1dc44325ae90f371ba47010ade3d6be8fd6895271db7dc4ad19ca8559f1'
SOURCE_SHA='b081ed2a0c6382d68db5f325e8e8169e0536914cd56b7d52549cb5312f5fe00d'
NATIVE='missions.zeta9.formalization.CoefficientMapFormalTransportJets'
NS='ZetaNine.CoefficientMapFormalTransportJets'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
ARGUMENTS=['m j hj','m j hj','m','m j hj','j hj','m j hj1 hj','m j A hj',
    'm j A hj1 hj','m j s A hs1 hs9 hA','m j s A hj hs1 hs9','m j s A hj hs1 hs9',
    'n j s A hj hs1 hs9','m j A B','m j A B','m j a A','m j s A B','m j s a A',
    'n hn r j s hj hs1 hs9','n hn r s hs1 hs9','n hn r s hs1 hs9','N f','N f',
    'n s P','n s q','n s q','n hn r s hs1 hs9']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def write(path,text):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(text if isinstance(text,bytes) else text.encode('utf-8'))
def dump(path,doc):write(path,json.dumps(doc,ensure_ascii=False,indent=2)+'\n')
def binding(path):return dict(task_relative=path.relative_to(TASK).as_posix(),
    bytes=path.stat().st_size,sha256=sha(path))


def native_gate():
    path=PREP/'preparation-manifest.json'
    assert sha(path)==PREP_SHA
    original=load(path)
    assert len(original['files'])==5 and len(original['actual_import_scheduling_only'])==19
    assert original['Lean_invocations']==0 and not original['kernel_PASS_claimed']
    for row in original['files']+original['actual_import_scheduling_only']:
        source=ROOT/row['root_relative']
        assert source.stat().st_size==row['bytes'] and sha(source)==row['sha256'],str(source)
    assert sha(ROOT/original['source']['root_relative'])==SOURCE_SHA
    return original


def statement_headers(raw):
    """Static exact-text inventory, never a parser/type/graph result."""
    text=raw.decode('utf-8-sig')
    starts=[];offset=0
    for line in text.splitlines(keepends=True):
        if line.startswith('theorem '):starts.append(offset)
        offset+=len(line)
    result=[]
    for start in starts:
        end=text.index(':= by',start)
        head=text[start:end].strip()
        result.append(dict(name=head.split()[1],header=head))
    return result


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not PROJECT.exists(),'ja1 must initially be absent.'
    assert not (OUT/'preparation-verification.json').exists()
    original=native_gate();sources=[]
    for index,row in enumerate(original['actual_import_scheduling_only']):
        relative=row['module'].replace('.','/')+'.lean'
        source=ROOT/row['root_relative']
        assert relative==row['root_relative']
        write(PROJECT/relative,source.read_bytes())
        snapshot=PROJECT/'s'/('i'+str(index).zfill(3))
        write(snapshot,source.read_bytes())
        sources.append(dict(row,project_relative=relative,
            immutable_initial_snapshot=binding(snapshot),initial_project_copy=binding(PROJECT/relative)))
    candidate=ROOT/original['source']['root_relative']
    inventory=statement_headers(candidate.read_bytes())
    assert len(inventory)==len(ARGUMENTS)==26
    dump(OUT/'static-original-header-inventory.json',dict(role='Uncompiled exact header inventory only',
        actual_type_or_parser_claimed=False,records=inventory,
        original_source_sha256=SOURCE_SHA))
    preamble='''import '''+NATIVE+'''
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportNumerators
open ZetaNine.CoefficientMapNumeratorPartialFractions
open ZetaNine.CoefficientMapFormalTransportJets
namespace JetsAuthorExpected
'''
    body=preamble
    for row,args in zip(inventory,ARGUMENTS):
        head=row['header'].replace('theorem '+row['name']+' ', 'theorem expected_'+row['name']+' ',1)
        body+='\n'+head+' := by\n  exact '+NS+'.'+row['name']+' '+args+'\n'
    body+='\nend JetsAuthorExpected\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.proofs true\nrun_meta do\n'
    body+='  for (actual,expected) in ['+', '.join('(`'+NS+'.'+r['name']+', `JetsAuthorExpected.expected_'+r['name']+')' for r in inventory)+'] do\n'
    body+='''    let .thmInfo a ← getConstInfo actual | throwError "Actual source declaration is not a theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Expected closed declaration is not a theorem: {expected}"
    let same ← isDefEq a.type b.type
    unless same do throwError "Actual complete type differs from the original frozen header: {actual}"
    let aa ← Lean.collectAxioms actual
    let ba ← Lean.collectAxioms expected
    let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard source/expected axioms: {actual}"
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_expression_repr",Json.str (reprStr a.type)),
      ("full_expected_type_expression_repr",Json.str (reprStr b.type)),
      ("full_source_proof_expression_repr",Json.str (reprStr a.value)),
      ("type_kernel_equal",toJson same),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
'''
    controls=[]
    for name,code in [('JetsFullTypeAudit',body),('JetsBoundaryAudit',(OUT/'boundary.template.lean').read_bytes())]:
        write(OUT/(name+'.lean'),code);write(PROJECT/(name+'.lean'),code)
        controls.append(dict(module=name,project_relative=name+'.lean',
            immutable_source=binding(OUT/(name+'.lean')),
            initial_project_copy=binding(PROJECT/(name+'.lean'))))
    modules=[r['module'] for r in sources]+[r['module'] for r in controls]
    resolver='import Lean\nopen Lean\nrun_meta do\n  for name in ['+', '.join('`'+m for m in modules)+'] do\n'
    resolver+='''    let path ← findOLean name
    IO.println (Json.mkObj [("module",Json.str name.toString),("olean",Json.str path.toString)]).compress
'''
    write(OUT/'resolver.lean',resolver);write(PROJECT/'resolver.lean',resolver)
    helper=(TASK/'formalization/platform/coefficient-map-matrix/lean_call.template.py').read_bytes()
    helper=helper.replace(b'MATRIX_RUN_PATHS_RECEIPT',b'JETS_RUN_PATHS_RECEIPT')
    write(OUT/'lean_call.template.py',helper);write(PROJECT/'lean_call.py',helper)
    lake='''import Lake
open Lake DSL
package zeta9JetsNativeAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'''+REV+'''"
lean_lib Native where
  roots := #[`'''+NATIVE+''']
  globs := #[ '''+', '.join('.one `'+r['module'] for r in sources if r['module'].startswith('missions.'))+''' ]
lean_lib Definitions
lean_lib Controls where
  roots := #[`JetsFullTypeAudit, `JetsBoundaryAudit]
  globs := #[.one `JetsFullTypeAudit, .one `JetsBoundaryAudit]
'''
    write(PROJECT/'lakefile.lean',lake)
    for name in ['lake-manifest.json','lean-toolchain']:write(PROJECT/name,(ROOT/name).read_bytes())
    assert (PROJECT/'lean-toolchain').read_text(encoding='utf-8').strip()=='leanprover/lean4:v4.33.1'
    assert next(r for r in load(PROJECT/'lake-manifest.json')['packages'] if r['name']=='mathlib')['rev']==REV
    paths=[]
    for module in modules:
        obj=PROJECT/'b/lib/lean'/(module.replace('.','/')+'.olean')
        row=dict(module=module,path=str(obj),path_plus_64=len(str(obj))+64,passed=len(str(obj))+64<=259)
        assert row['passed'],row
        paths.append(row)
    dump(OUT/'preparation-state.json',dict(status='PURE_NATIVE_AUTHOR_PREPARATION',Lean_invocations=0,
        original_preparation_sha256=PREP_SHA,original_source_sha256=SOURCE_SHA,
        original5bindings_unchanged=True,source=sources,controls=controls,
        fresh_project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        project_initially_absent=True,build_cache_absent=True,package_junction_absent=True,
        compiler_objects_borrowed=False,shared_fixed_Mathlib_packages_only=True,
        source_count=19,static_source_inventory_count=26,expected_closed_types=26,
        future_boundary_proof_count=15,source_inventory_is_not_actual_graph=True,
        path_checks=paths,future_actual_calls=dict(runtime=1,fresh_native_sources=19,controls=2,resolver=1,total=23),
        actual_PASS_claimed=False,Root_API_scope_credentials_modified=False))
    print(json.dumps(dict(status='PURE_NATIVE_AUTHOR_PREPARATION',source19_copied=True,
        static_inventory=26,boundary_candidates=15,future_actual_calls=23,
        longest_path_plus64=max(r['path_plus_64'] for r in paths),Lean_invocations=0)))


if __name__=='__main__':main()

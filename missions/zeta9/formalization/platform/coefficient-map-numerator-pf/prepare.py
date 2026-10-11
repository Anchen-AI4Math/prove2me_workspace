"""Pure GenericNumeratorPF platform preparation; never invokes Lean/Lake.

Import-line traversal below schedules source compilation only. New declaration
graphs, reference spans, minimal definition membership and proof closure are
explicitly pending genuine Stage1/Stage2 oracles after a Root lane grant.
"""
from pathlib import Path
import hashlib, json, sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/pa1'
NATIVE = 'missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions'
NS = 'ZetaNine.CoefficientMapNumeratorPartialFractions'
DATA_NS = 'ZetaNine.CoefficientMapFormalTransportData'
TAG = 'CoefficientMapNumeratorPF'
REV = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE_SHA = '2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77'
AUTHOR_SHA = '7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5'
INDEPENDENT_SHA = '49a69e8a35d4325c77aee2543a5aa7aed630838bcdfa6dbd16225f35e0c7dc97'
AUTHOR = TASK / 'verification/formalization-coefficient-map-numerator-pf-2026-10-04'
INDEPENDENT = TASK / 'verification/formalization-coefficient-map-numerator-pf-independent-2026-10-04'
DEFS = ['numeratorLocalTruncation', 'numeratorPartialBlock',
        'numeratorPartialNumerator', 'numeratorCandidateClearedSeries']
DATA_CANDIDATES = ['numeratorClearedSeries', 'numeratorLocalCoefficient']
TARGETS = ['actual_numerator_polynomial_partial_fractions',
           'actual_numerator_global_partial_fractions',
           'actual_numerator_local_coefficients_injective']
SUFFIXES = ['polynomial', 'global', 'injective']
ARGS = ['m A hproper', 'm A hproper t hregular', 'm A B hA hB heq']
STD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding='utf-8-sig'))
def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value if isinstance(value, bytes) else value.encode('utf-8'))
def dump(path, value): write(path, json.dumps(value, ensure_ascii=False, indent=2)+'\n')
def binding(path):
    return dict(task_relative=path.relative_to(TASK).as_posix(),
                bytes=path.stat().st_size, sha256=sha(path))
def source_binding(path):
    return dict(root_relative=path.relative_to(ROOT).as_posix(),
                bytes=path.stat().st_size, sha256=sha(path))
def bound_path(row):
    return ROOT/row['root_relative'] if 'root_relative' in row else TASK/row['task_relative']


def native_gate():
    assert sha(TASK/'formalization/CoefficientMapNumeratorPartialFractions.lean') == SOURCE_SHA
    assert sha(AUTHOR/'author-audit.json') == AUTHOR_SHA
    assert sha(INDEPENDENT/'independent-review.json') == INDEPENDENT_SHA
    author, ind = load(AUTHOR/'author-audit.json'), load(INDEPENDENT/'independent-review.json')
    assert author['verdict'] == ind['verdict'] == 'PASS'
    assert len(author['checks']) == 24 and all(row['pass'] for row in author['checks'])
    assert len(ind['checks']) == 32 and all(row['passed'] for row in ind['checks'])
    assert len(author['stable_files']) == 188 and len(ind['stable_files']) == 388
    verified = {}
    for role, report in [('native_author', author), ('native_independent', ind)]:
        records = []
        for row in report['stable_files']:
            path = bound_path(row)
            assert path.resolve().is_relative_to(ROOT.resolve())
            assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
            records.append(dict(row, actual_sha256=sha(path), actual_bytes=path.stat().st_size))
        verified[role] = records
    records = ind['successful_groups_actual_records']['source']
    defs = [r for r in records if r['kind'] == 'definition_full_expression']
    proofs = [r for r in records if r['kind'] == 'proof_full_type']
    assert len(records) == 40 and len(defs) == 16 and len(proofs) == 24
    assert len([r for r in defs if r['declaration'].startswith(NS+'.')]) == 4
    assert len([r for r in proofs if r['declaration'].startswith(NS+'.')]) == 23
    assert all(set(r['axioms']) <= STD for r in records)
    assert all(r['type_expression_repr'] and r['full_value_expression_repr'] for r in defs)
    assert all(r['full_type_expression_repr'] for r in proofs)
    byname = {r['declaration']:r for r in proofs}
    assert all(byname[NS+'.'+name]['full_type_expression_repr'] for name in TARGETS)
    return author, ind, verified, records


def imports_scheduling_only(source):
    """Fixed import lines are a scheduling hint, never an elaborated graph."""
    return [dep for line in source.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('import ') for dep in line.removeprefix('import ').split()
            if dep.startswith('missions.zeta9.formalization.')
            or dep == 'Definitions.Def_ZetaNine_HarmonicStability']


def source_closure_from_real_imports(ind):
    bound = {bound_path(r).resolve():r for r in ind['stable_files']}
    ordered, edges, active, done = [], {}, set(), set()
    def visit(module):
        if module in done: return
        assert module not in active, 'Cyclic source scheduling hint.'
        active.add(module)
        rel = module.replace('.', '/')+'.lean'
        source = ROOT/rel
        assert source.is_file() and source.resolve() in bound, str(source)
        assert sha(source) == bound[source.resolve()]['sha256']
        deps = imports_scheduling_only(source)
        edges[module] = deps
        for dep in deps: visit(dep)
        active.remove(module);done.add(module)
        write(PROJECT/rel, source.read_bytes())
        ordered.append(dict(source_binding(source), module=module,
            project_relative=rel, parser_name=module.rsplit('.',1)[1]))
    visit(NATIVE)
    return ordered, edges


def parent_definitions():
    previous = TASK/'formalization/platform/coefficient-map-partial-fractions/root-copy-plan.json'
    plan = load(previous)
    records = list(plan['required_existing_Definitions'])
    actual = next(r for r in plan['files'] if r['root_relative_destination'].startswith('Definitions/'))
    records.append(dict(root_relative=actual['root_relative_destination'],
        task_relative=actual['staged_task_relative'], sha256=actual['sha256']))
    harmonic = ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean'
    records.insert(0,dict(source_binding(harmonic),task_relative=None,
        fixed_Root_source_only=True))
    result=[]
    for row in records:
        installed = ROOT/row['root_relative']
        source = TASK/row['task_relative'] if row['task_relative'] else installed
        assert sha(source) == sha(installed) == row['sha256']
        write(PROJECT/row['root_relative'], source.read_bytes())
        result.append(dict(row,bytes=source.stat().st_size,
            module=row['root_relative'].removesuffix('.lean').replace('/','.')))
    assert len({r['module'] for r in result}) == len(result)
    return result, binding(previous)


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'preparation-verification.json').exists(), 'Do not overwrite frozen preparation.'
    assert not PROJECT.exists(), 'pa1 must be absent before initial pure preparation.'
    assert not (OUT/'author-audit.json').exists()
    author, ind, verified, records = native_gate()
    sources, edges = source_closure_from_real_imports(ind)
    parents, parent_plan_binding = parent_definitions()
    dump(OUT/'native-input-verification.json',dict(status='PURE_INPUT_BYTES_VERIFIED',
        Lean_executed=False,source_sha256=SOURCE_SHA,author_sha256=AUTHOR_SHA,
        independent_sha256=INDEPENDENT_SHA,verified_bindings=verified,
        author_checks=24,independent_checks=32,author_bound_files=188,independent_bound_files=388,
        historical_native_author_parent_object_reuse_is_explicit=True,
        historical_native_author_failure_excluded=True,
        historical_native_independent_failure_excluded=True,
        author_source_records=40,author_Data_PF_definitions=16,author_Data_PF_proofs=24))
    dump(OUT/'source-scheduling-hint.json',dict(role='Import-line scheduling only',
        genuine_Stage1_graph=False,sources=sources,edges=edges))

    controls=[]
    for module,source,counts in [
        ('NativeNumeratorPFSourceControl',INDEPENDENT/'source_audit.lean',dict(definitions=16,proofs=24)),
        ('NativeNumeratorPFExpectedControl',INDEPENDENT/'expected_types_prepared.lean',dict(expected_proofs=24,kernel_types=24)),
        ('NativeNumeratorPFBoundaryControl',INDEPENDENT/'own_boundaries_prepared.lean',dict(boundary_proofs=25)),
        ('NativeNumeratorPFAuthorBoundaryControl',AUTHOR/'b2.lean',dict(boundary_proofs=15,endpoint_kernel_types=3))]:
        fixed = next(r for r in ind['stable_files'] if bound_path(r).resolve() == source.resolve())
        assert sha(source) == fixed['sha256']
        write(OUT/'native-controls'/(module+'.lean'),source.read_bytes())
        write(PROJECT/(module+'.lean'),source.read_bytes())
        controls.append(dict(source_binding(source),module=module,
            project_relative=module+'.lean',historical_expected_counts=counts,
            staged_replay_membership_pending_actual_parser_and_graph=True))

    graph_template = TASK/'formalization/platform/coefficient-map-connection/extract_decl_graph.lean'
    graph = graph_template.read_text(encoding='utf-8-sig')
    old_import = 'import missions.zeta9.formalization.CoefficientMapConnection'
    assert graph.count(old_import) == 1
    graph = graph.replace(old_import,'import '+NATIVE+'\n'+'\n'.join('import '+r['module'] for r in controls))
    old_filter = 'let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m'
    assert graph.count(old_filter) == 1
    graph = graph.replace(old_filter,old_filter+' || m == `Definitions.Def_ZetaNine_HarmonicStability'+
        ''.join(' || m == `'+r['module'] for r in controls))
    old_output = 'D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-connection/decl_graph.jsonl'
    assert graph.count(old_output) == 1
    graph = graph.replace(old_output,(OUT/'decl_graph.jsonl').as_posix())
    write(OUT/'extract_decl_graph.lean',graph);write(PROJECT/'extract_decl_graph.lean',graph)
    parser_template = TASK/'formalization/platform/coefficient-map-jet/extract_sketch_info.lean'
    parser = parser_template.read_text(encoding='utf-8-sig')
    old_snapshot = 'missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean'
    assert parser.count(old_snapshot) == 1
    for row in sources:
        name = row['parser_name'];filename='extract_'+name+'_sketch.lean'
        code = parser.replace(old_snapshot,(OUT/(name+'-oracle-input.lean')).as_posix())
        write(OUT/filename,code);write(PROJECT/filename,code)
    header_template = TASK/'formalization/platform/coefficient-map-connection/extract_header.lean'
    write(OUT/'extract_header.lean',header_template.read_bytes())
    write(PROJECT/'extract_header.lean',header_template.read_bytes())
    helper = (TASK/'formalization/platform/coefficient-map-matrix/lean_call.template.py').read_bytes()
    helper = helper.replace(b'MATRIX_RUN_PATHS_RECEIPT',b'NUMERATOR_PF_RUN_PATHS_RECEIPT')
    write(OUT/'lean_call.template.py',helper);write(PROJECT/'lean_call.py',helper)
    lake = '''import Lake
open Lake DSL
package zeta9NumeratorPFPlatformAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'''+REV+'''"
lean_lib Native where
  roots := #[`'''+NATIVE+''']
  globs := #[ '''+', '.join('.one `'+r['module'] for r in sources if r['module'].startswith('missions.'))+''' ]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
lean_lib Controls where
  roots := #[ '''+', '.join('`'+r['module'] for r in controls)+''' ]
  globs := #[ '''+', '.join('.one `'+r['module'] for r in controls)+''' ]
lean_lib Comparison where
  roots := #[`NativeValueComparisonDefinition, `StagedValueComparisonDefinition]
  globs := #[.one `NativeValueComparisonDefinition, .one `StagedValueComparisonDefinition]
'''
    write(PROJECT/'lakefile.lean',lake)
    for name in ['lean-toolchain','lake-manifest.json']:write(PROJECT/name,(ROOT/name).read_bytes())
    assert (PROJECT/'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.33.1'
    assert next(r for r in load(PROJECT/'lake-manifest.json')['packages'] if r['name']=='mathlib')['rev'] == REV
    byname = {r['declaration']:r for r in records}
    selected=[dict(name=NS+'.'+name,arguments=args,
        short_module_suffix=suffix,
        local_solution='Solutions/Sol_ZetaNine_'+TAG+'_'+suffix+'.lean',
        local_reference='Theorems/Thm_ZetaNine_'+TAG+'_'+suffix+'.lean',
        frozen_native_full_type_expression_repr=byname[NS+'.'+name]['full_type_expression_repr'],
        frozen_native_type_pp_diagnostic=byname[NS+'.'+name]['type_pp_diagnostic'],
        frozen_native_axioms=byname[NS+'.'+name]['axioms'],
        new_actual_parser_span=None,new_actual_kernel_type_check=None)
        for name,args,suffix in zip(TARGETS,ARGS,SUFFIXES)]
    modules=[r['module'] for r in sources+parents+controls]+['Definitions.Def_ZetaNine_'+TAG,
        'NativeValueComparisonDefinition','StagedValueComparisonDefinition']+[
        r[key].removesuffix('.lean').replace('/','.') for r in selected for key in ['local_solution','local_reference']]
    paths=[]
    for module in dict.fromkeys(modules):
        obj=PROJECT/'b/lib/lean'/(module.replace('.','/')+'.olean')
        row=dict(module=module,path=str(obj),path_plus_64=len(str(obj))+64,passed=len(str(obj))+64<=259)
        assert row['passed'],row
        paths.append(row)
    native_modules={r['module'] for r in sources}
    parent_compiles=sum(r['module'] not in native_modules for r in parents)
    call_counts=dict(runtime=1,native_source_compiles=len(sources),native_control_compiles=len(controls),
        actual_stage1=1,actual_stage2_source_parsers=len(sources),actual_header=1,
        existing_platform_definition_compiles=parent_compiles)
    call_counts['total']=sum(call_counts.values())
    plan=dict(status='PREPARATION_ONLY',Lean_executed=False,Stage1_Stage2_results_claimed=False,
        author_PASS_claimed=False,source_sha256=SOURCE_SHA,author_sha256=AUTHOR_SHA,
        independent_sha256=INDEPENDENT_SHA,pinned_mathlib_rev=REV,
        source_project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        fresh_build_task_relative=(PROJECT/'b').relative_to(TASK).as_posix(),
        project_initially_absent=True,cache_initially_absent=True,package_link_created=False,
        native_proof_objects_borrowed=False,native_sources=sources,parent_definitions=parents,
        parent_copy_plan_binding=parent_plan_binding,native_controls=controls,
        original_PF_source_counts=dict(definitions=4,theorems=23,records=27),
        original_Data_PF_counts=dict(definitions=16,theorems=24,records=40),
        all_PF_source_definitions=DEFS,minimal_Data_definition_candidates=DATA_CANDIDATES,
        minimal_new_Definitions_membership=None,actual_proof_closure_size=None,
        actual_definition_valueRefs=None,selected_actual_endpoints=selected,
        exact_future_scoped_build_entrypoints=[r['local_solution'].removesuffix('.lean').replace('/','.') for r in selected],
        graph_template_binding=binding(graph_template),parser_template_binding=binding(parser_template),
        header_template_binding=binding(header_template),path_checks=paths,future_oracle_calls=call_counts,
        future_proof_strategy='Read actual Stage1 type/value reachability plus genuine instance roots. Use Stage2 declaration/ref/open/header spans; inline complete reached original helper proofs in dependency order. Preserve all 23 actual PF proofs where their generic helpers are required, rename only the chosen target and wrap it. Do not import this PF target Theorem/Solution or add PF existence/transport assumptions.',
        future_value_strategy='Actual graph decides precisely which Data declarations become importable alongside four PF pure definitions. Do not promote all 12 Data definitions by module association. Each included new pure definition needs full native/staged type/value kernel equality and closed whole-function rfl; statement/proof dependencies are explicit.',
        future_control_strategy='Native full controls are replayed in the fresh native environment. Staged expected/boundary/value controls must be selected from actual parser declarations using the actual minimal Definition/closure; Data/Connection-only statements may be explicitly excluded as out of this generic PF scope, never silently counted. New independent expected types retain all original degree and regular-point binders.',
        original_domain='All m>=0, actual A over Q with natDegree<9*(m+1); global t over Q with every t+k nonzero, k<=m. Injectivity has two strict degree bounds and equality of the actual jets for 1<=s<=9, j<=m. No n>=1 or Even restriction is added.',
        forbidden_added_hypotheses=['PF existence','abstract principal-part array','chosen coefficients','formal coefficient transport','zeta independence','HasSum','summability'],
        excluded_claims=['formal five-output transport','parameter-shift HasSum identity','integer heights','small forms','irrationality','arbitrary abstract-array uniqueness'],
        no_Root_API_credentials_scope_writes=True,Root_installation_claimed=False,
        external_acceptance_claimed=False,independent_platform_review_required=True)
    dump(OUT/'preparation-state.json',plan)
    print(json.dumps(dict(status=plan['status'],native_sources=len(sources),parent_Definitions=len(parents),
        native_controls=len(controls),future_initial_calls=call_counts['total'],
        PF_source_definitions=4,PF_source_proofs=23,minimal_new_definitions=None,
        verified_author_bindings=188,verified_independent_bindings=388,
        longest_path_plus64=max(r['path_plus_64'] for r in paths),Lean_executed=False)))


if __name__=='__main__':main()

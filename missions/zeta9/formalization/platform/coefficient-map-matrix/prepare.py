"""Pure Matrix platform preparation. No Lean/Lake invocation or Root writes.

Native frozen records supply declaration names and actual previously audited
types. New graph, parser, header, kernel and proof results remain pending.
"""
from pathlib import Path
import hashlib, json, sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/ma1'
NATIVE = 'missions.zeta9.formalization.CoefficientMapMatrix'
NS = 'ZetaNine.CoefficientMapMatrix'
REV = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE_SHA = 'a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99'
AUTHOR_SHA = '767b25d5db8a371308a875b023d58f050eb1969650e62917207157c6c8bbc010'
INDEPENDENT_SHA = 'c333e8459bd458d62b4a48917a188970c9579ecea6e9707998d9a0289ceb2e72'
AUTHOR = TASK / 'verification/formalization-coefficient-map-matrix-2026-10-04'
INDEPENDENT = TASK / 'verification/formalization-coefficient-map-matrix-independent-2026-10-04'
KERNEL = TASK / 'formalization/platform/coefficient-map-kernel-bridge'
DEFS = ['actualFMatrix', 'selectionMatrix', 'selectedIntegerPair',
        'selectedIntegerOutput', 'selectedIntegerMultiplier']
TARGETS = ['actualFMatrix_det_ne_zero',
           'selectedIntegerMultiplier_coordinates_product',
           'selectedIntegerMultiplier_actual_HasSum_and_absolute']
ARGS = ['n hn2 hn', 'n hn2 hn b a', 'n hn2 hn b a']
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


def native_gate():
    assert sha(TASK/'formalization/CoefficientMapMatrix.lean') == SOURCE_SHA
    assert sha(AUTHOR/'author-audit.json') == AUTHOR_SHA
    assert sha(INDEPENDENT/'independent-review.json') == INDEPENDENT_SHA
    author, ind = load(AUTHOR/'author-audit.json'), load(INDEPENDENT/'independent-review.json')
    assert author['verdict'] == ind['verdict'] == 'PASS'
    assert author['source_records'] == 22 and author['definitions'] == 5 and author['theorems'] == 17
    assert len(ind['checks']) == 32 and all(row['pass'] for row in ind['checks'])
    assert len(ind['stable_files']) == 517
    actual_bindings = []
    for row in ind['stable_files']:
        path = ROOT/row['root_relative'] if 'root_relative' in row else TASK/row['task_relative']
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
        actual_bindings.append(dict(row, actual_sha256=sha(path), actual_bytes=path.stat().st_size))
    records = ind['actual_source_records']
    assert len(records) == 22 and sum(r['kind'] == 'def' for r in records) == 5
    assert sum(r['kind'] == 'theorem' for r in records) == 17
    assert all(set(r['axioms']) <= STD and r['full_type_expression_repr'] for r in records)
    assert [r['declaration'] for r in records if r['kind'] == 'def'] == [NS+'.'+n for n in DEFS]
    return author, ind, actual_bindings


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'author-audit.json').exists(), 'Do not overwrite a frozen author.'
    assert not (PROJECT/'b').exists(), 'Preparation requires a fresh empty proof cache.'
    assert not (PROJECT/'.lake').exists(), 'No package junction or Lake configuration run in pure preparation.'
    author, ind, verified = native_gate()
    dump(OUT/'native-input-verification.json', dict(
        status='PURE_INPUT_BYTES_VERIFIED', Lean_executed=False,
        source_sha256=SOURCE_SHA, author_sha256=AUTHOR_SHA,
        independent_sha256=INDEPENDENT_SHA, checks=32, verified_bindings=verified,
        original_author_failed_compilations_retained=2,
        author_parent_cache_reuse_is_historical=True))

    kernel_plan = load(KERNEL/'root-copy-plan.json')
    expected = dict(kernel_plan['sources_sha256'])
    expected['CoefficientMapMatrix'] = SOURCE_SHA
    assert len(expected) == 12
    native_sources = []
    for name, expected_sha in expected.items():
        source = TASK/'formalization'/(name+'.lean')
        assert sha(source) == expected_sha
        rel = 'missions/zeta9/formalization/'+name+'.lean'
        write(PROJECT/rel, source.read_bytes())
        native_sources.append(dict(source_binding(source), module=rel.removesuffix('.lean').replace('/', '.'),
            project_relative=rel, parser_name=name))

    parents = list(kernel_plan['required_existing_Definitions'])
    kernel_def = kernel_plan['files'][0]
    parents.append(dict(root_relative=kernel_def['root_relative_destination'],
        task_relative=kernel_def['staged_task_relative'], sha256=kernel_def['sha256']))
    assert len(parents) == 12 and len({r['root_relative'] for r in parents}) == 12
    parent_bindings = []
    for row in parents:
        source, installed = TASK/row['task_relative'], ROOT/row['root_relative']
        assert sha(source) == sha(installed) == row['sha256']
        write(PROJECT/row['root_relative'], source.read_bytes())
        parent_bindings.append(dict(row, bytes=source.stat().st_size,
            module=row['root_relative'].removesuffix('.lean').replace('/', '.')))
    harmonic = next(r for r in parent_bindings if r['module'] == 'Definitions.Def_ZetaNine_HarmonicStability')
    harmonic_source = TASK/harmonic['task_relative']
    native_sources.insert(0, dict(source_binding(harmonic_source),
        module=harmonic['module'], project_relative=harmonic['root_relative'],
        parser_name='Def_ZetaNine_HarmonicStability'))
    assert len(native_sources) == 13

    controls = []
    for module, source, count in [
        ('NativeMatrixAuthorSourceControl', AUTHOR/'type-audit.lean', 22),
        ('NativeMatrixAuthorEndpointControl', AUTHOR/'endpoint-audit.lean', 12),
        ('NativeMatrixIndependentSourceControl', INDEPENDENT/'source-full-audit.lean', 22),
        ('NativeMatrixIndependentBoundaryControl', INDEPENDENT/'independent-boundary.lean', 26)]:
        exact = next(r for r in ind['stable_files'] if
            (ROOT/r['root_relative'] if 'root_relative' in r else TASK/r['task_relative']).resolve() == source.resolve())
        assert sha(source) == exact['sha256']
        write(OUT/'native-controls'/(module+'.lean'), source.read_bytes())
        write(PROJECT/(module+'.lean'), source.read_bytes())
        controls.append(dict(source_binding(source), module=module,
            project_relative=module+'.lean', expected_records=count))

    graph_template = TASK/'formalization/platform/coefficient-map-connection/extract_decl_graph.lean'
    graph = graph_template.read_text(encoding='utf-8-sig')
    old_import = 'import missions.zeta9.formalization.CoefficientMapConnection'
    assert graph.count(old_import) == 1
    graph = graph.replace(old_import, 'import '+NATIVE+'\n'+'\n'.join('import '+c['module'] for c in controls))
    old_select = 'let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m'
    assert graph.count(old_select) == 1
    graph = graph.replace(old_select, old_select+' || m == `Definitions.Def_ZetaNine_HarmonicStability'+
        ''.join(' || m == `'+c['module'] for c in controls))
    old_output = 'D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/coefficient-map-connection/decl_graph.jsonl'
    assert graph.count(old_output) == 1
    graph = graph.replace(old_output, (OUT/'decl_graph.jsonl').as_posix())
    write(OUT/'extract_decl_graph.lean', graph)
    write(PROJECT/'extract_decl_graph.lean', graph)

    parser_template = TASK/'formalization/platform/coefficient-map-jet/extract_sketch_info.lean'
    parser = parser_template.read_text(encoding='utf-8-sig')
    original_snapshot = 'missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean'
    assert parser.count(original_snapshot) == 1
    for row in native_sources:
        name = row['parser_name']
        code = parser.replace(original_snapshot, (OUT/(name+'-oracle-input.lean')).as_posix())
        filename = 'extract_'+name+'_sketch.lean'
        write(OUT/filename, code); write(PROJECT/filename, code)
    header_template = TASK/'formalization/platform/coefficient-map-connection/extract_header.lean'
    write(OUT/'extract_header.lean', header_template.read_bytes())
    write(PROJECT/'extract_header.lean', header_template.read_bytes())

    lake = '''import Lake
open Lake DSL
package zeta9MatrixPlatformAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'''+REV+'''"
lean_lib Native where
  roots := #[`'''+NATIVE+''']
  globs := #[ '''+', '.join('.one `'+r['module'] for r in native_sources if r['module'].startswith('missions.'))+''' ]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
lean_lib Controls where
  roots := #[ '''+', '.join('`'+c['module'] for c in controls)+''' ]
  globs := #[ '''+', '.join('.one `'+c['module'] for c in controls)+''' ]
lean_lib Comparison where
  roots := #[`NativeValueComparisonDefinition, `StagedValueComparisonDefinition]
  globs := #[.one `NativeValueComparisonDefinition, .one `StagedValueComparisonDefinition]
'''
    write(PROJECT/'lakefile.lean', lake)
    write(PROJECT/'lean_call.py', (OUT/'lean_call.template.py').read_bytes())
    for name in ['lean-toolchain', 'lake-manifest.json']:
        write(PROJECT/name, (ROOT/name).read_bytes())
    assert (PROJECT/'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.33.1'
    assert next(r for r in load(PROJECT/'lake-manifest.json')['packages'] if r['name'] == 'mathlib')['rev'] == REV

    records = {r['declaration']:r for r in ind['actual_source_records']}
    selected = [dict(name=NS+'.'+n, arguments=a,
        frozen_native_full_type_expression_repr=records[NS+'.'+n]['full_type_expression_repr'],
        frozen_native_type_pp_diagnostic=records[NS+'.'+n]['type_pp_diagnostic'],
        frozen_native_axioms=records[NS+'.'+n]['axioms'],
        new_actual_parser_span=None, new_actual_kernel_type_check=None)
        for n,a in zip(TARGETS,ARGS)]
    modules = [r['module'] for r in native_sources]+[r['module'] for r in parent_bindings]+[
        'Definitions.Def_ZetaNine_CoefficientMapMatrix']+[r['module'] for r in controls]+[
        'NativeValueComparisonDefinition', 'StagedValueComparisonDefinition']+[
        prefix+'ZetaNine_CoefficientMapMatrix_'+n for n in TARGETS
        for prefix in ['Solutions.Sol_', 'Theorems.Thm_']]
    path_checks = []
    for module in dict.fromkeys(modules):
        obj = PROJECT/'b/lib/lean'/(module.replace('.', '/')+'.olean')
        row = dict(module=module, path=str(obj), path_plus_64=len(str(obj))+64,
                   passed=len(str(obj))+64 <= 259)
        assert row['passed'], row
        path_checks.append(row)
    plan = dict(status='PREPARATION_ONLY', Lean_executed=False,
        Stage1_Stage2_results_claimed=False, author_PASS_claimed=False,
        source_sha256=SOURCE_SHA, author_sha256=AUTHOR_SHA, independent_sha256=INDEPENDENT_SHA,
        pinned_mathlib_rev=REV, source_project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        fresh_build_task_relative=(PROJECT/'b').relative_to(TASK).as_posix(),
        cache_initially_absent=True, native_proof_objects_borrowed=False,
        original_source_counts=dict(definitions=5, theorems=17, records=22),
        new_actual_definitions=DEFS, selected_actual_endpoints=selected,
        native_sources=native_sources, parent_definitions=parent_bindings, native_controls=controls,
        expected_original_project_definitions=70,
        expected_original_project_definition_count_is_pending_new_actual_graph=True,
        actual_proof_closure_size=None, actual_definition_valueRefs=None,
        exact_future_scoped_build_entrypoints=[
            'Solutions.Sol_ZetaNine_CoefficientMapMatrix_'+n for n in TARGETS],
        graph_template_binding=binding(graph_template), parser_template_binding=binding(parser_template),
        header_template_binding=binding(header_template), path_checks=path_checks,
        future_oracle_calls=dict(native_source_compiles=13, native_control_compiles=4,
            existing_platform_definition_compiles=11, actual_stage1=1, actual_stage2_source_parsers=13,
            actual_header=1, runtime=1, total=44),
        future_proof_strategy='Actual cross-module Stage1 type/value closure plus all source instances; parser-owned declaration/reference/open spans in dependency order. Inline complete original helper proofs, preserve all 17 Matrix proofs, rename only each chosen actual target and wrap it. No import of a Matrix target Theorem or Solution. Parent Definitions remain their hash-fixed actual values.',
        future_value_strategy='Five pure Matrix definitions are copied only from new actual parser spans. Native and staged shared-alias programs differ only by import and each gets five full type/value isDefEq checks and five closed whole-function rfl proofs. Existing proof-bearing parent Definition equivalences require their frozen complete kernel/closed data evidence and explicit actual valueRefs.',
        original_domain='Every inverse/determinant/sum endpoint retains n>=2 and Even n; b,a are integers but the multiplier coefficients and inverse matrix are rational.',
        forbidden_added_hypotheses=['F invertible', 'determinant nonzero', 'kernel zero',
            'aggregate bijective', 'HasSum', 'summability', 'zeta independence'],
        excluded_claims=['integer inverse polynomial', 'integral coefficients', 'height bounds',
            'small nonzero integer forms', 'irrationality', 'formal five-output transport'],
        no_Root_API_credentials_scope_writes=True, Root_installation_claimed=False,
        external_acceptance_claimed=False, independent_platform_review_required=True)
    dump(OUT/'preparation-state.json', plan)
    print(json.dumps(dict(status=plan['status'], native_sources=13, parent_Definitions=12,
        native_controls=4, defs=5, original_proofs=17, selected_targets=3,
        verified_native_independent_bindings=517, longest_path_plus64=max(r['path_plus_64'] for r in path_checks),
        Lean_executed=False), ensure_ascii=False))


if __name__ == '__main__': main()

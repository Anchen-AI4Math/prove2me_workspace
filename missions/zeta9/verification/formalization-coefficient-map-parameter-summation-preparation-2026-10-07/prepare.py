"""Pure SOURCE preparation; no process, Lean, Lake, API, or credentials."""
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/ost1'
PREVIOUS = TASK / 'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
AUTHOR = TASK / 'verification/formalization-coefficient-map-formal-transport-outputs-author-2026-10-07'
SOURCE = TASK / 'formalization/CoefficientMapParameterSummationTransport.lean'
NATIVE = 'missions.zeta9.formalization.CoefficientMapParameterSummationTransport'
NS = 'ZetaNine.CoefficientMapParameterSummationTransport'
OUTPUTS_SHA = '8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6'
AUTHOR_SHA = '4e1d50c94ec296144696b8dc7c71dea74f682e9c0a69ed8e46aa4fe5e862f315'
JETS_SHA = 'ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
ARGS = {
    'transferMultiplier_natDegree_le': 'n W',
    'even_add_two': 'n hn',
    'exactL_eq_prescribed_actual_output': 'n W',
    'transfer_actual_five_outputs': 'n hn W hW',
    'transfer_actual_exactL': 'n hn W hW',
    'quartic_actual_HasSum_and_absolute': 'n hn2 hn W hW',
    'actual_chosen_exactL_transport': 'n hn r',
    'actual_chosen_HasSum_transport': 'n hn2 hn r',
    'actual_chosen_tsum_transport': 'n hn2 hn r',
    'quartic_HasSum_transport': 'n hn2 hn W hW',
    'quartic_tsum_transport': 'n hn2 hn W hW',
    'transferred_inverseMultiplier_eq': 'n hn2 hn b',
    'inverseMultiplier_coordinates_transport': 'n hn2 hn b',
    'chosen_transferMultiplier_eq_connectionP': 'n hn2 hn r',
    'selectedIntegerMultiplier_transport': 'n hn2 hn b a',
    'selectedIntegerMultiplier_parameter_HasSum': 'n hn2 hn b a',
    'selectedIntegerMultiplier_parameter_tsum': 'n hn2 hn b a',
}
OPENS = '''open ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw if isinstance(raw, bytes) else raw.encode('utf-8'))


def dump(path, obj):
    write(path, json.dumps(obj, ensure_ascii=False, indent=2) + '\n')


def binding(path):
    return dict(task_relative=path.relative_to(TASK).as_posix(), bytes=path.stat().st_size,
                sha256=sha(path))


def headers(raw):
    result = []
    lines = raw.decode('utf-8-sig').splitlines(keepends=True)
    for i, line in enumerate(lines):
        if line.startswith('theorem '):
            header = ''.join(lines[i:]).split(':=', 1)[0].rstrip()
            result.append(dict(name=line.split()[1], header=header))
    return result


def save_control(name, raw):
    immutable = OUT / 'controls' / (name + '.lean')
    target = PROJECT / (name + '.lean')
    write(immutable, raw)
    write(target, raw)
    return dict(module=name, project_relative=name + '.lean',
                immutable_source=binding(immutable), initial_project_copy=binding(target))


def main():
    assert not PROJECT.exists(), 'fresh pure SOURCE project must not already exist'
    assert not (OUT / 'preparation-verification.json').exists()
    export = AUTHOR / 'OutputsVerifiedSource.lean'
    report = AUTHOR / 'author-audit.json'
    assert sha(export) == OUTPUTS_SHA and sha(report) == AUTHOR_SHA
    assert load(report)['verdict'] == 'PASS'
    copied = []
    old = load(PREVIOUS / 'source-inputs.json')
    for record in old['sources']:
        module = record['module']
        if module.endswith('.CoefficientMapFormalTransportOutputs'):
            origin, expected = export, OUTPUTS_SHA
        else:
            origin, expected = Path(record['origin_absolute']), record['sha256']
        assert sha(origin) == expected, module
        raw = origin.read_bytes()
        target = PROJECT / record['project_relative']
        snapshot = PROJECT / 's' / ('i' + str(len(copied)).zfill(3))
        write(target, raw)
        write(snapshot, raw)
        copied.append(dict(module=module, project_relative=record['project_relative'],
                           origin_absolute=str(origin), bytes=len(raw), sha256=expected,
                           initial_project_copy=binding(target), immutable_snapshot=binding(snapshot)))
    assert len(copied) == 21
    assert next(r for r in copied if r['module'].endswith('.CoefficientMapFormalTransportJets'))['sha256'] == JETS_SHA
    raw = SOURCE.read_bytes()
    target = PROJECT / (NATIVE.replace('.', '/') + '.lean')
    snapshot = PROJECT / 's/i021'
    write(target, raw)
    write(snapshot, raw)
    copied.append(dict(module=NATIVE, project_relative=target.relative_to(PROJECT).as_posix(),
                       origin_absolute=str(SOURCE), bytes=len(raw), sha256=sha(SOURCE),
                       initial_project_copy=binding(target), immutable_snapshot=binding(snapshot)))
    inventory = headers(raw)
    assert len(inventory) == 17 and {r['name'] for r in inventory} == set(ARGS)
    assert not any(token in raw.decode('utf-8') for token in ['sorry', 'admit', 'axiom '])
    controls = []
    for name in ['IndependentExprDagV3', 'IndependentExprDagValidationV3']:
        source = PREVIOUS / 'controls' / (name + '.lean')
        controls.append(save_control(name, source.read_bytes()))
    prefix = ('import ' + NATIVE + '\nimport IndependentExprDagV3\nimport Lean\n'
              'noncomputable section\nopen scoped BigOperators Matrix\n'
              'open Polynomial\n' + OPENS)
    code = prefix + '\nnamespace ParameterSummationAuthorExpected\n'
    for item in inventory:
        name = item['name']
        code += item['header'].replace('theorem ' + name, 'theorem expected_' + name, 1)
        code += ' := by\n  exact ' + NS + '.' + name + ' ' + ARGS[name] + '\n\n'
    code += 'end ParameterSummationAuthorExpected\nopen Lean Meta\n'
    code += 'set_option maxHeartbeats 0\nset_option maxRecDepth 20000\nrun_meta do\n'
    pairs = ', '.join('(`' + NS + '.' + r['name'] + ', `ParameterSummationAuthorExpected.expected_' + r['name'] + ')' for r in inventory)
    code += '  for (actual,expected) in [' + pairs + '] do\n' + '''    let .thmInfo a ← getConstInfo actual | throwError "Not a source theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Not an expected theorem: {expected}"
    let equal ← isDefEq a.type b.type
    unless equal do throwError "Complete expected type mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard axiom: {actual}"
    let ad ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let bd ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_and_proof_expression_dag",ad),
      ("full_expected_type_and_proof_expression_dag",bd),
      ("type_kernel_equal",toJson equal),("all_fields_Expr_equal_roundtrip",toJson true),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
'''
    controls.append(save_control('ParameterSummationFullTypeAudit', code))
    code = prefix + '''
namespace ParameterSummationAuthorDefinitionExpected
def transferMultiplier (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  coordinatePolynomial (polynomialCoordinates W ᵥ* connectionGamma n)
end ParameterSummationAuthorDefinitionExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  let actual := `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier
  let expected := `ParameterSummationAuthorDefinitionExpected.transferMultiplier
  let .defnInfo a ← getConstInfo actual | throwError "Not a source definition"
  let .defnInfo b ← getConstInfo expected | throwError "Not an expected definition"
  let te ← isDefEq a.type b.type
  let ve ← isDefEq a.value b.value
  unless te && ve do throwError "Complete definition type/value mismatch"
  let aa ← collectAxioms actual
  let ba ← collectAxioms expected
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
    throwError "Nonstandard definition axioms"
  let ad ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
  let bd ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
  IO.println (Json.mkObj [("kind",Json.str "actual_complete_definition_kernel_value"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson te),("value_kernel_equal",toJson ve),
    ("full_source_type_and_value_expression_dag",ad),
    ("full_expected_type_and_value_expression_dag",bd),
    ("source_axioms",toJson (aa.toList.map Name.toString)),
    ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
'''
    controls.append(save_control('ParameterSummationDefinitionAudit', code))
    boundary_names = []
    code = prefix + '\nnamespace ParameterSummationAuthorBoundary\n'
    endpoints = [
        ('n1_exact_r0', 'actual_chosen_exactL_transport 1 (by decide) (0 : Fin 5)'),
        ('n2_HasSum_r0', 'actual_chosen_HasSum_transport 2 (by decide) (by decide) (0 : Fin 5)'),
        ('n2_HasSum_r4', 'actual_chosen_HasSum_transport 2 (by decide) (by decide) (4 : Fin 5)'),
        ('n2_tsum_r4', 'actual_chosen_tsum_transport 2 (by decide) (by decide) (4 : Fin 5)'),
        ('n2_transfer_r0', 'chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (0 : Fin 5)'),
        ('n2_transfer_r4', 'chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (4 : Fin 5)'),
        ('n2_selected_B', 'selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) 1 0'),
        ('n2_selected_A', 'selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) 0 1'),
        ('n2_selected_tsum', 'selectedIntegerMultiplier_parameter_tsum 2 (by decide) (by decide) 1 1'),
    ]
    for name, proof in endpoints:
        # An inferred theorem type is a SOURCE boundary control, not a parsed-type claim.
        code += 'theorem ' + name + ' : _ := ' + proof + '\n'
        boundary_names.append('ParameterSummationAuthorBoundary.' + name)
    code += 'end ParameterSummationAuthorBoundary\nopen Lean Meta\n'
    code += 'set_option maxHeartbeats 0\nset_option maxRecDepth 20000\nrun_meta do\n'
    code += '  for name in [' + ','.join('`' + n for n in boundary_names) + '] do\n' + '''    let .thmInfo info ← getConstInfo name | throwError "Boundary is not a theorem"
    let axioms ← collectAxioms name
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless axioms.toList.all allowed.contains do throwError "Nonstandard boundary axioms"
    let dag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip info.type info.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_closed_boundary"),
      ("declaration",Json.str name.toString),("full_type_and_proof_expression_dag",dag),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
'''
    controls.append(save_control('ParameterSummationBoundaryAudit', code))
    write(PROJECT / 'lean-toolchain', (TASK / '.rt/oa1/lean-toolchain').read_bytes())
    write(PROJECT / 'lakefile.toml', '''name = "parameterSummationAuthor"
version = "0.1.0"
buildDir = "b"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "0df444a360eaa60ab8c11dca51a86af692955474"
[[lean_lib]]
name = "ParameterSummationNative"
roots = ["missions.zeta9.formalization.CoefficientMapParameterSummationTransport"]
''')
    write(PROJECT / 'lake-manifest.json', (TASK / '.rt/oa1/lake-manifest.json').read_bytes())
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        write(OUT / 'project-config' / name, (PROJECT / name).read_bytes())
    dump(OUT / 'static-original-header-inventory.json', dict(
        role='UNCOMPILED exact SOURCE text; no Lean parser/kernel evidence', records=inventory))
    dump(OUT / 'source-inputs.json', dict(sources=copied, controls=controls,
        author_source_provenance=binding(export), author_report_provenance=binding(report),
        prior_source_list_provenance=binding(PREVIOUS / 'source-inputs.json')))
    max_path = max(len(str(PROJECT / 'b/lib/lean' / (r['module'].replace('.', '/') + '.olean'))) + 64
                   for r in copied)
    checks = {
        'native_sources_22': len(copied) == 22,
        'complete_source_headers_17': len(inventory) == 17,
        'controls_5': len(controls) == 5,
        'max_olean_path_plus64_lt260': max_path < 260,
        'no_package_link': not (PROJECT / '.lake').exists(),
        'no_own_build_cache': not (PROJECT / 'b').exists(),
        'no_proof_objects': not any(PROJECT.rglob('*.olean*')),
        'outputs_author_export_pinned': sha(export) == OUTPUTS_SHA,
        'genuine_Jets_export_pinned': next(r for r in copied if r['module'].endswith('.CoefficientMapFormalTransportJets'))['sha256'] == JETS_SHA,
    }
    assert all(checks.values())
    dump(OUT / 'preparation-verification.json', dict(verdict='PURE_SOURCE_PREPARATION_PASS_NOT_LEAN_PASS',
        checks=checks, actual_runtime_calls=0, actual_Lean_calls=0,
        static_counts=dict(native_sources=22, complete_expected_types=17,
                           whole_definitions=1, closed_boundaries=9, controls=5,
                           planned_serial_calls=29, planned_own_object_resolutions=27),
        max_object_path_plus64=max_path, independent_review_still_required=True,
        Root_lane_grant_still_required=True))
    dump(OUT / 'endpoint-contracts.json', dict(status='UNCOMPILED',
        formal_coordinates_domain='all n>=1, all rational quartics W',
        HasSum_and_tsum_domain='even n>=2, all rational quartics W',
        genuine_inverse_domain='even n>=2, all output vectors b:Fin5→Q',
        no_transport_or_HasSum_or_zeta_independence_conclusion_premises=True,
        theorem_headers=inventory, closed_boundary_source_cases=endpoints,
        old_freezes_unchanged=True, platform_action_performed=False))
    stable = [SOURCE, Path(__file__).resolve(), OUT / 'static-original-header-inventory.json',
              OUT / 'source-inputs.json', OUT / 'preparation-verification.json',
              OUT / 'endpoint-contracts.json']
    stable += list((OUT / 'controls').glob('*.lean'))
    stable += list((OUT / 'project-config').iterdir())
    for r in copied:
        stable += [TASK / r['initial_project_copy']['task_relative'], TASK / r['immutable_snapshot']['task_relative']]
    stable += [PROJECT / r['project_relative'] for r in controls]
    stable += [PROJECT / name for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
    entries = [binding(p) for p in stable]
    dump(OUT / 'preparation-bindings.json', dict(role='pure SOURCE bindings, no kernel evidence', files=entries))
    write(OUT / 'PREPARATION_SHA256SUMS.txt', ''.join(r['sha256'] + '  ' + r['task_relative'] + '\n' for r in entries))
    print(json.dumps(dict(verdict='PURE_SOURCE_PREPARATION_PASS_NOT_LEAN_PASS',
                          candidate_sha256=sha(SOURCE), counts=load(OUT / 'preparation-verification.json')['static_counts'],
                          stable_files=len(entries), max_object_path_plus64=max_path)))


if __name__ == '__main__':
    main()

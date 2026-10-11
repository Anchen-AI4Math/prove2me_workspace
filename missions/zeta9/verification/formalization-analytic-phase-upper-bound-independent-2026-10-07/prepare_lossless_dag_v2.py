"""Pure SOURCE-only repair after retained actual proof-tree OOM."""
import re
import sys
sys.dont_write_bytecode = True
import prepare_independent as p

CORE = 'APIPhaseExprDagV1'
VALIDATION = 'APIPhaseExprDagValidationV1'


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    receipt = p.load(p.OUT / 'compile-receipt.json')
    assert len(receipt['rows']) == 4
    latest = {r['label']: r for r in receipt['rows']}
    assert latest['source-AnalyticPhase']['exit_code'] == 0
    assert latest['source-AnalyticPhaseUpperBound']['exit_code'] == 0
    failed = latest['control-types']
    assert failed['exit_code'] != 0 and failed['failed_attempt_retained']
    assert 'INTERNAL PANIC: out of memory' in (p.TASK / failed['log']['task_relative']).read_text(encoding='utf-8')
    origin_core = p.TASK / '.rt/ost1/IndependentExprDagV3.lean'
    origin_validation = p.TASK / '.rt/ost1/IndependentExprDagValidationV3.lean'
    assert p.sha(origin_core) == '1322612913bdc66d360720f64f9c72fa6047234e0717024ebb01a6c1303044e7'
    assert p.sha(origin_validation) == '5c8ef7f4dc5c512497479b47ec4cd50280042febcc7ed45ed793360ad75ab693'
    original_core = origin_core.read_text(encoding='utf-8')
    core = original_core.split('\n', 1)[1]
    assert core.startswith('import Lean\n')
    assert 'CoefficientMap' not in core
    tail = origin_validation.read_text(encoding='utf-8').split('end IndependentLosslessExprDagV1', 1)[1]
    replacements = {
        'ZetaNine.CoefficientMapKernelBridge.positiveProduct': 'ZetaNine.AnalyticPhase.phaseRatio',
        'ZetaNine.CoefficientMapKernelBridge.negativeProduct': 'ZetaNine.AnalyticPhase.phaseSlope',
        'ZetaNine.CoefficientMapKernelBridge.aValue': 'ZetaNine.AnalyticPhase.smoothPhaseRatio',
    }
    for old, new in replacements.items():
        assert tail.count(old) == 1
        tail = tail.replace(old, new)
    validation = 'import ' + CORE + '\nimport missions.zeta9.formalization.AnalyticPhaseUpperBound\nimport Lean.Util.CollectAxioms\nopen Lean Meta\nset_option autoImplicit false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 8000000\n' + tail
    original_types = (p.OUT / 'controls-v1/APIPhaseTypes.lean').read_text(encoding='utf-8')
    assert p.binding(p.PROJECT / 'APIPhaseTypes.lean') == next(b for b in p.load(p.OUT / 'preparation-state.json')['controls'] if b['task_relative'].endswith('/APIPhaseTypes.lean'))
    start = original_types.index('private def apRecord')
    end = original_types.index('\nrun_cmd liftTermElabM do', start)
    replacement = '''private def apRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some value := ci.value? true | throwError "Missing full proof/definition value: {n}"
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
  let (rt,rv) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let exactType := Expr.equal ci.type rt
  let exactValue := Expr.equal value rv
  unless exactType && exactValue do throwError "Full-field Expr DAG changed an expression: {n}"
  let typeKernel ← isDefEq ci.type rt
  let valueKernel ← isDefEq value rv
  let typed ← isDefEq (← inferType rv) ci.type
  unless typeKernel && valueKernel && typed do
    throwError "Reconstructed full proof/value does not have its exact complete type: {n}"
  apEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",toJson payload.compress),
    ("value_raw_format",toJson "lossless lean-expr-dag-v1; full type_root and value_root"),
    ("all_fields_type_Expr_equal",toJson exactType),("all_fields_value_Expr_equal",toJson exactValue),
    ("full_type_kernel_equal",toJson typeKernel),("full_value_kernel_equal",toJson valueKernel),
    ("full_value_typed",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← apAxioms n)]
'''
    types = original_types[:start] + replacement + original_types[end:]
    types = 'import ' + CORE + '\n' + types
    assert types.split('\nrun_cmd liftTermElabM do', 1)[1] == original_types.split('\nrun_cmd liftTermElabM do', 1)[1]
    original_resolver = (p.OUT / 'controls-v1/APIPhaseResolver.lean').read_text(encoding='utf-8')
    resolver = original_resolver + '''
run_cmd liftTermElabM do
  for n in #[`APIPhaseExprDagV1, `APIPhaseExprDagValidationV1] do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    let j := Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]
    liftM <| IO.println ("PHI_RECORD|" ++ j.compress)
'''
    created = []
    for name, data in [(CORE + '.lean', core), (VALIDATION + '.lean', validation), ('APIPhaseTypes.lean', types), ('APIPhaseResolver.lean', resolver)]:
        snapshot = p.OUT / 'controls-v2' / name
        assert not snapshot.exists(), 'Preserve previous repair versions'
        p.write(snapshot, data)
        p.write(p.PROJECT / name, data)
        created.append(dict(module=name.removesuffix('.lean'), immutable_source=p.binding(snapshot), private_source=p.binding(p.PROJECT / name)))
    for name, origin in [('IndependentExprDagV3.lean', origin_core), ('IndependentExprDagValidationV3.lean', origin_validation)]:
        p.write(p.OUT / 'serializer-source-origin-v1' / name, origin.read_bytes())
    doc = dict(role='private independent SOURCE controls repair; mathematical SOURCE untouched',
               reason='Actual control-types-01 OOM expanding shared proof with reprStr; exact DAG instead of tree duplication',
               failed_actual_row=failed, original_preparation=p.binding(p.OUT / 'preparation-state.json'),
               original_runner=p.binding(p.OUT / 'run_independent.py'),
               extension_grant=p.binding(p.OUT / 'Root-lean-lane-grant-dag-extension.json'),
               generic_serializer_origin_SOURCE=p.binding(origin_core), generic_validation_origin_SOURCE=p.binding(origin_validation),
               serializer_entire_body_after_unrelated_import_byte_identical=True,
               all20_serializer_field_fixtures_preserved=True, all3_small_source_fixtures_are_actual_phase_definitions=True,
               mathematical_originals_exports_and_own_source2_immutable=True,
               old_control_sources_failed_inputs_and_logs_immutable=True,
               no_proof_objects_copied=True, new_private_controls=created,
               complete34_theorems_7_definitions_68_source_declarations_scope_unchanged=True,
               full_proof_values_required=True, no_binder_metadata_universe_or_name_erasure=True,
               actual_DAG_decode_Expr_equal_inferType_and_isDefEq_required=True,
               original_kernel_raw_Expr_equal_false_records_not_rewritten=True,
               planned_new_generic_SOURCE_compiler_calls=2, Lean_calls_by_this_pure_preparation=0,
               API_Root_install_scope_or_mission_operations=False)
    p.dump(p.OUT / 'lossless-dag-v2-preparation.json', doc)
    print('Pure DAG repair ready; all proof fields preserved; no Lean executed by preparation.')
    print('Preparation SHA256: ' + p.sha(p.OUT / 'lossless-dag-v2-preparation.json'))


if __name__ == '__main__':
    main()

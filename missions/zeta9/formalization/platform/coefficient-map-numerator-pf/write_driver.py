"""Copy proven recorder mechanisms as source only; execute no Lean or Lake."""
from pathlib import Path
import prepare as p


def main():
    assert not (p.OUT/'preparation-verification.json').exists()
    previous=p.TASK/'formalization/platform/coefficient-map-matrix'
    driver=(previous/'run_actual.py').read_text(encoding='utf-8-sig')
    replacements=[
        ('Future serial Matrix author oracles.', 'Future serial GenericNumeratorPF author oracles.'),
        ("role='Matrix platform author, independent review required'", "role='GenericNumeratorPF platform author, independent review required'"),
        ('MATRIX_RUN_', 'NUMERATOR_PF_RUN_'),
        ("assert p.sha(TASK/row['task_relative']) == p.sha(ROOT/row['root_relative']) == row['sha256']",
         "source = TASK/row['task_relative'] if row['task_relative'] else ROOT/row['root_relative']\n        assert p.sha(source) == p.sha(ROOT/row['root_relative']) == row['sha256']"),
        ('missions/zeta9/formalization/CoefficientMapMatrix.lean',p.NATIVE.replace('.','/')+'.lean'),
        ("assert len(latest) == 44 and all(r['exit_code'] == 0 for r in latest.values())",
         "assert len(latest) == state['future_oracle_calls']['total'] and all(r['exit_code'] == 0 for r in latest.values())"),
        ("print('44 actual oracle/source/control calls completed; later staging and author freeze still pending.')",
         "print(str(len(latest))+' actual oracle/source/control calls completed; later staging and author freeze still pending.')")]
    for before,after in replacements:
        assert before in driver,before
        driver=driver.replace(before,after)
    p.write(p.OUT/'execute_oracles.py',driver)
    p.write(p.OUT/'retain_actual_inputs.py',(previous/'retain_actual_inputs.py').read_bytes())
    p.dump(p.OUT/'driver-source-provenance.json',dict(Lean_executed=False,
        actual_driver_adapted_source=p.binding(previous/'run_actual.py'),
        short_snapshot_helper_source=p.binding(previous/'retain_actual_inputs.py'),
        source_only_copy=True,no_compiler_objects_copied=True,
        exact_literal_adaptations=[dict(before=a,after=b) for a,b in replacements],
        outputs=[p.binding(p.OUT/name) for name in ['execute_oracles.py','retain_actual_inputs.py']]))


if __name__=='__main__':main()

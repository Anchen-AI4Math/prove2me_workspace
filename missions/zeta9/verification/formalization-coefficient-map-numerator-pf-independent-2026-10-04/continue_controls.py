"""Serial new-attempt controls; retains the earlier failed whole run."""
from pathlib import Path
import importlib.util
import argparse

OUT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pf_independent_run_v2', OUT / 'run-v2.py')
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent-lane-authorized', action='store_true', required=True)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    driver.verify()
    driver.configure(driver.lane_grant())
    receipt = driver.load(OUT / 'actual-execution-receipt.json')
    assert receipt['source_phase_complete']
    for name in ['IndependentValuesV2', 'ValueAliases']:
        source = driver.PROJECT / (name + '.lean')
        output = driver.CACHE / (name + '.olean')
        driver.run('fresh source-only definition alias ' + name,
                   ['-o', str(output), str(source)], source, output, args.resume)
    programs = [('source','source_audit.lean'),('expected','expected_types_prepared.lean'),
                ('values','whole_values_v2.lean'),('own','own_boundaries_prepared.lean'),
                ('author_types','author_types_replay.lean'),
                ('author_values','author_values_replay.lean'),
                ('author_boundaries','author_boundaries_replay.lean'),
                ('resolver','actual_resolver_v2.lean')]
    selected = {}
    for key,name in programs:
        source = OUT / name
        row = driver.run('actual independent control ' + name, [str(source)], source, resume=args.resume)
        selected[key] = row['label']
    driver.dump(OUT / 'terminal-control-selection.json', {'successful_control_labels':selected})
    receipt = driver.load(OUT / 'actual-execution-receipt.json')
    receipt['controls_phase_complete'] = True
    receipt['status'] = 'ALL_REQUIRED_SUCCESSFUL_EXECUTIONS_FINISHED_WITH_RETAINED_FAILURES'
    driver.dump(OUT / 'actual-execution-receipt.json', receipt)

if __name__ == '__main__':
    main()

"""Refresh the proof manifest from saved current verdicts and theorem snapshots."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERIFY = HERE / 'verification'


def main():
    target = VERIFY / 'proof-manifest.json'
    manifest = json.loads(target.read_text(encoding='utf-8'))
    proofs = {record['theorem_name']: record for record in manifest['accepted_proofs']}
    support = json.loads((VERIFY / 'bridge-nodes.json').read_text(encoding='utf-8'))
    for suffix, record in support.items():
        if record.get('proof_status') != 'ACCEPTED':
            continue
        name = 'ThreeSumSharpTail.' + suffix
        proofs[name] = {
            'theorem_name': name, 'theorem_id': record['theorem_id'],
            'submission_id': record['proof_submission_id'], 'verdict': 'ACCEPTED',
            'solution': f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean'}
    manifest['accepted_proofs'] = list(proofs.values())
    main_theorem = json.loads((VERIFY / 'ThreeSumSharpTail_threeSum_1999017-current.json').read_text(encoding='utf-8'))
    manifest['main_status'] = main_theorem['status']
    algorithm_theorem = json.loads((VERIFY / 'ThreeSumSharpTail_admissible_parameters_solve_3sum-current.json').read_text(encoding='utf-8'))
    manifest['algorithm_status'] = algorithm_theorem['status']
    manifest['remaining_child'] = None if algorithm_theorem['status'] == 'Proved' else algorithm_theorem['theorem_name']
    algorithm_file = VERIFY / 'algorithm-bridge-submission.json'
    if algorithm_file.exists():
        algorithm = json.loads(algorithm_file.read_text(encoding='utf-8'))
        manifest['algorithm_reduction'] = {
            'submission_id': algorithm.get('submission_id'), 'status': algorithm['status']}
        if algorithm['status'] in ('SKETCH_ACCEPTED', 'ACCEPTED'):
            manifest['remaining_frontier'] = 'ThreeSumSharpTail.cost_regime_solve_3sum'
    if main_theorem['status'] == 'Proved' and algorithm_theorem['status'] == 'Proved':
        manifest['remaining_frontier'] = None
    build_file = VERIFY / 'scoped-build.json'
    if build_file.exists():
        build = json.loads(build_file.read_text(encoding='utf-8'))
        manifest['local_build'] = {'record': 'scoped-build.json',
            'exit_code': build['exit_code'],
            'sources_unchanged_during_build': build['sources_unchanged_during_build']}
    manifest['graph_audit'] = 'graph-check.json'
    target.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'Accepted proof records: {len(proofs)}; main status: {manifest["main_status"]}')


if __name__ == '__main__':
    main()

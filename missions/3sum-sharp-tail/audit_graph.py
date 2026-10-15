"""Audit the actual final remote snapshots, not a hypothetical import graph."""
import json
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERIFY = HERE / 'verification'


def read(name):
    return json.loads((VERIFY / name).read_text(encoding='utf-8-sig'))


def main():
    main_graph = read('ThreeSumSharpTail_threeSum_1999017-graph.json')
    tail_graph = read('ThreeSumSharpTail_sharp_normalized_tail-graph.json')
    required = [
        (main_graph, '40c65758-b61e-402e-8afd-d2bc6e1784f1',
         '8c295241-d05d-4f1a-8854-2c0491f7b594', '1674355a-fcd8-4885-8ec3-cc3e1ff29624'),
        (main_graph, 'c9f11bd4-4101-4aaa-8c30-d0efc095df48',
         '8c295241-d05d-4f1a-8854-2c0491f7b594', '1674355a-fcd8-4885-8ec3-cc3e1ff29624'),
        (tail_graph, '855a023f-a057-46c2-bfda-b79ac07eed11',
         'd469e187-401e-4cfa-9dfb-0b0969e4d5db', '9424a09d-c1f8-409f-a290-5ec47c17f016'),
    ]
    nodes = read('certificate-nodes.json')
    encoding_id = nodes['encoding_log_certificate']['theorem_id']
    entropy_id = nodes['entropy_log_certificate']['theorem_id']
    certificate_submission = read('certificate-retry-submission.json')['submission_id']
    required.extend([
        (main_graph, encoding_id, certificate_submission, 'c9f11bd4-4101-4aaa-8c30-d0efc095df48'),
        (main_graph, entropy_id, certificate_submission, 'c9f11bd4-4101-4aaa-8c30-d0efc095df48'),
        (main_graph, encoding_id, nodes['entropy_log_certificate']['proof_submission_id'], entropy_id),
    ])
    support_file = VERIFY / 'bridge-nodes.json'
    support = read('bridge-nodes.json') if support_file.exists() else {}
    algorithm_file = VERIFY / 'algorithm-bridge-submission.json'
    if algorithm_file.exists():
        reduction = read('algorithm-bridge-submission.json')
        if reduction.get('status') in ('SKETCH_ACCEPTED', 'ACCEPTED'):
            for child in ('rational_theta_certificate', 'rational_cost_regime',
                          'cost_regime_solve_3sum'):
                required.append((main_graph, support[child]['theorem_id'],
                    reduction['submission_id'], reduction['theorem_id']))
    for name, record in support.items():
        if record.get('proof_status') != 'ACCEPTED':
            continue
        graph = read('ThreeSumSharpTail_' + name + '-graph.json')
        expected_children = {
            'encoding_bound': ['ThreeSumSharpTail.binomial_entropy_bounds'],
            'retained_tiles_cost': ['ThreeSumSharpTail.sharp_normalized_tail',
                                    'ThreeSumApsp.Spec.length_nineStrs'],
            'pruned_encoding_comparison': [],
            'rational_theta_certificate': [],
            'pruned_cost_certificate': ['ThreeSumSharpTail.pruned_encoding_comparison'],
            'rational_cost_regime': ['ThreeSumSharpTail.pruned_cost_certificate'],
            'pruned_program_correct': ['Light.Sec4.preCoreSpec_all',
                'Light.Sec4.queryAtSpec_all', 'Light.Sec4.shared_base58'],
            'pruned_program_solves': ['ThreeSumSharpTail.pruned_program_correct'],
            'pruned_lop_detection': ['ThreeSumSharpTail.pruned_program_solves',
                'ThreeSumSharpTail.rational_power_representation',
                'ThreeSumSharpTail.pruned_offline_steps'],
            'full_d_uniformize': ['Light.Sec3.claim_exactTriangleUniform_usingCorollary26'],
            'pruned_offline_steps': ['ThreeSumApsp.Spec.length_nineStrs',
                'ThreeSumApsp.Spec.mem_nineStrs', 'ThreeSumApsp.Spec.pairwise_lt_nineStrs',
                'ThreeSumApsp.eq_lowest_of_lt'],
            'uniform_three_sum_transfer': ['Light.Sec3.ChanHe.claim_CH20_Theorem_5_1',
                'Light.Sec3.claim_VW13_Theorem_4_3', 'Light.Sec3.realized_threeSum',
                'ThreeSumApsp.FromClaims.solvedAt_of_realized',
                'ThreeSumApsp.WordRam.SolvedInTime.endStatement'],
            'full_d_call_balance': [],
            'full_d_call_total': ['ThreeSumSharpTail.full_d_call_balance'],
            'full_d_extra_total': ['ThreeSumSharpTail.full_d_call_balance'],
            'full_d_explicit_time': ['ThreeSumSharpTail.full_d_call_total',
                'ThreeSumSharpTail.full_d_extra_total'],
            'full_d_parameter_host': ['Light.Sec3.et17_spec', 'Light.Sec3.obeysBound17_hostTime'],
            'rational_power_representation': [],
            'cost_regime_solve_3sum': ['ThreeSumSharpTail.rational_power_representation',
                'ThreeSumSharpTail.full_d_parameter_host',
                'ThreeSumSharpTail.full_d_explicit_time',
                'ThreeSumSharpTail.full_d_uniformize',
                'ThreeSumSharpTail.pruned_lop_detection',
                'ThreeSumSharpTail.uniform_three_sum_transfer'],
        }[name]
        children = []
        for child_name in expected_children:
            matches = [node['theorem_id'] for node in graph['nodes']
                       if node.get('theorem_name') == child_name]
            assert len(matches) == 1, (name, child_name, matches)
            children.append(matches[0])
        required.extend((graph, child, record['proof_submission_id'], record['theorem_id'])
                        for child in children)
    paths = []
    for graph, child, submission, parent in required:
        edges = {(e['source'], e['target'], e['kind']) for e in graph['edges']}
        sketch = 'sketch-' + submission
        assert (child, sketch, 'sketch') in edges, (child, sketch)
        assert (sketch, parent, 'sketch') in edges, (sketch, parent)
        paths.append({'child': child, 'submission_id': submission, 'parent': parent})
    names = ['binomial_entropy_bounds', 'sharp_normalized_tail', 'sharp_saving_strict',
             'explicit_parameter_certificate', 'admissible_parameters_solve_3sum',
             'threeSum_1999017', 'encoding_log_certificate', 'entropy_log_certificate']
    names.extend(name for name, record in support.items()
                 if record.get('proof_status') == 'ACCEPTED')
    records = []
    for name in names:
        theorem = read('ThreeSumSharpTail_' + name + '-current.json')
        records.append({'name': theorem['theorem_name'], 'id': theorem['theorem_id'],
                        'status': theorem['status']})
    for record in records[:4]:
        assert record['status'] == 'Proved', record
    for record in records[6:]:
        assert record['status'] == 'Proved', record
    result = {'read_at_utc': datetime.now(timezone.utc).isoformat(),
              'theorems': records, 'verified_paths': paths,
              'independent_roots': ['ThreeSumSharpTail.sharp_saving_strict',
                                    'ThreeSumSharpTail.pruned_encoding_comparison'],
              'remaining_connection': None if records[4]['status'] == records[5]['status'] == 'Proved'
                  else 'finite pruned cost regime to full-D reductions and the exact word-RAM solver',
              'all_requested_theorems_proved': all(record['status'] == 'Proved' for record in records),
              'main_graph_nodes': len(main_graph['nodes']),
              'main_graph_edges': len(main_graph['edges']),
              'tail_graph_nodes': len(tail_graph['nodes']),
              'tail_graph_edges': len(tail_graph['edges'])}
    (VERIFY / 'graph-check.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'Graph paths verified: {len(paths)}; completed supporting theorems: {len(records) - 2}.')
    print('Remaining goal status: ' + records[5]['status'])


if __name__ == '__main__':
    main()

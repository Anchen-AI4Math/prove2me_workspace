"""Publish the original even-n rational quartic aggregate kernel and inverse after fixed gates."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-kernel-bridge'
common.SOURCE = '1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb'
common.EXPECTED_CHECKS = 52
common.EXPECTED_AUTHOR_HASH = 'd0c86d3cb8f08e6c9e961782718cbedb8c319f4805002586cfa286f68d7eb057'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = '65a61c301d4fb2d85d01b304de1f48f9e12bdf45704d9dccfb999e070fbd7ea9'
common.SCOPE_LABEL = 'original even n>=2 rational quartic five-output kernel, bijection and exact summation'
common.EXTRA_SCOPE_AUDIT = {
    'original_F_bijection_proved': True,
    'original_F_bijection_scope': 'p=9,q=1,m=n,d=0; every even n>=2; rational quartic multipliers; actual outputs B,rho3,rho5,rho7,rho9',
    'legacy_full_F_proved_flag_scope': 'all-parameter families, beyond this original quartic theorem',
    'general_parameter_F_invertibility_proved': False,
    'integral_multiplier_inverse_proved': False,
    'denominator_height_bound_proved': False,
}
common.EXPLANATION_OVERRIDES = {
    'original_quartic_aggregate_kernel_zero': 'Start from the original rational quartic and the true zero five-output vector. Construct the genuine cumulative telescoper, establish the actual rational shift and polynomial quotient relation, and apply the proved polynomial degree obstruction. The quotient and original multiplier vanish. Even n and n>=2 remain explicit; neither kernel triviality nor a rational-function relationship is supplied as a premise.',
    'original_five_dimensional_map_bijective': 'Apply the actual quartic kernel theorem to the genuine five coefficient coordinates. The coordinate map is injective, and finite dimensionality of the same rational five-dimensional domain and codomain gives surjectivity. The proof uses the real five outputs, not the larger local coefficient array, and assumes no determinant or inverse.',
    'inverseMultiplier_actual_HasSum_and_absolute': 'Use the genuine linear equivalence obtained from the proved bijection, with its closed actual proof field, to recover the prescribed rational five-output target. The actual inverse multiplier has degree at most four. The complete cancellation and infinite-summation proofs give a genuine HasSum and norm summability for the original weighted series. A rational or integer output target has a rational polynomial preimage; no integral multiplier or denominator-height claim is asserted.'}
common.TITLE_OVERRIDES = {
    'original_quartic_aggregate_kernel_zero': 'Z9.F original kernel — Actual rational quartic kernel vanishes for even n>=2',
    'original_five_dimensional_map_bijective': 'Z9.F original inverse — Genuine five-output map is bijective for even n>=2',
    'inverseMultiplier_actual_HasSum_and_absolute': 'Z9.F original inverse — Prescribed rational target has actual absolute HasSum'}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '6767eca98651d8c1e5867134bb981b1ccf3a45ed24ea5603b067c71a113abf28'
    assert copy['source_sha256'] == common.SOURCE
    by_path = {r['root_relative_destination']: r for r in copy['files']}
    by_name = {r['theorem_name']: r for r in plan['targets']}
    assert len(author['targets']) == len(by_name) == 3
    assert {r['theorem'] for r in author['targets']} == set(by_name)
    normalized = []
    for row in author['targets']:
        target = by_name[row['theorem']]
        assert row['original_solution_reference_type_equal'] is True
        assert row['actual_original_type']
        assert set(row['original_axioms']) == set(row['solution_axioms']) == common.STANDARD
        normalized.append({**row, 'theorem_name': row['theorem'],
            'original_solution_reference_type_exactly_equal': row['original_solution_reference_type_equal'],
            'extra_top_level_solution_binders': [],
            'solution_sha256': by_path[target['local_solution']]['sha256'],
            'reference_sha256': by_path[target['local_reference']]['sha256']})
    return {**author, 'targets': normalized}


common.TARGET_AUDIT_ADAPTER = adapt_author_targets



def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('definitions', 'poll-jobs', 'problems', 'verify',
                                        'poll-proofs', 'link', 'check-only'))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Original even-n rational quartic inverse: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    for batch, name in [('coefficient-map', 'ZetaNine_CoefficientMap'),
                        ('coefficient-map-jet', 'ZetaNine_CoefficientMapJet'),
                        ('coefficient-map-injectivity', 'ZetaNine_CoefficientMapInjectivity'),
                        ('coefficient-map-partial-fractions', 'ZetaNine_CoefficientMapPartialFractions'),
                        ('coefficient-map-reflection', 'ZetaNine_CoefficientMapReflection'),
                        ('coefficient-map-finite-sum', 'ZetaNine_CoefficientMapFiniteSum'),
                        ('coefficient-map-summation', 'ZetaNine_CoefficientMapSummation'),
                        ('coefficient-map-aggregate', 'ZetaNine_CoefficientMapAggregate'),
                        ('coefficient-map-telescoper', 'ZetaNine_CoefficientMapTelescoper'),
                        ('coefficient-map-shift-degree', 'ZetaNine_CoefficientMapShiftDegree'),
                        ('', 'ZetaNine_HarmonicStability')]:
        parent = api.TASK / 'formalization/platform'
        if batch:
            parent = parent / batch
        receipt = json.loads((parent / f'definition-receipts/{name}.json').read_text(encoding='utf-8'))
        readback = client.call('GET', '/publish-jobs/' + receipt['job_id'])
        api.save(f'dependency-definition-readbacks/{name}.json', readback)
        assert readback['status'] == 'PUBLISHED', f'Wait for existing {name} publication job.'
    if args.mode == 'definitions':
        api.publish_definitions(client, definitions)
    elif args.mode == 'poll-jobs':
        api.poll_jobs(client, definitions, problems)
    elif args.mode == 'problems':
        api.publish_problems(client, definitions, problems)
    elif args.mode == 'verify':
        api.verify(client, problems)
    elif args.mode == 'poll-proofs':
        api.poll_proofs(client, problems)
    else:
        common.link(client, problems)


if __name__ == '__main__':
    main()

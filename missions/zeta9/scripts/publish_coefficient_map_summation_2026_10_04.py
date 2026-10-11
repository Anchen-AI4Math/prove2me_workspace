"""Publish actual absolute summability and the genuine exact infinite L identity."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-summation'
common.SOURCE = 'c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d'
common.EXPECTED_CHECKS = 25
common.EXPECTED_AUTHOR_HASH = 'eed4d2dc0cd429401cf7b7bbffd34cb556cc2159f773c57dcdb8fe9cbee37a79'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = '83d08d7146f472a2674f48158dd1154803ace82e2890506797d735b12041822e'
common.SCOPE_LABEL = 'actual absolute infinite summation'
common.EXPLANATION_OVERRIDES = {
    'actualSeries_norm_summable': 'The stronger degree gap proves that the genuine simple-pole total vanishes. Subtract the common 1/u term from the actual order-one partial fractions; each shifted difference is bounded in norm by j/u^2. All higher orders are bounded by convergent p-series. Finite sums of these actual bounds establish absolute summability of the true rational-function series. No evenness or summability input is assumed.',
    'actualSeries_hasSum_exactL': 'The actual reflection theorem cancels even-order totals for even n, and the stronger degree gap cancels the simple-pole total. The proved finite harmonic identity, genuine higher-order zeta limits and vanishing shifted tail identify the limit with the actual B plus rho_3*zeta(3), rho_5*zeta(5), rho_7*zeta(7), rho_9*zeta(9). Independently proved actual absolute summability then gives HasSum by uniqueness of partial-sum limits. Neither the cancellation nor the zeta identity is an extra hypothesis.',
    'original_integer_quartic_exact_infinite_L': 'For even n>=2, the actual degree bound of an integer quartic after rational mapping implies the stronger proper-degree gap. Apply the proved genuine HasSum result to this exact mapped multiplier to obtain the original infinite L identity. The construction is p=9, q=1, m=n, d=0, and no extra coefficient-cancellation or convergence input is supplied. This does not assert a useful small nonzero integer-form sequence or irrationality.'}
common.TITLE_OVERRIDES = {
    'actualSeries_norm_summable': 'Z9.F infinite sum — Actual strong-proper rational family is absolutely summable',
    'actualSeries_hasSum_exactL': 'Z9.F infinite sum — Genuine HasSum to the exact odd-zeta linear form',
    'original_integer_quartic_exact_infinite_L': 'Z9.F infinite sum — Original even integer-quartic L identity'}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == 'ab40b8a9bbb5904e1d6c277c7408803eb60d9b64efd0fea0af14c607386d4adc'
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
        print('Actual infinite summation: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    for batch, name in [('coefficient-map', 'ZetaNine_CoefficientMap'),
                        ('coefficient-map-jet', 'ZetaNine_CoefficientMapJet'),
                        ('coefficient-map-injectivity', 'ZetaNine_CoefficientMapInjectivity'),
                        ('coefficient-map-partial-fractions', 'ZetaNine_CoefficientMapPartialFractions'),
                        ('coefficient-map-reflection', 'ZetaNine_CoefficientMapReflection'),
                        ('coefficient-map-finite-sum', 'ZetaNine_CoefficientMapFiniteSum'),
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

"""Publish actual reflection and degree-gap cancellation after fixed review gates."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-reflection'
common.SOURCE = '8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707'
common.EXPECTED_CHECKS = 25
common.EXPECTED_AUTHOR_HASH = '7d48c5b7197fc9d9543b35063c256aa73bea606a59866ea81df227f731105651'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = '954a72aeed9af3188e62ed16030cdae9212da68d3c1d93eb6b75c2e854d50241'
common.SCOPE_LABEL = 'actual reflection and strong-degree cancellation'
common.EXPLANATION_OVERRIDES = {
    'local_coefficient_reflection': 'Reverse the actual finite products under t -> -t-n and use the genuine quadratic multiplier coordinate. The actual shifted numerator and unit denominator series transform by rescaling with -1. Uniqueness of the genuine cleared series then gives the sign of every actual local coefficient, for even n and orders 1 through 9. Reflection is derived from the true coefficients, not supplied as an array assumption.',
    'rho_even_order_zero': 'Reverse the finite pole-index sum and apply the proved reflection sign for every genuine local coefficient. For an even order the actual total equals its negative, hence is zero over the rationals. Only even n and orders 1 through 9 are required; no properness or infinite-series convergence is assumed.',
    'rho_one_zero_of_strong_proper': 'The proved actual global polynomial partial-fraction identity identifies its coefficient at degree 9n+8 with the genuine simple-pole total. The stronger degree gap forces this actual numerator coefficient to vanish. Thus the simple-pole total is zero for every n under StrongProper, without an even-n assumption. Strict properness alone does not suffice: the actual n=0, W=X^4 boundary has rho_1=1 and R(t)=1/t.'}
common.TITLE_OVERRIDES = {
    'local_coefficient_reflection': 'Z9.F reflection — Signs of the genuine reflected local coefficients',
    'rho_even_order_zero': 'Z9.F reflection — Actual even-order totals vanish for even n',
    'rho_one_zero_of_strong_proper': 'Z9.F reflection — Strong degree gap cancels the actual simple-pole total'}


def adapt_author_targets(author, plan):
    # Normalize fixed-hash field names in memory; retain all frozen evidence.
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == 'd8a5022833267eba1884f519a2f61b80343dfae4f53820e80ae57c2c9a6e5ad6'
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
        print('Actual reflection: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    for batch, name in [('coefficient-map', 'ZetaNine_CoefficientMap'),
                        ('coefficient-map-jet', 'ZetaNine_CoefficientMapJet'),
                        ('coefficient-map-injectivity', 'ZetaNine_CoefficientMapInjectivity'),
                        ('coefficient-map-partial-fractions', 'ZetaNine_CoefficientMapPartialFractions')]:
        receipt = json.loads((api.TASK / f'formalization/platform/{batch}/definition-receipts/{name}.json').read_text(encoding='utf-8'))
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

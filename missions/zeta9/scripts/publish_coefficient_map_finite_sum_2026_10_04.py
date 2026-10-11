"""Publish genuine finite harmonic identities, retaining the simple-pole term."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-finite-sum'
common.SOURCE = 'b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97'
common.EXPECTED_CHECKS = 29
common.EXPECTED_AUTHOR_HASH = 'b3b91da77d5c2523fdd9b091351ac302540206d4a882f24e8c0d6476e504eaf0'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = 'dea9dff29978c2576d9a3955bf7aa4a265a70edb60e4b6a9a7f9acd31815df50'
common.SCOPE_LABEL = 'actual finite harmonic summation'
common.EXPLANATION_OVERRIDES = {
    'actual_finite_harmonic_identity': 'For every positive integer summation point all genuine poles are regular, so the proved actual global partial fractions apply. Exchange only finite sums over points, poles and orders, and use the proved harmonic shift difference for each pole. This yields the exact finite harmonic identity for the actual rational function under strict properness, with all orders 1 through 9 retained. No reflection or infinite-summability input is assumed.',
    'actual_grouped_finite_identity': 'Start from the proved finite identity for the actual local coefficients. Split each harmonic difference into its common H_T part, actual shifted tail, and genuine constant term. Finite distributivity collects the true coefficient totals into the displayed grouped identity. In particular rho_1 times the first-order harmonic number remains present: the actual n=0, W=X^4 boundary yields H_T, and this finite statement does not assert convergence.',
    'harmonic_difference_eq_shifted': 'Split the actual finite generalized harmonic number at T, then reindex the remaining interval by u -> T+u. This gives the exact finite difference for every natural order, T and shift j, including order zero and the empty T=0 or j=0 intervals. All denominator identities are at positive shifted integer indices; no asymptotic or zeta-value input is needed.'}
common.TITLE_OVERRIDES = {
    'actual_finite_harmonic_identity': 'Z9.F finite sum — Actual rational family has the exact finite harmonic identity',
    'actual_grouped_finite_identity': 'Z9.F finite sum — Genuine constant, coefficient totals and shifted tail',
    'harmonic_difference_eq_shifted': 'Z9.F finite sum — Exact generalized harmonic shift difference'}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '3e89c024cc54d362fcf6e2ef6b6ca90272ff675883266176f266d2bc6a231094'
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
        print('Actual finite summation: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    for batch, name in [('coefficient-map', 'ZetaNine_CoefficientMap'),
                        ('coefficient-map-jet', 'ZetaNine_CoefficientMapJet'),
                        ('coefficient-map-injectivity', 'ZetaNine_CoefficientMapInjectivity'),
                        ('coefficient-map-partial-fractions', 'ZetaNine_CoefficientMapPartialFractions'),
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

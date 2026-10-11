"""Publish the actual polynomial shift-degree obstruction after fixed review gates."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-shift-degree'
common.SOURCE = '96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953'
common.EXPECTED_CHECKS = 24
common.EXPECTED_AUTHOR_HASH = '6139eee95fa63d6427a2bced0171b7ae9c5ec6917fcfa124802a995f32e06e18'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = 'e687dabc5c3d95123ac30e4671a6022362fa7a61ad1689a69402fb0c73ec368e'
common.SCOPE_LABEL = 'actual polynomial shift-degree obstruction'
common.EXPLANATION_OVERRIDES = {
    'actual_shift_difference_coefficient': 'Expand the genuine shift polynomials and the actual H(X+1). The two leading terms cancel. Taylor coefficients and the genuine leading coefficient give the coefficient at natDegree(H)+10 as (7n-2-natDegree(H))*leadingCoeff(H). Only H nonzero is required; no positivity, parity, monicity or operator equation is added.',
    'actual_shift_difference_degree_lower_bound': 'Under n>=1 and natDegree(H)<=7n-3, the proved actual coefficient is nonzero. Hence its exponent natDegree(H)+10 is at most the true operator degree. The degree assumption excludes the genuine n=1,H=X^5 resonance; it is retained exactly.',
    'actual_shift_difference_small_degree_implies_zero': 'If H were nonzero, the actual degree lower bound would give operator degree at least natDegree(H)+10, contradicting its assumed degree at most eight. The proof keeps the original quotient degree bound and n>=1. It supplies the polynomial obstruction; a separate proof establishes the relationship with the genuine rational telescoper.'}
common.TITLE_OVERRIDES = {
    'actual_shift_difference_coefficient': 'Z9.F shift degree — Exact coefficient of the genuine polynomial difference',
    'actual_shift_difference_degree_lower_bound': 'Z9.F shift degree — Actual operator degree in the nonresonant domain',
    'actual_shift_difference_small_degree_implies_zero': 'Z9.F shift degree — Low operator degree forces the quotient to vanish'}


def adapt_author_targets(author, plan):
    # Normalize fixed-hash field names in memory; retain all frozen evidence.
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '48edfb368179cb7ed0f746ca2acc4bbafc06103d5e6bc498cdc8b4e6e42e3cb9'
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


def adapt_independent_review(review):
    # The fixed reviewer uses 'scope' for this precise informational limitation.
    scope = 'This batch proves the actual rational polynomial shift obstruction. It does not import or establish a rational telescoper bridge, full coefficient-map inverse or zeta irrationality. Both original quotient degree and low operator degree hypotheses remain exact.'
    findings = []
    for row in review.get('findings', []):
        if row.get('severity') == 'scope':
            assert row.get('message') == scope
            row = {**row, 'severity': 'informational'}
        findings.append(row)
    return {**review, 'findings': findings}


common.INDEPENDENT_REVIEW_ADAPTER = adapt_independent_review


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('definitions', 'poll-jobs', 'problems', 'verify',
                                        'poll-proofs', 'link', 'check-only'))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Actual shift degree: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
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

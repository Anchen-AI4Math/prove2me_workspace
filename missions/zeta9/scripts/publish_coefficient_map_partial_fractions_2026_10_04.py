"""Publish reviewed actual global partial fractions on their genuine proper domain."""
from __future__ import annotations
import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-partial-fractions'
common.SOURCE = 'eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a'
common.EXPECTED_CHECKS = 22
common.EXPECTED_AUTHOR_HASH = 'd416ad774d2f4a7b599151aef4f460a42395f116cf5e13d577d311ca2a9aa20f'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = 'b24b529239f6f583ae2c3565f76c970d6351f8f86d1edef7af7708eaa5321933'
common.SCOPE_LABEL = 'actual finite global partial fractions'
common.EXPLANATION_OVERRIDES = {
    'candidate_local_coefficients': 'The candidate polynomial numerator is formed from the actual order-1-through-9 local coefficients. At a given pole its own block reconstructs the truncation of the genuine cleared power series; every other block contains X^9 after the actual shift. Thus the candidate cleared series has exactly the genuine coefficients at each of the nine orders. This statement has no properness assumption and does not replace the original coefficients by an abstract array.',
    'actual_global_polynomial_partial_fractions': 'All genuine local coefficients of the difference between the true weighted numerator and the actual partial-fraction candidate vanish. Each ninth-power pole factor divides that difference, and the distinct factors are pairwise coprime. Their full product therefore divides it. Strict properness bounds the true numerator degree, while the explicitly constructed candidate has degree at most 9n+8, forcing the difference to vanish. This proves the actual global polynomial identity without a partial-fraction identity assumption.',
    'actual_global_partial_fractions': 'Divide the proved actual polynomial identity by the genuine ninth-power denominator at a rational point where every t+j is nonzero. The true factorization identifies each actual summand with its local coefficient divided by (t+j)^s. Only regular rational points are asserted. Strict properness can leave a simple-pole total, so this finite algebraic identity does not itself assert infinite-series convergence.'}
common.TITLE_OVERRIDES = {
    'candidate_local_coefficients': 'Z9.F global PF — The actual candidate reconstructs every genuine local coefficient',
    'actual_global_polynomial_partial_fractions': 'Z9.F global PF — Exact actual polynomial partial-fraction identity',
    'actual_global_partial_fractions': 'Z9.F global PF — Actual global partial fractions at regular rational points'}


def adapt_author_targets(author, plan):
    # Fixed-hash author evidence is normalized in memory; no frozen file is edited.
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT/'root-copy-plan.json') == '6d60147f78b8463471c32fb257c9fd3fbad22c970733487c469dfb821650b847'
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
    parser.add_argument('mode', choices=('definitions','poll-jobs','problems','verify','poll-proofs','link','check-only'))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Actual finite global PF: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    for batch, name in [('coefficient-map','ZetaNine_CoefficientMap'),
                        ('coefficient-map-jet','ZetaNine_CoefficientMapJet'),
                        ('coefficient-map-injectivity','ZetaNine_CoefficientMapInjectivity')]:
        receipt = json.loads((api.TASK/f'formalization/platform/{batch}/definition-receipts/{name}.json').read_text(encoding='utf-8'))
        readback = client.call('GET','/publish-jobs/'+receipt['job_id'])
        api.save(f'dependency-definition-readbacks/{name}.json',readback)
        assert readback['status'] == 'PUBLISHED', f'Wait for existing {name} publication job.'
    if args.mode == 'definitions': api.publish_definitions(client,definitions)
    elif args.mode == 'poll-jobs': api.poll_jobs(client,definitions,problems)
    elif args.mode == 'problems': api.publish_problems(client,definitions,problems)
    elif args.mode == 'verify': api.verify(client,problems)
    elif args.mode == 'poll-proofs': api.poll_proofs(client,problems)
    else: common.link(client,problems)


if __name__ == '__main__':
    main()

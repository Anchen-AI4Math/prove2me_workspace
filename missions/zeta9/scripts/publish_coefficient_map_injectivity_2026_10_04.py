"""Publish the reviewed complete local-array injectivity, preserving its proper domain."""
from __future__ import annotations
import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-injectivity'
common.SOURCE = 'ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095'
common.EXPECTED_CHECKS = 16
common.EXPECTED_AUTHOR_HASH = 'b91251de9261a7656de3274575072995452706d8a9ee0e570ae9ded4ce5b2253'
common.SCOPE_LABEL = 'actual complete local-array injectivity'
common.EXPLANATION_OVERRIDES = {
    'all_local_coefficients_zero_implies_zero': 'Every order 1 through 9 is an actual coefficient of the genuine cleared formal series. Vanishing makes X^9 divide every shifted weighted numerator, hence (X+j)^9 divides the true weighted numerator for every pole j. The factors are pairwise coprime, so the full ninth-power denominator divides it. The strict proper degree bound forces the numerator to be zero. The actual unweighted numerator is nonzero, and composition with the degree-two coordinate is injective, so W=0. No aggregate coefficient-map or irrationality input is assumed.',
    'fullLocalCoefficientMap_injective': 'Apply the actual coefficient subtraction identity and the proved zero-array theorem to W-V. The maximum-degree bound preserves strict properness under subtraction. Equality of the actual finite (n+1)-by-9 local coefficient arrays then gives W=V. This map retains all pole locations and orders; it is not the five-dimensional aggregate map F from the research notes.',
    'quartic_is_proper': 'The explicit bound deg(W)<=4 implies 2n+2deg(W)<9(n+1) for every natural n. This is strict properness only, which permits O(1/t); at n=0, W=X^4 is the actual 1/t boundary. This theorem does not prove the stronger degree gap needed for simple-pole cancellation or infinite summation.'}
common.TITLE_OVERRIDES = {
    'all_local_coefficients_zero_implies_zero': 'Z9.F local array — Zero genuine coefficients force the proper multiplier to vanish',
    'fullLocalCoefficientMap_injective': 'Z9.F local array — Injectivity of the complete actual pole-coefficient array',
    'quartic_is_proper': 'Z9.F local array — Every quartic multiplier satisfies strict properness'}


def adapt_author_targets(author, plan):
    # Normalize only field names of a fixed-hash audit; never edit frozen evidence.
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT/'root-copy-plan.json') == '51bc6ae331a1e8b781c4dd8250248e4bed8e7c5092bb50db5bcd73f4423cf9c3'
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
            # Exact original/solution/reference type equality rules out extra binders.
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
        print('Frozen proper-domain local-array sources, independent review and actual scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    # Existing published Base and Jet definition jobs are the only allowed dependencies.
    for batch, name in [('coefficient-map','ZetaNine_CoefficientMap'),('coefficient-map-jet','ZetaNine_CoefficientMapJet')]:
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

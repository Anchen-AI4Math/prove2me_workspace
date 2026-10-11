"""Publish the genuine rational telescoper only after fixed review gates."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-telescoper'
common.SOURCE = '8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121'
common.EXPECTED_CHECKS = 40
common.EXPECTED_AUTHOR_HASH = '28f93d0ab2f580cf7edae113ce297e40486882de33236d0bac08d426ee2abe0b'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = 'fd669f98db06df18d7f1e10c5c734499be42bf3b78306aceafe9052a451c21d3'
common.SCOPE_LABEL = 'actual cumulative rational telescoper and quotient degree bound'
common.EXPLANATION_OVERRIDES = {
    'actual_weightedR_is_difference': 'Construct the cumulative coefficients from the genuine local array. The actual zero five-output vector, reflection and strong degree gap cancel every order total. At regular rational points, genuine global partial fractions yield the original weighted rational function as Q(t)-Q(t+1). All original parity, degree-gap, zero-output and regular-point hypotheses remain explicit.',
    'telescoper_actual_rational_representation': 'Combine the actual cumulative finite sum over poles zero through n-1 using the real cleared denominator. This identifies its genuine polynomial numerator divided by that denominator to the ninth power at every regular point, for n>=1. This representation needs no parity or zero-output assumption.',
    'actual_polynomial_quotient_degree_bound': 'Under the actual even, strong and zero-aggregate hypotheses, exact summation gives Q(1)=0. The genuine difference propagates the positive and negative roots. Their 2n+2 distinct linear factors divide the actual numerator, and the original numerator degree bound gives an actual quotient of degree at most 7n-3. No polynomial quotient existence or kernel vanishing is added as a premise.'}
common.TITLE_OVERRIDES = {
    'actual_weightedR_is_difference': 'Z9.F telescoper — Genuine weighted rational function is a cumulative difference',
    'telescoper_actual_rational_representation': 'Z9.F telescoper — Actual cleared rational representation',
    'actual_polynomial_quotient_degree_bound': 'Z9.F telescoper — Actual root divisibility and quotient degree bound'}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '7162be6b7d324c74cc961a35a29b2b7ef24111ee086dfb09243425d175bd46bb'
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
        print('Actual telescoper: frozen sources, independent review and scoped build verified. No API operation.')
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

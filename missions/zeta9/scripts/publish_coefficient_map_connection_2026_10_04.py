"""Publish the actual original polynomial connection system after frozen gates."""
from __future__ import annotations

import argparse
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-connection'
common.SOURCE = '098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
common.EXPECTED_CHECKS = 33
common.EXPECTED_AUTHOR_HASH = '876033891293bc5fdf4f8846d26d099631a5124c6f6c245e5c1ad996bd8779e5'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = '3e36738130bd205946526b4b2a87d0443d094af24275c2ac4ee920d365709813'
common.SCOPE_LABEL = 'original n>=1 polynomial connection kernel, bijection and five unique systems'
common.EXTRA_SCOPE_AUDIT = {
    'original_connection_system_proved': True,
    'original_connection_system_scope': 'all n>=1; genuine degree-4 P and degree-9 q; original D P(u)+H(q) polynomial operator',
    'actual_rational_function_parameter_transport_proved': False,
    'actual_five_output_parameter_transport_proved': False,
    'explicit_F_matrix_proved': False,
    'integral_multiplier_inverse_proved': False,
}
common.EXPLANATION_OVERRIDES = {
    'connection_homogeneous_kernel_zero': 'Use the actual polynomial identity D P(u)+H(q)=0 with n>=1 and degree(q)<=9. Tenfold divisibility at t=1 forces multiplicity at least ten at the actual q root n, contradicting degree at most nine unless q vanishes. The remaining composition identity forces P to vanish. No aggregate kernel, determinant, connection invertibility or zeta independence is assumed.',
    'connectionLinearMap_bijective': 'The genuine fifteen-coordinate map takes five P coefficients and ten q coefficients to the fifteen even t coefficients of the original polynomial operator. Reflection and its degree bound recover the full polynomial from these coordinates. The actual homogeneous kernel theorem gives injectivity, and finite dimensionality gives surjectivity. This t-coefficient basis is triangularly equivalent to the paper u-coefficient basis; it is not claimed to have identical matrix entries.',
    'connection_five_systems_unique': 'For each of the five original right sides, construct the unique pair of rational polynomials P and q with degrees at most four and nine satisfying the full original connection identity. The target is the actual scaled three-factor Z polynomial times (u-n-1)^r. All n>=1 are covered. This polynomial statement leaves actual rational-function and five-output parameter transport as separate obligations.',
}
common.TITLE_OVERRIDES = {
    'connection_homogeneous_kernel_zero': 'Z9 connection — Original polynomial homogeneous kernel vanishes for n>=1',
    'connectionLinearMap_bijective': 'Z9 connection — Genuine fifteen-coordinate connection map is bijective',
    'connection_five_systems_unique': 'Z9 connection — Five original right-side systems have unique rational solutions',
}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '19dd8f1d73b41cb10c1d85c9822ad80deb5082c0c721158488684a48d1a18d66'
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


def adapt_independent_findings(review):
    # The exact frozen report uses topic/detail findings. Keep those bytes intact;
    # classify only these reviewed historical diagnostics and scope statements.
    assert review['source_sha256'] == common.SOURCE
    assert review['author_sha256'] == common.EXPECTED_AUTHOR_HASH
    assert len(review['checks']) == 47 and len(review['stable_files']) == 940
    assert review['counts']['failed_Lean_invocations'] == 0
    assert [f['topic'] for f in review['findings']] == [
        'cache', 'source_and_proof_fields', 'pretty_printing', 'Root', 'scope']
    assert all(set(f) == {'topic', 'detail'} and f['detail'] for f in review['findings'])
    return {**review, 'findings': [
        {**f, 'severity': 'informational'} for f in review['findings']]}


common.INDEPENDENT_REVIEW_ADAPTER = adapt_independent_findings


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('definitions', 'poll-jobs', 'problems', 'verify',
                                        'poll-proofs', 'link', 'check-only'))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Original connection system: frozen sources, independent review and scoped build verified. No API operation.')
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

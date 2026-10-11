"""Publish the actual five-output linear structure after fixed review gates."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-aggregate'
common.SOURCE = 'e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299'
common.EXPECTED_CHECKS = 35
common.EXPECTED_AUTHOR_HASH = 'f7062cfecbbe14e5d36e69165e159630f4e090bbe1989b5d79ddc9bae2435ddf'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.EXPECTED_INDEPENDENT_HASH = 'ff464d565f54cdcb8efd6445864fb278ed8ed0525c2b0fbab6fe158c96d5c24d'
common.SCOPE_LABEL = 'actual five-output linear structure'
common.EXPLANATION_OVERRIDES = {
    'aggregate_add': 'Derive additivity from the genuine weighted local coefficients, then collect the actual finite constant term and the four actual odd-order totals. This proves additivity of the original five outputs (B,rho3,rho5,rho7,rho9), rather than an unrelated full coefficient array. Its data and the proven linear-map fields agree with the actual native definitions.',
    'polynomial_restore': 'For every rational polynomial of natural degree at most four, evaluate its actual five coefficient coordinates. The genuine coordinate polynomial reconstructs those coefficients at every degree, with coefficients above four zero by the original degree bound. This includes zero and nonmonic polynomials, and supplies no invertibility assumption.',
    'aggregate_zero_all_rho': 'Vanishing of the actual five-output vector gives the four odd totals and the actual constant term zero. The separately proved genuine reflection cancels even-order totals for even n; the stronger degree bound cancels the simple-pole total. Thus all actual orders one through nine vanish, with the original Even and StrongProper premises retained. This result does not itself assume or assert aggregate injectivity.'}
common.TITLE_OVERRIDES = {
    'aggregate_add': 'Z9.F aggregate — Additivity of the actual five outputs',
    'polynomial_restore': 'Z9.F aggregate — Exact recovery from genuine quartic coordinates',
    'aggregate_zero_all_rho': 'Z9.F aggregate — Actual zero outputs cancel all coefficient totals'}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == 'defc8a43e447894f4024a70abc7e551738f15e20dcad220870d0984d79b4366d'
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
    # Normalize two fixed shared-root bindings without changing the frozen report.
    shared = {
        '../../.lake/build/lib/lean/Definitions/Def_ZetaNine_HarmonicStability.olean': '.lake/build/lib/lean/Definitions/Def_ZetaNine_HarmonicStability.olean',
        '../../Definitions/Def_ZetaNine_HarmonicStability.lean': 'Definitions/Def_ZetaNine_HarmonicStability.lean',
    }
    files = []
    normalized = set()
    for row in review['stable_files']:
        relative = row.get('task_relative')
        if relative in shared:
            assert row['root_relative'] == 'missions/zeta9/' + relative
            row = {**row, 'task_relative': None, 'root_relative': shared[relative]}
            normalized.add(relative)
        files.append(row)
    assert normalized == set(shared)
    return {**review, 'stable_files': files}


common.INDEPENDENT_REVIEW_ADAPTER = adapt_independent_review


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('definitions', 'poll-jobs', 'problems', 'verify',
                                        'poll-proofs', 'link', 'check-only'))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Actual aggregate: frozen sources, independent review and scoped build verified. No API operation.')
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

"""Publish the actual even-n F matrix after the independent frozen gate."""
from __future__ import annotations

import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / 'formalization/platform/coefficient-map-matrix'
common.SOURCE = 'a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99'
common.EXPECTED_CHECKS = 33
common.EXPECTED_AUTHOR_HASH = 'c908b981d4fbb5b9c84ec137e829e1a1ac06b382640ef447811208b23bc09f8e'
common.INDEPENDENT_REVIEW_PATH = 'independent/independent-integration-review.json'
common.SCOPE_LABEL = 'actual even n>=2 F matrix, rational selected inverse and exact HasSum'
common.EXTRA_SCOPE_AUDIT = {
    'actual_F_matrix_even_n_ge_two_proved': True,
    'matrix_convention': 'monomial rows, actual five-output columns; toMatrix is the transpose',
    'actual_selected_rational_inverse_coordinates_proved': True,
    'actual_selected_exact_HasSum_and_absolute_proved': True,
    'inverse_multiplier_integer_coefficients_proved': False,
    'denominator_height_bounds_proved': False,
    'actual_five_output_parameter_transport_proved': False,
    'all_parameter_F_invertibility_proved': False,
}
common.EXPLANATION_OVERRIDES = {
    'actualFMatrix_det_ne_zero': 'The actual matrix has monomial rows and the genuine constant/rho3/rho5/rho7/rho9 output columns. Its row action equals the original quartic aggregate map. The independently proved bijection for even n>=2 makes the determinant a unit and hence nonzero. The standard column-action matrix is its transpose.',
    'selectedIntegerMultiplier_coordinates_product': 'For integer target values b and a, form the actual output (b,0,0,0,a). The coefficients of the selected rational quartic multiplier are exactly (b,a) times the two-row selection matrix times the actual F inverse. The multiplier is rational; this proof does not establish integer coefficients or denominator bounds.',
    'selectedIntegerMultiplier_actual_HasSum_and_absolute': 'The actual selected rational quartic has outputs (b,0,0,0,a). Its genuine weighted rational function on positive natural arguments has sum b+a*zetaReal(9) and is absolutely summable. zetaReal is the real part of the actual Riemann zeta function. The assumptions are precisely even n>=2 and integer target values b,a.',
}
common.TITLE_OVERRIDES = {
    'actualFMatrix_det_ne_zero': 'Z9.F — Actual five-output matrix is nonsingular for even n>=2',
    'selectedIntegerMultiplier_coordinates_product': 'Z9.F — Selected rational quartic coefficients equal (b,a) S F inverse',
    'selectedIntegerMultiplier_actual_HasSum_and_absolute': 'Z9.F — Selected actual rational function has absolute sum b+a zeta(9)',
}


def adapt_author_metadata(author):
    # Recover omitted metadata from the exact files already bound by this report.
    # The frozen author bytes are never edited and no new execution is claimed.
    assert common.digest(common.OUT / 'author-audit.json') == common.EXPECTED_AUTHOR_HASH
    assert author['source_sha256'] == common.SOURCE
    bound = {r['task_relative']: r for r in author['stable_files']}
    names = ['.rt/ma1/lean-toolchain', '.rt/ma1/lake-manifest.json',
             'formalization/platform/coefficient-map-matrix/toolchain.log',
             'formalization/platform/coefficient-map-matrix/toolchain-exit.txt']
    for relative in names:
        row = bound[relative]
        path = common.api.TASK / relative
        assert path.stat().st_size == row['bytes'] and common.digest(path) == row['sha256']
    toolchain = (common.api.TASK / names[0]).read_text(encoding='utf-8').strip()
    manifest = json.loads((common.api.TASK / names[1]).read_text(encoding='utf-8'))
    mathlib = [p for p in manifest['packages'] if p['name'] == 'mathlib']
    assert len(mathlib) == 1
    assert (common.api.TASK / names[3]).read_text(encoding='utf-8').strip() == '0'
    assert 'Lean (version 4.33.1,' in (common.api.TASK / names[2]).read_text(encoding='utf-8')
    assert toolchain == 'leanprover/lean4:v4.33.1' and mathlib[0]['rev'] == common.api.ENV
    return {**author, 'lean_toolchain': toolchain, 'mathlib_rev': mathlib[0]['rev']}


def adapt_author_targets(author, plan):
    copy = common.api.read('root-copy-plan.json')
    assert common.digest(common.OUT / 'root-copy-plan.json') == '94e573d015d6aba167adc32bad6e7b6427a81cfdf290e7483415ce2fbee7498c'
    assert copy['source_sha256'] == common.SOURCE
    by_path = {r['root_relative_destination']: r for r in copy['files']}
    by_name = {r['theorem_name']: r for r in plan['targets']}
    assert len(author['targets']) == len(by_name) == 3
    assert {r['theorem'] for r in author['targets']} == set(by_name)
    normalized = []
    for row in author['targets']:
        target = by_name[row['theorem']]
        original = row['actual_original_type']
        assert original and original == row['solution_type'] == row['reference_type'] == row['wrapper_type']
        assert set(row['original_axioms']) == set(row['solution_axioms']) == set(row['wrapper_axioms']) == common.STANDARD
        # References are declaration mirrors and are explicitly excluded as proofs.
        assert set(row['reference_axioms']) == common.STANDARD | {'sorryAx'}
        normalized.append({**row, 'theorem_name': row['theorem'],
            'original_solution_reference_type_exactly_equal': True,
            'extra_top_level_solution_binders': [],
            'solution_sha256': by_path[target['local_solution']]['sha256'],
            'reference_sha256': by_path[target['local_reference']]['sha256']})
    return {**author, 'targets': normalized}


common.AUTHOR_METADATA_ADAPTER = adapt_author_metadata
common.TARGET_AUDIT_ADAPTER = adapt_author_targets


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('definitions', 'poll-jobs', 'problems', 'verify',
                                        'poll-proofs', 'link', 'check-only'))
    args = parser.parse_args()
    pin_path = common.OUT / 'independent/Root-reviewed-publication-pin.json'
    if not pin_path.exists():
        raise SystemExit('Awaiting completed independent review and explicit Root byte/hash verification; no API operation.')
    pin = json.loads(pin_path.read_text(encoding='utf-8'))
    assert pin['Root_rehashed_all_independent_bindings'] is True
    assert pin['author_sha256'] == common.EXPECTED_AUTHOR_HASH
    assert pin['source_sha256'] == common.SOURCE
    common.EXPECTED_INDEPENDENT_HASH = pin['independent_report_sha256']
    definitions, problems = common.gate()
    if args.mode == 'check-only':
        print('Actual matrix: frozen sources, independent review and scoped build verified. No API operation.')
        return
    api = common.api
    client = api.Client()
    if args.mode == 'definitions': api.publish_definitions(client, definitions)
    elif args.mode == 'poll-jobs': api.poll_jobs(client, definitions, problems)
    elif args.mode == 'problems': api.publish_problems(client, definitions, problems)
    elif args.mode == 'verify': api.verify(client, problems)
    elif args.mode == 'poll-proofs': api.poll_proofs(client, problems)
    else: common.link(client, problems)


if __name__ == '__main__':
    main()

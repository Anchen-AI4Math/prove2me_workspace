"""Personal complete pure Phase preflight, not independent Lean verification."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from fractions import Fraction as Q
from math import comb
import collections
import json
import re
import sys
sys.dont_write_bytecode = True
import prepare_independent as p

PREP_SHA = 'a56d7e71bb4d0372116eeea4de707e6b853b3420f90a51223c934d3c12174bf1'


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    report = p.AUTHOR / 'author-audit.json'
    assert p.sha(report) == p.AUTHOR_SHA
    author = p.load(report)
    assert len(author['stable_bindings']) == 25818
    checked = []
    def check_binding(b):
        actual = Path(b['absolute_path']).resolve()
        assert actual.name.lower() not in {'credentials.json', '.env'}
        assert actual.is_relative_to(p.TASK.resolve()) or actual.is_relative_to((p.ROOT / '.lake/packages').resolve()) or actual.is_relative_to(p.TOOLCHAIN)
        if b.get('task_relative'):
            rel = Path(b['task_relative'])
            assert not rel.is_absolute() and '..' not in rel.parts and (p.TASK / rel).resolve() == actual
        if b.get('root_relative'):
            rel = Path(b['root_relative'])
            assert not rel.is_absolute() and '..' not in rel.parts and (p.ROOT / rel).resolve() == actual
        assert actual.stat().st_size == b['bytes'] and p.sha(actual) == b['sha256'], str(actual)
        return b
    print('Personal complete author rehash: 25818 bindings, 2 read threads.', flush=True)
    with ThreadPoolExecutor(max_workers=2) as pool:
        for index, b in enumerate(pool.map(check_binding, author['stable_bindings']), 1):
            checked.append(b)
            if index % 5000 == 0: print('Personally rehashed ' + str(index), flush=True)
    assert len(checked) == 25818
    assert len({str(Path(b['absolute_path']).resolve()).casefold() for b in checked}) == 25818
    assert p.sha(p.OUT / 'preparation-state.json') == PREP_SHA
    state = p.load(p.OUT / 'preparation-state.json')
    checks = []
    def require(name, condition):
        assert condition, name
        checks.append({'name': name, 'passed': True})
    theorem_prefixes, definitions, contracts = {}, {}, []
    for contract in state['source_contracts']:
        name = contract['module']
        for key in ['shared_source', 'frozen_author_export', 'independent_fresh_source']:
            b = contract[key]
            require('contract rehash ' + key + ' ' + name, p.binding(p.TASK / b['task_relative']) == b)
        original = p.TASK / contract['shared_source']['task_relative']
        export = p.TASK / contract['frozen_author_export']['task_relative']
        own = p.TASK / contract['independent_fresh_source']['task_relative']
        old, fresh = original.read_text(encoding='utf-8-sig'), own.read_text(encoding='utf-8-sig')
        require('true verified SOURCE exact ' + name, p.sha(original) == p.ORIGINAL[name] and p.sha(export) == p.EXPECTED[name] and own.read_bytes() == export.read_bytes())
        require('complete original theorem forall prefixes ' + name, p.prefixes(old) == p.prefixes(fresh))
        require('complete original definition bodies ' + name, p.defs(old) == p.defs(fresh))
        require('original import definition prelude exact ' + name, old[:old.index('theorem ')] == fresh[:fresh.index('theorem ')])
        require('actual SOURCE without holes ' + name, not re.search(r'\b(sorry|admit|native_decide)\b', fresh)
                and not re.search(r'(?m)^\s*(axiom|opaque|constant)\s', fresh))
        theorem_prefixes.update(p.prefixes(old)); definitions.update(p.defs(old)); contracts.append(contract)
    require('34 exact forall preparations', len(theorem_prefixes) == 34 and theorem_prefixes == state['expected_theorem_prefixes'])
    require('seven full definition preparations', len(definitions) == 7 and definitions == state['original_full_definition_source'])
    for b in state['configs'] + state['controls']:
        require('fresh control/config rehash ' + b['task_relative'], p.binding(p.TASK / b['task_relative']) == b)
    require('no independent compiler receipts', not (p.OUT / 'compile-receipt.json').exists())
    require('no independent object build directory', not (p.PROJECT / 'b').exists())
    require('no independent package junction or lake directory', not (p.PROJECT / '.lake').exists())
    require('no independent proof objects present', not list(p.PROJECT.rglob('*.olean*')))
    types = p.load(p.AUTHOR / 'actual-types-and-auxiliaries.json')
    kernel = p.load(p.AUTHOR / 'actual-kernel-and-definitions.json')
    boundaries = p.load(p.AUTHOR / 'actual-typed-boundaries.json')
    theorems = {p.NS + n for n in theorem_prefixes}
    defs = {p.NS + n for n in definitions}
    actual_thms = [r for r in types if r['kind'] == 'theorem']
    actual_defs = [r for r in types if r['kind'] == 'definition']
    require('author 34 exact original theorem inventory', len(actual_thms) == 34 and {r['name'] for r in actual_thms} == theorems)
    require('author seven full definition inventory', len(actual_defs) == 7 and {r['name'] for r in actual_defs} == defs)
    inventories = [r for r in types if r['kind'] == 'module_inventory']
    module_names = {n for r in inventories for n in r['constant_names'] + r['extra_names']}
    module_records = {r['name']: r for r in types if r['kind'] in ['module_declaration', 'module_extra']}
    require('every actual generated/match/eq/public auxiliary included', len(inventories) == 2 and module_names == set(module_records)
            and len(module_names) == 68 and sorted(module_names - theorems - defs) == state['auxiliary_expected_names'])
    require('all 68 source declaration full values genuinely typed', all(r['value_raw'] is not None and r['full_value_typed'] for r in module_records.values()))
    thm_comparisons = [r for r in kernel if r['kind'] == 'theorem_compare']
    def_comparisons = [r for r in kernel if r['kind'] == 'definition_compare']
    helper_comparisons = [r for r in kernel if r['kind'] == 'definition_helper_compare']
    rfls = [r for r in kernel if r['kind'] == 'definition_rfl']
    domain = [r for r in kernel if r['kind'] == 'exact_domain_compare']
    require('author 34 full type Expr.equal and isDefEq', len(thm_comparisons) == 34 and {r['actual'] for r in thm_comparisons} == theorems
            and all(r['type_exprEqual'] and r['type_isDefEq'] for r in thm_comparisons))
    require('seven raw Expr.equal false results retained', len(def_comparisons) == 7 and {r['actual'] for r in def_comparisons} == defs
            and all(r['value_exprEqual'] is False for r in def_comparisons))
    require('seven actual complete definition kernel equalities', all(r['type_exprEqual'] and r['type_isDefEq'] and r['value_isDefEq']
            and r['normalized_value_exprEqual'] and r['normalized_value_isDefEq'] for r in def_comparisons))
    require('seven full-function rfl witnesses', len(rfls) == 7 and {r['name'] for r in rfls} == {'original_value_' + n for n in definitions}
            and all(r['full_value_typed'] and r['value_raw'] is not None for r in rfls))
    require('all14 paired helper full proofs and types checked', len(helper_comparisons) == 14 and len({r['actual'] for r in helper_comparisons}) == 8
            and all(r['type_exprEqual'] and r['value_exprEqual'] and r['type_isDefEq'] and r['value_isDefEq']
                    and r['actual_value_typed'] and r['expected_value_typed'] for r in helper_comparisons))
    require('author unrestricted exact open domain', len(domain) == 1 and domain[0]['type_exprEqual'] and domain[0]['type_isDefEq']
            and theorem_prefixes['phase_global_upper_bound'] == 'theorem phase_global_upper_bound :\n    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) :=')
    require('15 typed boundary proofs', len(boundaries) == 15 and all(r['kind'] == 'typed_boundary' and r['isProp'] and r['full_value_typed']
            and r['value_raw'] is not None for r in boundaries))
    raw_count, std3_count = 0, 0
    for r in types + kernel + boundaries:
        for key, value in r.items():
            if key.endswith('axioms'):
                require('actual Std3 list ' + str(std3_count), set(value) <= {'propext', 'Classical.choice', 'Quot.sound'})
                std3_count += 1
            if key.endswith('_raw') and value is not None:
                require('untruncated raw expression ' + str(raw_count), isinstance(value, str) and value and '...' not in value and '…' not in value)
                raw_count += 1
    require('author raw and Std3 exact totals', raw_count == 313 and std3_count == 243)
    control = (p.PROJECT / 'APIPhaseTypes.lean').read_text(encoding='utf-8')
    require('independent declaration inventory covers all source names', 'data.constNames' in control and 'data.extraConstNames' in control
            and 'apRecord "module_declaration"' in control and 'apRecord "module_extra"' in control and 'inferType e' in control)
    control_kernel = (p.PROJECT / 'APIPhaseKernel.lean').read_text(encoding='utf-8')
    require('independent seven whole-function rfl SOURCE witnesses', all(
        'theorem independent_original_value_' + n + ' : APIndOriginalDefs.' + n + ' = ' + p.NS + n + ' := rfl' in control_kernel
        for n in definitions))
    require('independent raw observations remain unnormalized', 'valueEqual := Expr.equal av bv' in control_kernel and
            'valueDefEq ← isDefEq av bv' in control_kernel and 'type_actual_raw' in control_kernel and 'value_actual_raw' in control_kernel)
    require('independent normalization only individually typed proposition helper unfolding', 'unless (← isProp a.type) && (← isProp b.type)' in control_kernel
            and 'Expr.equal a.type c.type && Expr.equal va0 vc' in control_kernel and 'inferType va' in control_kernel and 'inferType vb' in control_kernel)
    a = Q(101, 100)
    raw = [Q((comb(10, k - 1) if 1 <= k <= 11 else 0) - (comb(10, k) if 0 <= k <= 10 else 0)) for k in range(12)]
    raw[10] -= 2; raw[11] -= 1
    shifted = [sum((raw[k] * comb(k, j) * a ** (k - j) for k in range(j, 12)), Q(0)) for j in range(11)]
    arithmetic = p.load(p.OUT / 'pure-independent-arithmetic-and-code.json')
    require('own exact arithmetic 11 positive translated coefficients', raw[11] == 0 and all(x > 0 for x in shifted)
            and [str(x) for x in shifted] == arithmetic['shifted_gap_coefficients'])
    coefficient_text = theorem_prefixes['phaseGap_identity']
    source_coefficients = [Q(int(u), int(v)) for u, v in re.findall(r'\((\d+) / (\d+) : ℝ\) \* \(x -', coefficient_text)]
    require('exact translated coefficients equal original theorem SOURCE', shifted == source_coefficients)
    s2 = sum((Q(1, 3) ** (2*k + 1) / (2*k + 1) for k in range(6)), Q(0))
    s3 = sum((Q(1, 2) ** (2*k + 1) / (2*k + 1) for k in range(11)), Q(0))
    tail = Q(1, 2) ** 23 / (1 - Q(1, 2) ** 2)
    slope_constant = Q(301, 100) * Q(101, 201) ** 10
    cap = 3 * Q(1098613, 1000000) - 20 * Q(693147, 1000000) + Q(309, 100000)
    margins = [2 * s2 - Q(693147, 1000000), Q(1098613, 1000000) - 2 * (s3 + tail)]
    require('own exact log partial sums and remainder', [str(s2), str(s3), str(tail)] ==
            [arithmetic['log_two_six_term_half_sum'], arithmetic['log_three_eleven_term_half_sum'], arithmetic['log_three_half_remainder']])
    require('own exact positive rational log margins', all(x > 0 for x in margins)
            and [str(x) for x in margins] == arithmetic['log_bounds_exact_positive_margins'])
    require('own exact upper slope constant', str(slope_constant) == arithmetic['actual_slope_constant'] and slope_constant < Q(309, 100000))
    require('own exact stronger cap and margin', cap == Q(-10564011, 1000000) and Q(-2641, 250) - cap == Q(11, 1000000))
    require('no independent Lean conclusion yet', state['Lean_executed'] is False and not (p.OUT / 'independent-audit.json').exists())
    result = dict(verdict='PERSONAL_COMPLETE_PURE_PHASE_PREFLIGHT_PASS; INDEPENDENT_LEAN_PENDING',
                  role='independent Phase auditor; former Parameter author is a distinct artifact',
                  observed_at_utc=datetime.now(timezone.utc).isoformat(), author_report=p.binding(report),
                  author_all_binding_count=25818, author_total_bytes=sum(b['bytes'] for b in checked), differences=0,
                  all_personally_rehashed_author_bindings=checked, preparation_state=p.binding(p.OUT / 'preparation-state.json'),
                  source_contracts=contracts, complete_original_theorems=34, complete_original_definitions=7,
                  seven_raw_Expr_equal_false_preserved=True, complete_definition_isDefEq_and_rfl_author_evidence_checked=True,
                  actual_source_declarations=68, actual_auxiliaries=27, helper_pair_records=14, unique_definition_helpers=8,
                  author_typed_boundaries=15, author_raw_expression_fields=313, author_Std3_lists=243,
                  pure_arithmetic=dict(shifted_gap_coefficients=[str(x) for x in shifted],
                      log_two_half_sum=str(s2), log_three_half_sum=str(s3), log_three_half_remainder=str(tail),
                      log_rational_margins=[str(x) for x in margins], upper_slope_constant=str(slope_constant),
                      certified_cap=str(cap), below_target_margin=str(Q(-2641, 250)-cap)),
                  checks=checks, no_author_objects_copied=True, no_existing_independent_objects=True,
                  Lean_calls_by_this_auditor=0, API_Root_install_scope_or_mission_operations=False,
                  independent_Lean_PASS=False, complete_Z9_A_or_irrationality_PASS=False,
                  required_next_action='Root lane grant then two fresh SOURCE compiles and four independent controls plus runtime')
    p.dump(p.OUT / 'personal-complete-pure-preflight-2026-10-07.json', result)
    print(json.dumps(dict(verdict=result['verdict'], bindings=25818, bytes=result['author_total_bytes'], checks=len(checks),
                          report_sha256=p.sha(p.OUT / 'personal-complete-pure-preflight-2026-10-07.json'), Lean_calls=0)))


if __name__ == '__main__':
    main()

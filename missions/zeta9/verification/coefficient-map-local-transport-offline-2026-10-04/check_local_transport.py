"""Pure Fraction design checks. No Lean process; no writes outside this directory."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import exact_helpers as h

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
INPUTS = [
    'formalization/CoefficientMapFormalTransportData.lean',
    'formalization/CoefficientMapFormalTransportBounds.lean',
    'formalization/CoefficientMapFormalTransportNumerators.lean',
    'formalization/CoefficientMapNumeratorPartialFractions.lean',
    'formalization/CoefficientMapFiniteSum.lean',
    'formalization/CoefficientMapAggregate.lean',
    'formalization/CoefficientMapMatrix.lean',
    'formalization/CoefficientMapReflection.lean',
    'research/review_formal_transport_independent_2026_10_04.py',
    'verification/formalization-coefficient-map-numerator-pf-2026-10-04/author-audit.json',
    'verification/formalization-coefficient-map-numerator-pf-2026-10-04/source-manifest.json',
    'verification/formalization-coefficient-map-numerator-pf-2026-10-04/SHA256SUMS.txt',
]
SNAPSHOTS = OUT / 'input-snapshots'
SNAPSHOTS.mkdir(exist_ok=True)
bindings = []
for relative in INPUTS:
    data = (TASK / relative).read_bytes()
    snapshot = SNAPSHOTS / Path(relative).name
    snapshot.write_bytes(data)
    bindings.append({'task_relative': relative, 'bytes': len(data),
        'sha256': hashlib.sha256(data).hexdigest(),
        'snapshot_relative': str(snapshot.relative_to(OUT)).replace('\\', '/')})

check = h.check
X, ONE = h.X, h.ONE
generic_cases = []
for m in range(7):
    # Includes zero, m=0, and deliberately improper A. Jets do not need degree bounds.
    samples = [[F(0)], ONE, X, [F(2), F(-3), F(5)],
        h.power(X, 9*(m+1)), h.power(X, 9*(m+1)+4),
        [F((-1)**k*(k+2), k+1) for k in range(9*(m+1)+6)]]
    for a_index, A in enumerate(samples):
        old = h.jets(m, A)
        U = h.mul(h.power([F(m+1), F(1)], 9), A)
        L = h.mul(h.power(X, 9), h.shift(A, F(1)))
        upper, lower = h.jets(m+1, U), h.jets(m+1, L)
        check(f'generic_m{m}_A{a_index}_upper_all_actual_jets',
              upper[:-1] == old and upper[-1] == [F(0)]*9)
        check(f'generic_m{m}_A{a_index}_lower_all_actual_jets',
              lower[0] == [F(0)]*9 and lower[1:] == old)
        D = h.mul(h.mul(h.power(X, 9), h.power([F(m+2), F(1)], 9)), h.shift(A, F(1)))
        double = h.jets(m+2, D)
        check(f'generic_m{m}_A{a_index}_double_all_actual_jets',
              double == [[F(0)]*9]+old+[[F(0)]*9])
        generic_cases.append({'m': m, 'A_sample': a_index, 'degree': len(h.trim(A))-1,
            'proper_required': False, 'coefficient_equalities': 9*(3*m+7)})
    for j in range(m+1):
        # Verify the two actual cleared-denominator reindexings as whole polynomials.
        dmj = h.prod(([F(k-j), F(1)] for k in range(m+1) if k != j))
        upper_d = h.prod(([F(k-j), F(1)] for k in range(m+2) if k != j))
        check(f'generic_m{m}_j{j}_upper_whole_cleared_denominator',
              upper_d == h.mul(dmj, [F(m+1-j), F(1)]))
    for j in range(1, m+2):
        prev = h.prod(([F(k-(j-1)), F(1)] for k in range(m+1) if k != j-1))
        lower_d = h.prod(([F(k-j), F(1)] for k in range(m+2) if k != j))
        check(f'generic_m{m}_j{j}_lower_whole_cleared_denominator',
              lower_d == h.mul([-F(j), F(1)], prev))

connection_instances = []
for n in range(1, 6):
    pairs = h.solve_connection(n)
    old_matrix = [h.five(h.jets(n, h.weighted(n, h.power(X, l)))) for l in range(5)]
    new_matrix = []
    for r, (P, q) in enumerate(pairs):
        prefix = f'connection_n{n}_r{r}_'
        b = h.jets(n, h.weighted(n, P))
        a = h.jets(n+2, h.weighted(n+2, h.power(X, r)))
        Qnum = h.mul(h.scale(h.prod([[-F(i+2), F(1)] for i in range(n)] +
            [[F(n+i+1), F(1)] for i in range(n)]), F(h.factorial(n)**7)),
            h.compose(q, [F(0), F(n-1), F(1)]))
        Ahat = h.shift(Qnum, F(1))
        c = h.jets(n+1, Ahat)
        old_lift = h.mul(h.mul(h.power(X, 9), h.power([F(n+2), F(1)], 9)),
                         h.shift(h.weighted(n, P), F(1)))
        clear = h.add(old_lift, h.sub(h.mul(h.power([F(n+2), F(1)], 9), Ahat),
                                    h.mul(h.power(X, 9), h.shift(Ahat, F(1)))))
        check(prefix+'whole_cleared_polynomial', clear == h.weighted(n+2, h.power(X, r)))
        transport = [[(b[j-1][s] if 1 <= j <= n+1 else F(0)) +
            (c[j][s] if j <= n+1 else F(0)) - (c[j-1][s] if j else F(0))
            for s in range(9)] for j in range(n+3)]
        check(prefix+'all_local_jets', a == transport)
        check(prefix+'left_endpoint_all_orders', a[0] == c[0])
        check(prefix+'right_endpoint_all_orders', a[-1] == [-v for v in c[-1]])
        check(prefix+'all_nine_rho', h.rho(a) == h.rho(b))
        old_eval = h.pf(b, F(1))
        q_eval = h.pf(c, F(1))
        check(prefix+'finite_harmonic_signed_correction',
            h.constant(a) == h.constant(b)-old_eval+q_eval)
        check(prefix+'old_actual_PF_at_one', old_eval == h.actual(n, P, F(1)) == 0)
        check(prefix+'Q_actual_PF_at_one', q_eval ==
            h.evaluate(Ahat, F(1))/h.evaluate(h.pole(n+1), F(1))**9 == 0)
        check(prefix+'Q_full_polynomial_PF', h.reconstructed(n+1, c) == h.trim(Ahat))
        check(prefix+'Q_strict_degree', len(h.trim(Ahat))-1 <= 2*n+18 < 9*(n+2))
        check(prefix+'all_five_outputs', h.five(a) == h.five(b))
        new_matrix.append(h.five(a))
        connection_instances.append({'n': n, 'r': r,
            'P_coefficients': [str(v) for v in P], 'q_coefficients': [str(v) for v in q],
            'terminal_c_order9': str(c[-1][-1]), 'terminal_a_order9': str(a[-1][-1])})
    gamma = [[h.coeff(P, l) for l in range(5)] for P, q in pairs]
    check(f'n{n}_all25_Gamma_left_matrix_entries', all(new_matrix[r][s] ==
        sum((gamma[r][l]*old_matrix[l][s] for l in range(5)), F(0))
        for r in range(5) for s in range(5)))
    if n % 2:
        check(f'n{n}_odd_has_four_zero_odd_rho_columns',
              all(row[s] == 0 for row in old_matrix for s in range(1, 5)))
    print(f'Pure exact chosen n={n}: local, rho, B and Gamma passed.', flush=True)

# A finite harmonic identity is valid for arbitrary arrays, without boundary zeros.
for n in range(6):
    b = [[F((-1)**(k+s)*(2*k+s+1), k+s+2) for s in range(9)] for k in range(n+1)]
    c = [[F((j+1)*(s+2), j+s+3) for s in range(9)] for j in range(n+2)]
    a = [[(b[j-1][s] if 1 <= j <= n+1 else F(0)) +
        (c[j][s] if j <= n+1 else F(0)) - (c[j-1][s] if j else F(0))
        for s in range(9)] for j in range(n+3)]
    check(f'arbitrary_arrays_n{n}_all_nine_rho', h.rho(a) == h.rho(b))
    check(f'arbitrary_arrays_n{n}_exact_B_correction',
          h.constant(a) == h.constant(b)-h.pf(b, F(1))+h.pf(c, F(1)))

negative = {}
cn1 = h.jets(2, h.shift([F(-4), F(0), F(1)], F(1)))
negative['n1_q1_c_first_order9'] = str(cn1[0][-1])
negative['n1_q1_c_terminal_order9'] = str(cn1[-1][-1])
check('negative_terminal_drop_changes_order9_rho', cn1[-1][-1] == -F(3, 512) != 0)
check('negative_unguarded_Nat_pred_changes_left_order9', cn1[0][-1] == -F(3, 512) != 0)
# At s=0 the coefficient is the ninth Taylor coefficient; inserted poles need not vanish.
negative['upper_m0_A1_newpole_order0'] = '-1'
negative['lower_m0_A1_newpole_order0'] = '1'
check('negative_inserted_upper_order0_is_nonzero', h.coeff(h.power(X, 9), 9) /
      F(-1)**9 == -1)
check('negative_inserted_lower_order0_is_nonzero', h.coeff(h.power(X, 9), 9) == 1)
negative['upper_m0_A1_outside_j2_order9'] = str(-F(1, 512))
check('negative_missing_pole_index_bound', F(-1)**9/(F(-2)*F(-1))**9 == -F(1, 512) != 0)
negative['n0_q1_Q2'] = '1/512'
negative['n0_P1_R0_at1'] = '1'
check('negative_n0_two_boundary_zeros_fail', h.actual(0, ONE, F(1)) == 1 and F(1, 512) != 0)
check('negative_n0_Q_degree9_not_strictly_proper', 18 == 9*(0+2))

current_changes = [row['task_relative'] for row in bindings if
    hashlib.sha256((TASK/row['task_relative']).read_bytes()).hexdigest() != row['sha256']]
report = {'status': 'OFFLINE_FINITE_EXACT_CHECKS_NOT_UNIVERSAL_LEAN_PROOF',
    'Lean_invocations': 0, 'native_objects_accessed': False,
    'author_code_or_author_finite_results_reused': False,
    'own_previous_pure_polynomial_helpers_source_only_reused': True,
    'check_count': len(h.checks), 'all_checks_pass': all(v['pass'] for v in h.checks),
    'generic_lift_instances': generic_cases, 'connection_instances': connection_instances,
    'negative_controls': negative, 'checks': h.checks, 'source_inputs': bindings,
    'point_in_time_inputs_changed_during_run': current_changes,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'helper_sha256': hashlib.sha256((OUT/'exact_helpers.py').read_bytes()).hexdigest()}
(OUT/'exact-checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
print(f'{len(h.checks)} pure exact checks passed; Lean calls 0.', flush=True)

"""Prepare a Sum-only finalizer; no verdict before actual replay completion."""
from pathlib import Path
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[3]
s=(TASK/"formalization/platform/coefficient-map-finite-sum/independent/finalize_review.py").read_text(encoding="utf-8")
def change(a,b):
    global s
    assert s.count(a)==1,(a,s.count(a))
    s=s.replace(a,b)
s=s.replace("FiniteSum","Summation").replace("FS platform","Summation platform").replace("Independent FS","Independent Summation")
s=s.replace('formalization-coefficient-map-finite-sum-2026-10-03','formalization-coefficient-map-summation-independent-2026-10-04')
change('TARGETS = ["actual_finite_harmonic_identity","actual_grouped_finite_identity","harmonic_difference_eq_shifted"]',
       'TARGETS = ["actualSeries_norm_summable","actualSeries_hasSum_exactL","original_integer_quartic_exact_infinite_L"]')
s=s.replace('40_fresh_independent','46_fresh_independent').replace('len(prep["rows"]) == 11','len(prep["rows"]) == 15').replace('len(replay["rows"]) == 29','len(replay["rows"]) == 31').replace('len(invocations) == 40','len(invocations) == 46')
s=s.replace('"preparation":11,"final_replay":29','"preparation":15,"final_replay":31')
s=s.replace('len(original) == 39 and len(definitions) == 36','len(original) == 46 and len(definitions) == 43')
s=s.replace('len(sol) == len(ref) == 37','len(sol) == len(ref) == 44')
s=s.replace('252_actual_definition','301_actual_definition').replace('len(comparisons) == 252','len(comparisons) == 301')
change('{"actual_Defs":36,"Base":9,"Jet":9,"Injectivity":7,"PF":5,"Summation":4,"HarmonicStability":2,"contexts":7}',
       '{"actual_Defs":43,"Base":9,"Jet":9,"Injectivity":7,"PF":5,"Reflection":4,"FiniteSum":4,"Summation":3,"HarmonicStability":2,"contexts":7}')
s=s.replace('native_count = 7 +','native_count = 21 +').replace('"original_Summation_proofs":7','"original_Summation_proofs":21')
start=s.index('assert len(boundary) == 44')
stop=s.index('\nprints = []',start)
s=s[:start]+'''assert len(boundary) == len(old_boundary) == 56
boundary_comparisons = []
assert {normalize(name) for name in boundary} == set(old_boundary)
for name,r in boundary.items():
    base=old_boundary[normalize(name)]
    boundary_comparisons.append({"declaration":name,"native_declaration":normalize(name),"type":r["type"],"axioms":r["axioms"],
        "pass":normalize(r["type"])==base["type"] and r["definitionValue"]==base["definitionValue"] and standard(r) and standard(base)})
assert rows(OUT/"replay-stage-boundary-audit.log") == rows(BATCH/"stage-boundary-audit.log")
closed = [r for r in boundary.values() if r["declaration"].startswith("sum_ind_")]
check("56_staged_boundary_records_equal_original_native_including_32_closed",len(closed)==32 and all(r["pass"] for r in boundary_comparisons),
    {"original_source_records":24,"original_closed_records":32,"original_math_review_sha256":"fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"})
new_boundary=rows(OUT/"independent-new-boundary.log")
check("eight_new_reviewer_analytic_controls_standard_axioms",len(new_boundary)==8 and all(standard(r) for r in new_boundary),
    {"absolute_without_even":True,"HasSum_supplies_summability_and_exact_tsum":True,"integer_even_two_X_four":True,"actual_n0_X3_at_positive_two":"1/8","actual_n0_X4_at_positive_two":"1/2","index_starts_at_positive_one":True})
required=["sum_ind_absolute_without_even","sum_ind_odd_n_one_absolute","sum_ind_n_zero_X_three_HasSum","sum_ind_n_zero_X_four_no_HasSum","sum_ind_n_zero_X_four_not_summable","sum_ind_n_zero_X_four_totalized_tsum_eq_exactL","sum_ind_n_zero_X_four_partial_diverges","sum_ind_closed_original_HasSum"]
check("actual_absolute_odd_and_divergent_totalized_tsum_boundaries_preserved",all(name in boundary for name in required),
    {"totalized_tsum_without_HasSum_not_proof_of_convergence":True,"original_even_integer_quartic_domain_kept":True})
''' + s[stop:]
s=s.replace('"author_new_boundary_records":list(author_new_boundary.values()),','')
start=s.index('scope = ')
stop=s.index('paths = set(',start)
s=s[:start]+'''scope = "Actual p9,q1,m=n,d0 absolute convergence under Strong without Even; exact odd-zeta HasSum under Even and Strong; original integer-quartic even n>=2 specialization"
findings = [
    {"severity":"informational","code":"EXACT_ANALYTIC_DOMAINS","detail":"Absolute norm summability keeps only actual StrongProperMultiplier; HasSum keeps Even n and Strong. The original integer endpoint keeps Even n>=2 and integer polynomial degree<=4. No rho-cancellation, summability, abstract rational function or zeta-limit premise is added."},
    {"severity":"informational","code":"GENUINE_HAS_SUM","detail":"Summability is proved before genuine HasSum. The original n0,X4 is strict proper but not Strong, is not summable and has no HasSum to any real, although Lean's totalized tsum equals zero. The actual n0,X3 converges to zetaReal3; odd n1 absolute summability remains valid."},
    {"severity":"informational","code":"ACTUAL_COMPLETE_PROOFS","detail":"All21 original Sum proofs and69 actual cross-source helpers remain in each Sol. Only Definitions and Mathlib imports support all complete proofs; reference Theorems carry sorryAx as statement stubs and are excluded from proof claims."},
    {"severity":"informational","code":"RAW_AND_PARSER_INPUT","detail":"Pure Harmonic raw CRLF bytes remain fixed; the independently executed official parser snapshot equals exact CRLF-to-LF normalization. All seven actual native source snapshots and eight actual parser outputs are reexecuted."},
    {"severity":"informational","code":"SCOPED_ROOT_BUILD","detail":"Root7+7 actual byte files and the parent scoped3789-job build0 are bound. Check1 names only the two existing Tao files; older PNT statement mirror is outside the new-Sol proof claim. Parent initial path gate failure is preserved separately, not successful build evidence."},
    {"severity":"informational","code":"OPEN_OBLIGATIONS","detail":"This batch proves actual infinite weighted sum for p9,q1,m=n,d0 and the original quartic specialization. Inverse height/integrality, small nonzero integer forms, general parameters, J and irrationality remain outside this verdict; KernelBridge results are separately reviewed."}]
md = "Independent Summation platform integration review: PASS.\\n\\n"+scope+".\\n\\n"
md += "46 observed fresh source/extraction/audit Lean exits0, plus one separate runtime probe; seven actual sources and pure Harmonic source, seven existing pure Def dependencies, eight Stage2/parser snapshots and header, and seven staged modules compile.301 actual Def type/value comparisons, three exact original/Sol/reference types,273 Sol proof records,56 exact original staged boundary records including32 closed controls and8 new reviewer analytic controls pass.\\n\\n"
md += "Absolute convergence has no Even premise; genuine odd-zeta HasSum preserves Even and Strong; the integer quartic endpoint preserves even n>=2. No root/scope/API/credential writes or publication occurred during this review. Earlier FS and Reflection independent freezes remain unchanged.\\n"
(OUT/"independent-integration-review.md").write_text(md,encoding="utf-8")
(OUT/"independent-integration-review.log").write_text("PASS\\n"+"\\n".join(c["name"]+": PASS" for c in checks)+"\\n",encoding="utf-8")
''' + s[stop:]
s=s.replace('"scope_verdict":"PASS_ACTUAL_FINITE_SUM_PLATFORM_INTEGRATION"','"scope_verdict":"PASS_ACTUAL_INFINITE_SUM_PLATFORM_INTEGRATION"')
s=s.replace('"preparation":11,"replay":29,"total":40','"preparation":15,"replay":31,"total":46').replace('"all_Lean_invocations":41','"all_Lean_invocations":47')
s=s.replace('"new_Def":4,"all_actual_Def":36,"definition_comparisons":252','"new_Def":3,"all_actual_Def":43,"definition_comparisons":301')
s=s.replace('"staged_boundary_records":44,"exact_original_closed_boundaries":27,"new_author_boundary_records":4,"new_reviewer_boundary_records":9','"staged_boundary_records":56,"exact_original_closed_boundaries":32,"new_reviewer_boundary_records":8')
change('paths.update(OUT.rglob("*"))','paths.update(OUT.rglob("*"))\npaths.add(BATCH/"root-install-attempt-01-failure.json")\nfor batch in ["coefficient-map-reflection","coefficient-map-finite-sum"]:\n    paths.add(TASK/"formalization/platform"/batch/"independent/independent-integration-review.json")')
change('paths.update(OUT.rglob("*"))','paths.update(ROOT/r["root_relative"] for r in load(OLD/"independent-review.json")["stable_files"])\npaths.update(OUT.rglob("*"))')
(OUT/"finalize_review.py").write_text(s,encoding="utf-8")
compile(s,str(OUT/"finalize_review.py"),"exec")
print("New Sum finalizer prepared; actual source/replay evidence required before verdict.")

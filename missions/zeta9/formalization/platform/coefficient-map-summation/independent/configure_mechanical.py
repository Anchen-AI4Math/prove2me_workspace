"""Prepare independently reconstructed Sum graph/parser/source splices."""
from pathlib import Path
import re
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[3]
RECIPE=TASK/"formalization/platform/coefficient-map-finite-sum/independent/mechanical_review.py"
s=RECIPE.read_text(encoding="utf-8")
def change(a,b):
    global s
    assert s.count(a)==1,(a,s.count(a))
    s=s.replace(a,b)
s=s.replace("CoefficientMapFiniteSum","CoefficientMapSummation")
change('TARGETS = ["actual_finite_harmonic_identity", "actual_grouped_finite_identity", "harmonic_difference_eq_shifted"]',
       'TARGETS = ["actualSeries_norm_summable", "actualSeries_hasSum_exactL", "original_integer_quartic_exact_infinite_L"]')
change('DEF_NAMES = ["rho", "constantTerm", "finiteL", "shiftedTail"]','DEF_NAMES = ["zetaReal", "exactL", "actualSeries"]')
s=s.replace('"HarmonicStability"','"Def_ZetaNine_HarmonicStability"')
s=s.replace('HarmonicStability-native','Def_ZetaNine_HarmonicStability-native')
s=s.replace('HarmonicStability-oracle','Def_ZetaNine_HarmonicStability-oracle')
s=s.replace('HarmonicStability-sketch','Def_ZetaNine_HarmonicStability-sketch')
s=s.replace('five_actual_sources_and_five_pure_Defs','seven_actual_sources_and_seven_pure_Defs')
s=s.replace('all_six_actual_Stage2','all_eight_actual_Stage2')
s=s.replace('actual_FiniteSum_parser_header_has_three_actual_imports','actual_Summation_parser_header_has_six_actual_imports')
change('["import missions.zeta9.formalization.CoefficientMapPartialFractions","import Definitions.Def_ZetaNine_HarmonicStability","import Mathlib.Algebra.BigOperators.Intervals"]',
       '["import missions.zeta9.formalization.CoefficientMapReflection","import missions.zeta9.formalization.CoefficientMapFiniteSum"]+["import "+m for m in MATHLIB]')
change('REV = "0df444a360eaa60ab8c11dca51a86af692955474"','REV = "0df444a360eaa60ab8c11dca51a86af692955474"\nMATHLIB = ["Mathlib.NumberTheory.LSeries.RiemannZeta","Mathlib.Analysis.PSeries","Mathlib.Analysis.Normed.Group.InfiniteSum","Mathlib.Analysis.Normed.Module.FiniteDimension"]')
change('for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:',
       'for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions","CoefficientMapReflection","CoefficientMapFiniteSum"]:')
s=s.replace('len(core) == 11','len(core) == 24').replace('"source_defs":4,"source_proofs":7','"source_defs":3,"source_proofs":21')
s=s.replace('four_Def_spans','three_Def_spans').replace('lightweight_four_actual_Def','lightweight_three_actual_Def')
oldline=next(line for line in s.splitlines() if line.startswith('definition = '))
change(oldline,'definition = "import Definitions.Def_ZetaNine_CoefficientMapReflection\\nimport Definitions.Def_ZetaNine_CoefficientMapFiniteSum\\n"+"\\n".join("import "+m for m in MATHLIB)+"\\n\\nset_option autoImplicit false\\nnoncomputable section\\nopen scoped BigOperators\\nopen Finset Polynomial\\n\\nnamespace "+NS+"\\n\\n"')
s=s.replace('len(diagnostics) == 6','len(diagnostics) == 12')
# Wrapper namespace opens and Mathlib imports are fixed literal format; all bodies
# and replacement spans still come from our actual graph/official parser run.
s=s.replace('ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability',
            'ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability')
change('sol = "import Definitions.Def_ZetaNine_CoefficientMapSummation\\nimport Mathlib.Tactic\\nimport Mathlib.Algebra.BigOperators.Intervals\\n\\n"+bridge',
       'sol = "import Definitions.Def_ZetaNine_CoefficientMapSummation\\nimport Mathlib.Tactic\\n"+"\\n".join("import "+m for m in MATHLIB)+"\\n\\nset_option autoImplicit false\\nset_option maxHeartbeats 2000000\\nnoncomputable section\\n"+bridge')
s=s.replace('"original_proofs_per_Sol":7','"original_proofs_per_Sol":21')
oldline=next(line for line in s.splitlines() if line.startswith('check("strict_proper_finite_sums'))
change(oldline,'check("strong_absolute_even_HasSum_and_integer_quartic_domains_in_prose", all(text in nl[i] for i,text in [(0,"No Even n premise"),(0,"stronger degree gap"),(0,"divergent harmonic"),(1,"Let $n$ be even"),(1,"genuine HasSum"),(1,"no HasSum"),(1,"totalized Lean tsum"),(2,"n\\\\ge2"),(2,"degree at most4"),(2,"Integer W is not a claim")]), "Absolute convergence has Strong without Even; actual odd-zeta HasSum keeps Even; integer quartic keeps even n>=2 and degree<=4.")')
s=s.replace('formalization-coefficient-map-finite-sum-2026-10-03','formalization-coefficient-map-summation-independent-2026-10-04')
s=s.replace('a4d2cec35a3e9b506aed7a0df0b2afacce4adf07a5b03f42b713b9726b581386','fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa')
s=s.replace('len(math["checks"]) == 15','len(math["checks"]) == 16')
mathline=next(line for line in s.splitlines() if line.startswith('check("independent_native_mathematical_review_exact_hash'))
change(mathline,mathline+'\ncheck("all_94_prior_native_math_review_bindings_unchanged",len(math["stable_files"])==94 and all(sha(ROOT/r["root_relative"])==r["sha256"] and (ROOT/r["root_relative"]).stat().st_size==r["bytes"] for r in math["stable_files"]),{"prior_cache_only_hash_bound_not_used_as_our_objects":True})')
s=s.replace('seven_installed_root_modules_and_five_existing_Defs','seven_installed_root_modules_and_seven_existing_Defs')
s=s.replace('len(copyplan["required_existing_Definitions"]) == 5','len(copyplan["required_existing_Definitions"]) == 7')
change('["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions","coefficient-map-reflection"]:',
       '["coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions","coefficient-map-reflection","coefficient-map-finite-sum"]:')
s=s.replace('all_687_prior_platform_freeze_members','all_907_prior_platform_freeze_members').replace('old_counts == [96,111,134,174,172]','old_counts == [96,111,134,174,172,220]')
start=s.index('retained = ')
stop=s.index('write(OUT/"mechanical-checks.json"',start)
s=s[:start]+'''failure = load(BATCH/"root-install-attempt-01-failure.json")
check("parent_initial_path_gate_failure_preserved_separate_from_success",failure["actual_exit_code"]==1 and failure["failed_before_copy_or_scope_change"] and not failure["mathematical_or_Lean_failure"] and failure["excluded_from_success_evidence"] and failure["correct_review"]==old_math.relative_to(TASK).as_posix(),{"failure_file":"root-install-attempt-01-failure.json","final_native_review_path_is_correct":True,"failure_not_success_evidence":True})
prior_reviews = {
    "coefficient-map-reflection":"954a72aeed9af3188e62ed16030cdae9212da68d3c1d93eb6b75c2e854d50241",
    "coefficient-map-finite-sum":"dea9dff29978c2576d9a3955bf7aa4a265a70edb60e4b6a9a7f9acd31815df50"}
for batch,h in prior_reviews.items():
    p=TASK/"formalization/platform"/batch/"independent/independent-integration-review.json"
    prior=load(p)
    assert sha(p)==h and prior["verdict"]=="PASS"
    assert all(sha(ROOT/r["root_relative"])==r["sha256"] and (ROOT/r["root_relative"]).stat().st_size==r["bytes"] for r in prior["stable_files"])
check("two_earlier_independent_transplant_freezes_unchanged",True,prior_reviews)
''' + s[stop:]
(OUT/"mechanical_review.py").write_text(s,encoding="utf-8")
compile(s,str(OUT/"mechanical_review.py"),"exec")
print("New Sum mechanical recipe prepared; needs our actual extraction before PASS.")

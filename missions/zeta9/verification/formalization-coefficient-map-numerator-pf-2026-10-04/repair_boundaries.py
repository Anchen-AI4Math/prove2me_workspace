from run import *

s=(OUT/'boundaries.lean').read_text(encoding='utf8')
s=s.replace('(by simp; omega)','(by simp)',1)
s=s.replace('(by intro k hk; have hk0 : k = 0 := by omega; simpa [hk0] using ht)',
            '(by\n      intro k hk\n      have hk0 : k = 0 := by omega\n      simpa only [hk0, Nat.cast_zero, add_zero] using ht)',1)
s=s.replace('Polynomial.X_comp, Polynomial.C_comp] <;> ring',
            'Polynomial.X_comp, Polynomial.C_comp, map_ofNat] <;> ring',1)
prefix='ZetaNine.CoefficientMapNumeratorPartialFractions.'
for original,control in [('actual_numerator_polynomial_partial_fractions','checked_exact_generic_polynomial_endpoint'),
                         ('actual_numerator_global_partial_fractions','checked_exact_generic_regular_point_endpoint'),
                         ('actual_numerator_local_coefficients_injective','checked_exact_generic_actual_jet_injectivity')]:
    s+='  let actual ← getConstInfo `'+prefix+original+'\n'
    s+='  let explicit ← getConstInfo `'+control+'\n'
    s+='  let eq ← isDefEq actual.type explicit.type\n'
    s+='  unless eq do throwError "Exact generic endpoint type mismatch"\n'
    s+='  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),("source",Json.str "'+prefix+original+'"),("control",Json.str "'+control+'"),("whole_type_kernel_equal",toJson eq),("actual_type_repr",Json.str (reprStr actual.type)),("explicit_type_repr",Json.str (reprStr explicit.type))]).compress\n'
write(OUT/'b2.lean',s)
dump(OUT/'boundary-repair-plan.json',{
    'failed_call':'r08','failed_source_preserved':sha(OUT/'boundaries.lean'),
    'Lean_exit':1,'failed_records_including_sorryAx_all_excluded':True,
    'failure_log_display_Python_exit':1,'failure_display_diagnostic':'GBK stdout failed to print U+211A after actual Lean1 had already been saved',
    'replacement_source':'b2.lean','replacement_sha256':sha(OUT/'b2.lean'),
    'core_Data_and_PF_sources_not_modified':True,
    'repairs':['remove redundant omega after closing simp','multiline regular-point index proof avoiding nested by semicolon','map_ofNat before polynomial ring normalization'],
    'extra_actual_generic_endpoint_type_kernel_comparisons':3})
sys.exit(run('actual own repaired boundaries and three exact endpoint kernel types',OUT/'b2.lean'))

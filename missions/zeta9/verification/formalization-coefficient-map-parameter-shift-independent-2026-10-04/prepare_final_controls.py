"""Prepare explicit actual-kernel type comparison and own-cache resolution; no Lean."""
from run import *
verify()
names=['positiveProduct_add_two','positiveProduct_parameter_shift','negativeProduct_add_two_sub_one',
 'negativeProduct_parameter_shift','poleProduct_parameter_shift','factorial_parameter_shift','connectionZ_eval_factors',
 'numerator_parameter_shift','connectionD_eval_factors','shifted_regular_conditions','actual_R_parameter_shift',
 'connectionRemainder_successor','connectionRemainder_difference','actual_original_connection_transport','five_actual_connection_transports_exist_unique']
code='import "expected-types"\n'
# Hyphenated filenames cannot be imported as ordinary canonical modules. Inline the
# independent closed type program byte-for-byte, then compare the real types.
code=(PROJECT/'expected-types.lean').read_text(encoding='utf-8')+'\n'
code+='run_meta do\n  for (sourceName, expectedName) in ['+','.join('(`ZetaNine.CoefficientMapParameterShift.'+n+', `IndependentParameterShiftExpected.expected_'+n+')' for n in names)+'] do\n'
code+='''    let actual ← getConstInfo sourceName
    let expected ← getConstInfo expectedName
    let eq ← isDefEq actual.type expected.type
    unless eq do throwError "Original and independent explicit type differ: {sourceName}"
    IO.println (Json.mkObj [("kind",Json.str "actual_whole_type_kernel_comparison"),
      ("source",Json.str sourceName.toString),("expected",Json.str expectedName.toString),
      ("type_kernel_equal",toJson eq),("actual_type_full_expr",Json.str (reprStr actual.type)),
      ("expected_type_full_expr",Json.str (reprStr expected.type))]).compress)
'''
write(OUT/'kernel-types.lean',code);write(PROJECT/'kernel-types.lean',code)
resolver='import Lean\nopen Lean\ndef main : IO Unit := do\n  let path ← IO.getEnv "LEAN_PATH"\n  IO.println ((Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress)\n  for m in (['+','.join(json.dumps(m) for m in ORDER)+'] : List String) do\n    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)\n    IO.println ((Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m),("resolved_olean",Json.str p.toString)]).compress)\n'
write(OUT/'resolver.lean',resolver);write(PROJECT/'resolver.lean',resolver)
dump(OUT/'final-controls-preparation.json',{'status':'PREPARED_NOT_EXECUTED','source_frozen_sha256':SOURCE_SHA,
 'kernel_exact_type_comparisons_prepared':15,'whole_value_rfl_controls':2,'own_boundary_controls_prepared':27,
 'resolver_modules_prepared':14,'expected_program_inlined_exactly_in_kernel_replay':True,
 'files':[{'name':n,'sha256':sha(OUT/n),'bytes':(OUT/n).stat().st_size} for n in ['kernel-types.lean','resolver.lean']]})
print('Pure final controls ready:15 true kernel types,14 actual module resolutions; zero Lean',flush=True)

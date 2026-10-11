"""Keep complete helper types/axiom closures without exporting irrelevant huge proof trees."""
import inspect_prepare as p
from prepare_controls import save
old=p.load(p.OUT/'control-preparation.json');path=p.PROJECT/old['semantic']['project_relative']
text=path.read_text(encoding='utf-8')
helper='''private def helperProof (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  let value ← match info with
    | .thmInfo actual => pure actual.value
    | .defnInfo actual => pure actual.value
    | .opaqueInfo actual => pure actual.value
    | _ => throwError "Expected actual proof helper"
  closed name info.type value
  let axioms ← standard name
  let payload ← ofExcept (persistedRoundTrip info.type info.type)
  let (first,second) ← ofExcept (decode payload)
  let same ← isDefEq info.type first
  unless same && Expr.equal info.type first && Expr.equal info.type second do throwError "Full helper type reconstruction failed"
  IO.println (Json.mkObj [("kind",Json.str "independent_generated_helper_proof_type"),
    ("declaration",Json.str name.toString),("closed_type_and_actual_proof",toJson true),
    ("axioms",toJson (axioms.toList.map Name.toString)),("complete_type_expression_dag",payload),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),("all_fields_Expr_equal_roundtrip",toJson true),
    ("whole_type_roundtrip_kernel_equal",toJson same)]).compress
'''
assert text.count('private def internalHelpers')==1
text=text.replace('private def internalHelpers',helper+'private def internalHelpers')
needle='      full name "independent_generated_or_internal_helper"'
assert text.count(needle)==1
text=text.replace(needle,'      if ← isProp info.type then\n        helperProof name\n      else\n        full name "independent_generated_or_internal_definition"')
row=save('OutputsIndependentSemanticV2',text)
new=dict(old);new['semantic']=row
new.update(original_unattempted_semantic_V1=old['semantic'],unattempted_V1_preserved=True,
    helper_proofs='Full closed type lossless roundtrip plus actual proof closure and Std3; huge raw helper proof values are not exported',
    helper_definitions='Full type and value lossless roundtrip, including metadata and generated matcher names')
p.dump(p.OUT/'control-preparation-v2.json',new)
print('V2 preserves all assertions; full helper types, actual closed proof/Std3 and full matcher definition values retained.')

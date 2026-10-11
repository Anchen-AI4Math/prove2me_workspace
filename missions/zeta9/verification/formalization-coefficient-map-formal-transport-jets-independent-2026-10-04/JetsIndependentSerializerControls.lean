import IndependentExprDagV3
import Lean
open Lean Meta IndependentLosslessExprDagV1
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

-- Fresh source-only serializer checks. Synthetic Exprs are serialization fixtures,
-- not mathematical declarations and do not count as theorem proofs.
run_meta do
  let numeric := Name.num Name.anonymous 7
  let textual := Name.str Name.anonymous "7"
  let nt := Expr.const `Nat []
  let pairs : List (Expr × Expr) := [
    (.const numeric [], .const textual []),
    (.letE `x nt (.lit (.natVal 1)) (.bvar 0) true,
      .letE `x nt (.lit (.natVal 1)) (.bvar 0) false),
    (.lam `x nt (.bvar 0) .implicit, .lam `x nt (.bvar 0) .strictImplicit),
    (.mdata ⟨[(`audit,.ofNat 0)]⟩ nt, .mdata ⟨[(`audit,.ofNat 1)]⟩ nt)]
  let mut count := 0
  for (a, b) in pairs do
    unless reprStr a != reprStr b do throwError "Fixture did not distinguish its relevant field"
    let payload ← ofExcept (persistedRoundTrip a b)
    let (ra, rb) ← ofExcept (decode payload)
    unless reprStr a == reprStr ra && reprStr b == reprStr rb do
      throwError "Serializer discarded a constructor field"
    IO.println (Json.mkObj [("kind",Json.str "independent_serializer_distinct_fields"),
      ("index",toJson count),("raw_fields_preserved",toJson true),("payload",payload)]).compress
    count := count + 1
  let badReference := Json.mkObj [("format",Json.str "lean-expr-dag-v1"),
    ("type_root",toJson (0 : Nat)),("value_root",toJson (0 : Nat)),
    ("nodes",Json.arr #[Json.arr #[Json.str "app",toJson (0 : Nat),toJson (0 : Nat)]])]
  match decode badReference with
  | .ok _ => throwError "Non-topological self-reference accepted"
  | .error message =>
    IO.println (Json.mkObj [("kind",Json.str "independent_serializer_bad_reference_rejected"),
      ("actual_decoder_message",Json.str message),("rejected",toJson true)]).compress
  let unknownConstructor := Json.mkObj [("format",Json.str "lean-expr-dag-v1"),
    ("type_root",toJson (0 : Nat)),("value_root",toJson (0 : Nat)),
    ("nodes",Json.arr #[Json.arr #[Json.str "unknown-constructor"]])]
  match decode unknownConstructor with
  | .ok _ => throwError "Unknown expression constructor accepted"
  | .error message =>
    IO.println (Json.mkObj [("kind",Json.str "independent_serializer_unknown_constructor_rejected"),
      ("actual_decoder_message",Json.str message),("rejected",toJson true)]).compress

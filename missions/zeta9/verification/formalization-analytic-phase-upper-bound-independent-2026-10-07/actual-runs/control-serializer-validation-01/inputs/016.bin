import APIPhaseExprDagV1
import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean.Util.CollectAxioms
open Lean Meta
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000


open IndependentLosslessExprDagV1
run_meta do
  let stdout ← IO.getStdout
  stdout.putStrLn "PHASE DAG validation started"
  stdout.flush
  let nm := Name.str (.num .anonymous 7) "7"
  let sub : Substring.Raw := ⟨"alpha beta", ⟨1⟩, ⟨5⟩⟩
  let si : SourceInfo := .original sub ⟨2⟩ sub ⟨9⟩
  let synt := Syntax.node si nm #[.missing,
    .atom (.synthetic ⟨1⟩ ⟨2⟩ true) "token",
    .ident .none sub nm [.namespace `Alpha, .decl nm ["f","g"]]]
  let md : MData := ⟨[(`str,.ofString "value"),(`bool,.ofBool true),
    (`name,.ofName nm),(`nat,.ofNat 271),(`int,.ofInt (-19)),(`syntax,.ofSyntax synt)]⟩
  let nt := Expr.const `Nat []
  let sampleLevel := Level.imax (.max (.param nm) (.succ .zero)) (.mvar ⟨nm⟩)
  let fixtures : Array Expr := #[.bvar 3,.fvar ⟨nm⟩,.mvar ⟨nm⟩,
    .sort sampleLevel,.const nm [.zero,.succ .zero,.max .zero .zero,.imax .zero .zero,.param nm,.mvar ⟨nm⟩],
    .app nt nt,.lam `x nt (.bvar 0) .default,.lam `x nt (.bvar 0) .implicit,
    .lam `y nt (.bvar 0) .strictImplicit,.lam `y nt (.bvar 0) .instImplicit,
    .forallE `x nt (.bvar 0) .implicit,.letE `x nt nt (.bvar 0) false,
    .letE `x nt nt (.bvar 0) true,.lit (.natVal 314),.lit (.strVal "literal"),
    .mdata md (.app nt nt),.proj nm 2 nt,
    .app (.lam `x nt (.bvar 0) .implicit) (.lam `y nt (.bvar 0) .default),
    .app (.mdata md nt) (.mdata ⟨[(`nat,.ofNat 99)]⟩ nt),
    .app (.letE `x nt nt (.bvar 0) true) (.letE `x nt nt (.bvar 0) false)]
  for i in [:fixtures.size] do
    let e := fixtures[i]!
    let payload ← ofExcept (persistedRoundTrip e e)
    let (rt,rv) ← ofExcept (decode payload)
    unless reprStr e == reprStr rt && reprStr e == reprStr rv do
      throwError "Fixture raw-tree reconstruction mismatch {i}"
    IO.println (Json.mkObj [("kind",tag "expr_dag_validation"),("fixture_index",toJson i),
      ("all_fields_roundtrip",toJson true),("raw_repr_reconstruction_equal",toJson true),
      ("original_raw_repr",tag (reprStr e)),("payload",payload)]).compress
    stdout.flush
  for wanted in ["ZetaNine.AnalyticPhase.phaseRatio",
      "ZetaNine.AnalyticPhase.phaseSlope","ZetaNine.AnalyticPhase.smoothPhaseRatio"] do
    let found := (← getEnv).constants.toList.filter fun (n,_) => n.toString==wanted
    unless found.length==1 do throwError "Small source declaration not unique"
    let (n,ci) := found.head!
    let some value := ci.value? (allowOpaque:=true) | throwError "Missing source value"
    let payload ← ofExcept (persistedRoundTrip ci.type value)
    let (rt,rv) ← ofExcept (decode payload)
    unless reprStr ci.type == reprStr rt && reprStr value == reprStr rv do
      throwError "Original raw-tree format differs after DAG reconstruction"
    let axioms ← collectAxioms n
    unless axioms.toList.all (fun a => [`propext,`Classical.choice,`Quot.sound].contains a) do
      throwError "Nonstandard small source validation axiom"
    IO.println (Json.mkObj [("kind",tag "expr_dag_small_source_validation"),("source_name",tag wanted),
      ("all_fields_roundtrip",toJson true),("raw_repr_reconstruction_equal",toJson true),
      ("original_type_raw_repr",tag (reprStr ci.type)),("original_value_raw_repr",tag (reprStr value)),
      ("axioms",toJson (axioms.toList.map Name.toString)),("payload",payload)]).compress
    stdout.flush

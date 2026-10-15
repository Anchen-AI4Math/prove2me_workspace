import Submission.ThreeSum.CompleteCostBridge

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false
set_option maxRecDepth 10000

private partial def normalizeThreeSumUploadType (names : Std.HashMap Name Name) (expr : Expr) : Expr :=
  match expr with
  | .const name levels => .const ((names.get? name).getD name) levels
  | .app f a => .app (normalizeThreeSumUploadType names f) (normalizeThreeSumUploadType names a)
  | .lam _ type body info => .lam .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .forallE _ type body info => .forallE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .letE _ type value body nondep => .letE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names value) (normalizeThreeSumUploadType names body) nondep
  | .mdata _ value => normalizeThreeSumUploadType names value
  | .proj name index value => .proj ((names.get? name).getD name) index (normalizeThreeSumUploadType names value)
  | other => other


private def requiredString (item : Json) (key : String) : MetaM String :=
  ofExcept (item.getObjValAs? String key)

-- Lean.ToExpr encodes quoted Names with mkStr1..8 or str/num. Decode only
-- these constructors, then apply the exact existing relocation dictionary.
-- This is confined to auditing Syntax-valued compiler defaults, never types.
private partial def quotedName? (e : Expr) : Option Name := do
  let head ← e.getAppFn.constName?
  let args := e.getAppArgs
  if head == ``Lean.Name.anonymous && args.isEmpty then return .anonymous
  if head == ``Lean.Name.str && args.size == 2 then
    let parent ← quotedName? args[0]!
    let .lit (.strVal value) := args[1]! | none
    return .str parent value
  if head == ``Lean.Name.num && args.size == 2 then
    let parent ← quotedName? args[0]!
    let .lit (.natVal value) := args[1]! | none
    return .num parent value
  let heads := #[``Lean.Name.mkStr1, ``Lean.Name.mkStr2, ``Lean.Name.mkStr3,
    ``Lean.Name.mkStr4, ``Lean.Name.mkStr5, ``Lean.Name.mkStr6, ``Lean.Name.mkStr7, ``Lean.Name.mkStr8]
  let some index := heads.findIdx? (fun n => n == head) | none
  unless args.size == index+1 do none
  let mut result := Name.anonymous
  for arg in args do
    let .lit (.strVal value) := arg | none
    result := .str result value
  return result

private partial def normalizeQuotedNames (names : Std.HashMap Name Name) (e : Expr) : Expr :=
  if let some name := quotedName? e then toExpr ((names.get? name).getD name)
  else match e with
    | .app f a => .app (normalizeQuotedNames names f) (normalizeQuotedNames names a)
    | .mdata _ value => normalizeQuotedNames names value
    | other => other

private def companionRecords (names : Std.HashMap Name Name) (label owner : Name)
    (ci : ConstantInfo) (localConstants : Array ConstantInfo) : MetaM (Array Json) := do
  let mut records := #[]
  for name in ci.type.getUsedConstants do
    let .str parent leaf := name | continue
    unless leaf.startsWith "_auto_" do continue
    unless parent == owner do throwError "Unexpected external auto companion {name} in {owner}"
    let generated ← match localConstants.find? (fun c => c.name == name) with
      | some value => pure value
      | none => getConstInfo name
    let .defnInfo info := generated | throwError "Expected a transparent auto-argument definition: {name}"
    unless info.type == mkConst ``Lean.Syntax do throwError "Unexpected auto companion type: {name}"
    let levels := info.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let norm := fun expr => normalizeThreeSumUploadType names (expr.instantiateLevelParams info.levelParams levels)
    records := records.push <| Json.mkObj [
      ("original",toJson (Name.str label leaf).toString),("name",toJson name.toString),
      ("universeCount",toJson info.levelParams.length),
      ("normalizedType",toJson (reprStr (norm info.type))),
      ("normalizedValue",toJson (reprStr (normalizeQuotedNames names (norm info.value))))]
  return records

run_meta do
  let inverseRaw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-auto-early-base-inverse.json"
  let inverse ← ofExcept (Json.parse inverseRaw >>= Json.getObj?)
  let mut names : Std.HashMap Name Name := {}
  for (new,old) in inverse.toArray do
    let old ← ofExcept old.getStr?
    names := names.insert new.toName old.toName
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-auto-early-inputs.json"
  let items ← ofExcept (Json.parse raw >>= Json.getArr?)
  let mut records := #[]
  let mut retainedRegions : Array CompactedRegion := #[]
  for item in items do
    let original := (← requiredString item "original").toName
    if true then
      let ci ← getConstInfo original
      records := records ++ (← companionRecords {} original original ci #[])
    else
      let stub := (← requiredString item "stub").toName
      let stubCI ← getConstInfo stub
      records := records ++ (← companionRecords names original stub stubCI #[])
      let path ← requiredString item "path"
      let (data,region) ← readModuleData path
      retainedRegions := retainedRegions.push region
      let some ci := data.constants.find? (fun c => c.name == `solution) | throwError "No solution CI"
      let implementation := (← requiredString item "implementation").toName
      records := records ++ (← companionRecords names original implementation ci data.constants)
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-auto-early-native.json" (Json.arr records).pretty
  logInfo s!"Recorded {records.size} source-free auto companions"

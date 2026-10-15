/- Pure future-provider probe specification. No Lean invocation has validated this file yet. -/
namespace LiteralAnalyticInterfaceOwnedInventory
open Lean Meta PiExponentStructuralKernelSnapshot

def exportInventory (anchor : Name) (moduleName output : String) : MetaM Unit := do
  let env ← getEnv
  let some wantedIndex := env.getModuleIdxFor? anchor
    | throwError "Interface data anchor does not have an imported provider owner"
  unless env.header.moduleNames[wantedIndex.toNat]?.map Name.toString == some moduleName do
    throwError "Interface data anchor imported owner differs from the exact provider"
  -- Every constant is enumerated. Only the owner index is inspected before
  -- filtering; name strings and expressions are exported only for matches.
  let mut found : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    if env.getModuleIdxFor? name == some wantedIndex then
      found := found.push (name, ci)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name, ci) in found do
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | _ => none
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("owner",toJson moduleName),
      ("ownerModuleIndex",toJson wantedIndex.toNat),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (envKind ci)),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (isClosed ci.type)),("closedValue",toJson (value.map isClosed)),
      ("isProp",toJson (← isProp ci.type)),("type",exprJson ci.type),
      ("value",value.map exprJson |>.getD Json.null),
      ("typeRefs",toJson ((uniqueSortedNames (exprNames ci.type)).map Name.toString)),
      ("valueRefs",toJson ((uniqueSortedNames (value.map exprNames |>.getD [])).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).toList.map Name.toString
        |>.mergeSort (fun a b => compare a b == .lt)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("providerModule",toJson moduleName),
    ("anchor",toJson anchor.toString),("providerModuleIndex",toJson wantedIndex.toNat),
    ("inventorySelection",toJson "all constants, exact imported owner index before name conversion"),
    ("rawOwnedCIs",Json.arr rows)]).compress

end LiteralAnalyticInterfaceOwnedInventory

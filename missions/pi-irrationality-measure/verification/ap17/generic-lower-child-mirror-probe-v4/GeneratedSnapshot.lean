import Lean
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound

open Lean Meta

namespace PiExponentInterfaceSnapshot

partial def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]

def binderTag : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

-- Keep binder information, constant names, universe levels and de Bruijn
-- indices. Binder display names and source metadata have no kernel meaning.
partial def exprJson : Expr → Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar n => Json.arr #[toJson "fvar", toJson n.name.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
  | .sort u => Json.arr #[toJson "sort", levelJson u]
  | .const n us => Json.arr #[toJson "const", toJson n.toString,
      Json.arr (us.map levelJson).toArray]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (binderTag bi), exprJson t, exprJson b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (binderTag bi), exprJson t, exprJson b]
  | .letE _ t v b nondep => Json.arr #[toJson "let", exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "natLiteral", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "stringLiteral", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson e]

def exportSnapshot (names : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing interface declaration: {name}"
    if ci.type.hasMVar || ci.type.hasFVar then
      throwError "The exported declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo _ => none
      | _ => none
    let typeText ← ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("prettyType", toJson typeText.pretty)]
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentInterfaceSnapshot

open Lean Meta

namespace FullRowMinorProofSnapshot

def refs (e : Expr) : Array Name :=
  (e.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def ownerOf (env : Environment) (name : Name) : MetaM Json := do
  match env.getModuleIdxFor? name with
  | none => pure <| Json.mkObj [("kind", toJson "OwnModule"),
      ("moduleIndex", Json.null), ("module", toJson env.mainModule.toString)]
  | some i =>
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid owner: {name}"
    pure <| Json.mkObj [("kind", toJson "ImportedModule"),
      ("moduleIndex", toJson i.toNat), ("module", toJson owner.toString)]

def ownerModule (env : Environment) (name : Name) : MetaM String := do
  match env.getModuleIdxFor? name with
  | none => pure env.mainModule.toString
  | some i =>
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid owner: {name}"
    pure owner.toString

def ciRow (name : Name) (helper : Bool) : MetaM (List (String × Json)) := do
  let env ← getEnv
  let some ci := env.find? name | throwError "Missing actual CI: {name}"
  let some value := valueOf ci | throwError "No proof value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
     value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Actual CI is not closed: {name}"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Actual proof CI has axioms outside Std3: {name}"
  let allUsedConstants := refs (mkApp ci.type value)
  let owner ← ownerOf env name
  let common := [
    ("name", toJson name.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("allUsedConstants", toJson (allUsedConstants.map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner)]
  pure <| if helper then
    common ++ [("type", PiExponentInterfaceSnapshot.exprJson ci.type)] else common

def exportEvidence (side output name importModule : String) : MetaM Unit := do
  let env ← getEnv
  let declName := name.toName
  unless (← ownerModule env declName) == importModule do
    throwError "Theorem is not from expected actual imported OLean: {declName}"
  let some ci := env.find? declName | throwError "Missing actual theorem: {declName}"
  let some value := valueOf ci | throwError "Missing actual theorem proof: {declName}"
  let mut pending := (refs value).toList
  let mut seen : Array Name := #[declName]
  let mut helpers : Array Name := #[]
  -- Discover helpers by actual module ownership, including genuine private CI;
  -- never manufacture names from a presumed _proof_ numbering convention.
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n then
      seen := seen.push n
      if (← ownerModule env n) == importModule then
        helpers := helpers.push n
        let some helperCI := env.find? n | throwError "Missing actual helper: {n}"
        let some helperValue := valueOf helperCI | throwError "Actual helper lacks value: {n}"
        pending := pending ++ (refs helperValue).toList
  helpers := helpers.qsort (fun a b => a.toString < b.toString)
  let helperRows ← helpers.mapM (fun n => do pure <| Json.mkObj (← ciRow n true))
  let theoremRow ← ciRow declName false
  let report := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("importModule", toJson importModule),
    ("theorem", Json.mkObj (theoremRow ++ [("automaticInlineHelpers", Json.arr helperRows)]))]
  IO.FS.writeFile output report.compress

end FullRowMinorProofSnapshot


namespace SelectedMinorProofSnapshot
open Lean Meta FullRowMinorProofSnapshot
def exportBundle (side output : String) (roots : Array Name) (owners boundary : Array String) : MetaM Unit := do
  let env ← getEnv
  let mut pending := roots.toList
  let mut seen : Array Name := #[]
  let mut found : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n && !boundary.contains n.toString then
      seen := seen.push n
      if owners.contains (← ownerModule env n) then
        found := found.push n
        let some ci := env.find? n | throwError "Missing actual proof CI: {n}"
        let some value := valueOf ci | throwError "Missing actual proof value: {n}"
        pending := pending ++ (refs (mkApp ci.type value)).toList
  for root in roots do
    unless found.contains root do throwError "Actual proof root was not exported: {root}"
  found := found.qsort (fun a b => a.toString < b.toString)
  let rows ← found.mapM (fun n => do pure <| Json.mkObj (← ciRow n true))
  IO.FS.writeFile output (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("side",toJson side),
    ("probeMainModule",toJson env.mainModule.toString),
    ("rootNames",toJson (roots.map Name.toString)),
    ("boundaryNames",toJson boundary),("rows",Json.arr rows)] |>.compress)
end SelectedMinorProofSnapshot


namespace PiExponentEquationProvenanceProbe
open Lean Meta

def ownership (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("index", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Equation probe type is not closed: {name}"
  let value := match ci with
    | .defnInfo d => some d.value
    | _ => none
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Equation probe definition value is not closed: {name}"
  let kind ← match ci with
    | .defnInfo _ => pure "def"
    | .thmInfo _ => pure "theorem"
    | _ => throwError "Equation probe found unsupported constant kind: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Equation probe nonstandard axiom: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("userName", toJson (privateToUserName name).toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("kind", toJson kind),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("owner", ownership (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def exportEquationSnapshot (primary : Name) (expectedModule output side : String) : MetaM Unit := do
  let envBefore ← getEnv
  let ci ← getConstInfo primary
  match ci with
  | .defnInfo _ => pure ()
  | _ => throwError "Primary source binding is not a definition"
  let some idx := envBefore.getModuleIdxFor? primary
    | throwError "Primary must belong to the imported source/provider module"
  unless envBefore.header.moduleNames[idx.toNat]?.map Name.toString == some expectedModule do
    throwError "Primary binding belongs to an unexpected module"
  let equations? ← Lean.Meta.getEqnsFor? primary
  let unfolding? ← Lean.Meta.getUnfoldEqnFor? primary
  let mut equations : Array Json := #[]
  for name in equations?.getD #[] do
    let parent? ← Lean.Meta.isEqnThm? name
    unless parent? == some primary do
      throwError "getEqnsFor? result lacks its exact inverse primary relation: {name}"
    equations := equations.push <| Json.mkObj [
      ("getter", toJson "Lean.Meta.getEqnsFor?"),
      ("inversePrimary", toJson (parent?.map Name.toString)),
      ("CI", ← checkedCI name)]
  let unfolding ← match unfolding? with
    | some name => pure <| Json.mkObj [
        ("getter", toJson "Lean.Meta.getUnfoldEqnFor?"), ("CI", ← checkedCI name)]
    | none => pure Json.null
  let result := Json.mkObj [
    ("side", toJson side), ("expectedModule", toJson expectedModule),
    ("primaryBinding", ← checkedCI primary),
    ("getEqnsForReturnedSome", toJson equations?.isSome),
    ("actualEquationNames", toJson (equations?.map (·.map Name.toString))),
    ("equations", Json.arr equations), ("unfolding", unfolding),
    ("probeMainModule", toJson (← getEnv).mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end PiExponentEquationProvenanceProbe

namespace GenericLowerPrivateMirrorSnapshot
open Lean Meta FullRowMinorProofSnapshot

def certifiedPrimaries : Array (Name × String) := #[(`OAI.PiExponent.InterpolationMatrix.exponentVector, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.InterpolationMatrix.truncatedLog, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.InterpolationMatrix.monomialImage, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.InterpolationMatrix.entry, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.InterpolationMatrix.matrix, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.InterpolationMatrix.truncatedLogMatrix, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData"), (`OAI.PiExponent.MatrixArithmetic.logWeights, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.rationalCenters, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.truncationOrders, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.rowWeightedSum, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.meanRowWeight, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.selectedMinor, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData"), (`OAI.PiExponent.MatrixArithmetic.columnScale, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"), (`OAI.PiExponent.MatrixArithmetic.rowScale, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"), (`OAI.PiExponent.MatrixArithmetic.denominator, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"), (`OAI.PiExponent.MatrixArithmetic.rowCost, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"), (`OAI.PiExponent.MatrixArithmetic.columnCost, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"), (`OAI.PiExponent.realWeightedSimplex, "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains"), (`OAI.PiExponent.strictWeightedSimplex, "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains"), (`OAI.PiExponent.InterpolationMatrix.columnWeights, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains"), (`OAI.PiExponent.InterpolationMatrix.rowWeights, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains"), (`OAI.PiExponent.InterpolationMatrix.Column, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains"), (`OAI.PiExponent.InterpolationMatrix.Row, "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains")]
def certifiedAutomaticDataHelpers : Array Name := #[`OAI.PiExponent.InterpolationMatrix.matrix._proof_1]

def resolveRoots (helpers : Array Name) (target : Name) (equations : Array Name)
    (moduleName output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target
    | throwError "Original clearing target has no imported module owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName &&
      (Lean.privateToUserName? target).isNone do
    throwError "Original clearing target is not the exact public source theorem"
  for userName in helpers do
    unless (env.find? userName).isNone do
      throwError "Original helper unexpectedly has a public kernel binding: {userName}"
  let mut candidates : Array (Name × Name) := #[]
  let mut publicNames : Array Name := #[]
  -- One environment traversal. Ownership is filtered by the exact module index
  -- before private user-name decoding or any effectful owner export.
  for (actualName, _) in env.constants.toList do
    if env.getModuleIdxFor? actualName == some moduleIndex then
      match Lean.privateToUserName? actualName with
      | some userName =>
          if helpers.contains userName then
            candidates := candidates.push (userName, actualName)
      | none => publicNames := publicNames.push actualName
  let mut resolved : Array Name := #[]
  let mut mapping : Array Json := #[]
  for userName in helpers do
    let found := candidates.filter (fun pair => pair.1 == userName)
    unless found.size == 1 do
      throwError "Exact actual private name/module binding is missing or ambiguous: {userName}"
    let actualName := found[0]!.2
    let some ci := env.find? actualName | throwError "Actual private CI is absent"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Private original helper is not a theorem"
    resolved := resolved.push actualName
    mapping := mapping.push <| Json.mkObj [
      ("sourceName",toJson userName.toString),("actualName",toJson actualName.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? actualName).map Name.toString)),
      ("owner",← ownerOf env actualName)]
  publicNames := publicNames.qsort (fun a b => a.toString < b.toString)
  let inventoryOutput := "missions/pi-irrationality-measure/verification/ap17/generic-lower-child-mirror-probe-v4/actual-owned-public-inventory.json"

  let mut inventory : Array Json := #[]
  for n in publicNames do
    let ci ← getConstInfo n
    let (binderCount, primary?) ← forallTelescope ci.type fun xs body => do
      let primary? := if body.isAppOfArity ``Eq 3 then
        match (body.getAppArgs[1]!).getAppFn with
        | .const primary _ => some primary
        | _ => none
        else none
      return (xs.size, primary?)
    let equations? ← match primary? with
      | some primary => Lean.Meta.getEqnsFor? primary
      | none => pure none
    let unfolding? ← match primary? with
      | some primary => Lean.Meta.getUnfoldEqnFor? primary
      | none => pure none
    let inverse? ← Lean.Meta.isEqnThm? n
    inventory := inventory.push <| Json.mkObj [
      ("actualName",toJson n.toString),("binderCount",toJson binderCount),
      ("closedForallEqLhsHead",toJson (primary?.map Name.toString)),
      ("actualEquationNames",toJson (equations?.map (·.map Name.toString))),
      ("actualUnfoldingName",toJson (unfolding?.map Name.toString)),
      ("inversePrimary",toJson (inverse?.map Name.toString)),
      ("CI",Json.mkObj (← ciRow n true))]
  IO.FS.writeFile inventoryOutput (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("rows",Json.arr inventory)]).compress

  let mut dataEquations : Array Json := #[]
  for n in publicNames do
    if n != target && !equations.contains n then
      let equationCI ← getConstInfo n
      match equationCI with
      | .thmInfo _ => pure ()
      | _ => throwError "Auxiliary data equation is not a theorem CI"
      unless !equationCI.type.hasMVar && !equationCI.type.hasFVar &&
          !equationCI.type.hasLooseBVars do
        throwError "Auxiliary theorem full type is not closed"
      let (primary, binderCount, closedEqualityType) ←
        forallTelescope equationCI.type fun xs body => do
          unless body.isAppOfArity ``Eq 3 do
            throwError "Auxiliary public CI is not a forall/Eq type: {n}"
          let args := body.getAppArgs
          let lhs := args[1]!
          let rhs := args[2]!
          let primary ← match lhs.getAppFn with
            | .const name _ => pure name
            | _ => throwError "Auxiliary Eq left side has no exact primary head constant"
          unless !lhs.hasMVar && !rhs.hasMVar do
            throwError "Auxiliary equality has metavariables before defEq"
          unless (← withTransparency .all <| isDefEqNoConstantApprox lhs rhs) do
            throwError "Auxiliary equality sides are not definitionally equal: {n}"
          unless !lhs.hasMVar && !rhs.hasMVar do
            throwError "Auxiliary equality has metavariables after defEq"
          let closed ← mkForallFVars xs body
          unless !closed.hasMVar && !closed.hasFVar && !closed.hasLooseBVars do
            throwError "Auxiliary equality telescope could not be reclosed"
          return (primary, xs.size, closed)
      let certified := certifiedPrimaries.filter (fun pair => pair.1 == primary)
      unless certified.size == 1 do
        throwError "Owned data equation has no exact Published full-Def primary certificate: {n}"
      let expectedModule := certified[0]!.2
      unless (← ownerModule env primary) == expectedModule do
        throwError "Auxiliary data-equation primary owner differs: {primary}"
      let primaryCI ← getConstInfo primary
      match primaryCI with
      | .defnInfo _ => pure ()
      | _ => throwError "Auxiliary equation inverse primary is not a definition"
      -- Capture both forward APIs before reading the nonpersistent inverse.
      let actualEquations? ← Lean.Meta.getEqnsFor? primary
      let actualUnfolding? ← Lean.Meta.getUnfoldEqnFor? primary
      let inverse? ← Lean.Meta.isEqnThm? n
      if let some inverse := inverse? then
        unless inverse == primary do
          throwError "Auxiliary inverse disagrees with its actual Eq lhs head"
      let route := if (actualEquations?.getD #[]).contains n then
          "equation-registry-forward"
        else if actualUnfolding? == some n then "unfolding-registry-forward"
        else "closed-typed-definitional-equality"
      let mut automaticDataHelpers : Array Json := #[]
      let some proofValue := valueOf equationCI
        | throwError "Auxiliary equation proof value missing"
      for used in refs (mkApp equationCI.type proofValue) do
        if certifiedAutomaticDataHelpers.contains used then
          let helperCI ← getConstInfo used
          unless (← isProp helperCI.type) do
            throwError "Certified automatic data helper is not a genuine Prop CI"
          automaticDataHelpers := automaticDataHelpers.push <| Json.mkObj [
            ("actualIsProp",toJson true),("CI",Json.mkObj (← ciRow used true))]
      dataEquations := dataEquations.push <| Json.mkObj [
        ("actualName",toJson n.toString),("primaryName",toJson primary.toString),
        ("primaryExpectedModule",toJson expectedModule),
        ("inverseGetter",toJson "Lean.Meta.isEqnThm?"),
        ("inversePrimary",toJson (inverse?.map Name.toString)),
        ("getter",toJson "Lean.Meta.getEqnsFor?"),
        ("actualEquationNames",toJson (actualEquations?.map (·.map Name.toString))),
        ("unfoldingGetter",toJson "Lean.Meta.getUnfoldEqnFor?"),
        ("actualUnfoldingName",toJson (actualUnfolding?.map Name.toString)),
        ("candidateBasis",toJson "actual closed CI forall/Eq lhs head constant"),
        ("provenanceRoute",toJson route),
        ("kernelEqualityProbe",Json.mkObj [
          ("checker",toJson "Lean.Meta.isDefEqNoConstantApprox"),
          ("transparency",toJson "all"),("constantApproximation",toJson false),
          ("binderCount",toJson binderCount),
          ("closedEqualityType",PiExponentInterfaceSnapshot.exprJson closedEqualityType),
          ("closedBeforeAndAfter",toJson true),("noMetavariablesBeforeAndAfter",toJson true),
          ("lhsHeadConstant",toJson primary.toString),("definitionalEquality",toJson true)]),
        ("primaryBinding",← PiExponentEquationProvenanceProbe.checkedCI primary),
        ("equation",← PiExponentEquationProvenanceProbe.checkedCI n),
        ("closedEquationProofReferences",Json.mkObj (← ciRow n true)),
        ("actualCertifiedAutomaticDataHelpers",Json.arr automaticDataHelpers)]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),("mapping",Json.arr mapping),
    ("publicTarget",toJson target.toString),("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("officialDataEquationCandidates",toJson (equations.map Name.toString)),
    ("ownedDataEquations",Json.arr dataEquations)]).compress
  return resolved.push target ++ equations
end GenericLowerPrivateMirrorSnapshot

run_meta do
  let roots ← GenericLowerPrivateMirrorSnapshot.resolveRoots #[`OAI.PiExponent.mem_realWeightedSimplex, `OAI.PiExponent.mem_strictWeightedSimplex, `OAI.PiExponent.InterpolationMatrix.column_mem_iff, `OAI.PiExponent.InterpolationMatrix.row_mem_iff, `OAI.PiExponent.InterpolationMatrix.column_weight_le, `OAI.PiExponent.InterpolationMatrix.row_weight_lt, `OAI.PiExponent.Arithmetic.log_lcmUpto_le, `OAI.PiExponent.Arithmetic.log_lcm_power_product_le, `OAI.PiExponent.Arithmetic.log_lcm_floor_product_le, `OAI.PiExponent.Arithmetic.sum_ceil_truncation_div_le, `OAI.PiExponent.Arithmetic.truncation_denominator_log_le, `OAI.PiExponent.Arithmetic.column_log_cost_le, `OAI.PiExponent.Arithmetic.sum_exponents_le_weight_div, `OAI.PiExponent.Arithmetic.row_log_cost_lower, `OAI.PiExponent.Arithmetic.normalized_arithmetic_bound, `OAI.PiExponent.MatrixArithmetic.log_denominator_le, `OAI.PiExponent.MatrixArithmetic.actual_row_card_pos, `OAI.PiExponent.MatrixArithmetic.ceil_log_weight_pos, `OAI.PiExponent.MatrixArithmetic.column_log_cost_le_H, `OAI.PiExponent.MatrixArithmetic.selected_column_log_cost_le, `OAI.PiExponent.MatrixArithmetic.row_weighted_cost_le] `OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound #[] "Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound" "missions/pi-irrationality-measure/verification/ap17/generic-lower-child-mirror-probe-v4/actual-private-mapping.json"
  PiExponentInterfaceSnapshot.exportSnapshot roots "missions/pi-irrationality-measure/verification/ap17/generic-lower-child-mirror-probe-v4/generated-types.json"
  SelectedMinorProofSnapshot.exportBundle "generated" "missions/pi-irrationality-measure/verification/ap17/generic-lower-child-mirror-probe-v4/generated-proof-references.json" roots #["Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound", "Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_clearing_bound", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains"] #["OAI.PiExponent.Arithmetic.lcmConstant", "OAI.PiExponent.Arithmetic.lcmConstant_pos", "OAI.PiExponent.InterpolationMatrix.Column", "OAI.PiExponent.InterpolationMatrix.Row", "OAI.PiExponent.InterpolationMatrix.columnWeights", "OAI.PiExponent.InterpolationMatrix.rowWeights", "OAI.PiExponent.MatrixArithmetic.columnCost", "OAI.PiExponent.MatrixArithmetic.denominator", "OAI.PiExponent.MatrixArithmetic.logWeights", "OAI.PiExponent.MatrixArithmetic.meanRowWeight", "OAI.PiExponent.MatrixArithmetic.rowCost", "OAI.PiExponent.MatrixArithmetic.rowWeightedSum", "OAI.PiExponent.MatrixArithmetic.selectedMinor", "OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound", "OAI.PiExponent.MatrixArithmetic.truncationOrders", "OAI.PiExponent.realWeightedSimplex", "OAI.PiExponent.strictWeightedSimplex"]
#print axioms OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_ThreeSum1960614_Analysis

open Lean

/- Alpha normalization only: erase binder labels and non-semantic metadata.
   Named constants, binder information, universe levels and all term structure
   are preserved. No definition unfolding or source text replacement occurs. -/
private partial def alpha (expr : Expr) : Expr :=
  match expr with
  | .app f a => .app (alpha f) (alpha a)
  | .lam _ type body info => .lam .anonymous (alpha type) (alpha body) info
  | .forallE _ type body info => .forallE .anonymous (alpha type) (alpha body) info
  | .letE _ type value body nondep => .letE .anonymous (alpha type) (alpha value) (alpha body) nondep
  | .mdata _ value => alpha value
  | .proj name index value => .proj name index (alpha value)
  | other => other

/- Compiled modules can share generated matchers under different names.
   Expand only matchers recognized by Lean itself, plus beta reduction.
   Ordinary named definitions are never unfolded by this comparison. -/
private partial def matcherNormal (env : Environment) (fuel : Nat) (expr : Expr) : Expr :=
  match expr with
  | .const name levels =>
      if Meta.isMatcherCore env name then
        match fuel,env.find? name with
        | fuel+1,some (.defnInfo value) =>
            matcherNormal env fuel (value.value.instantiateLevelParams value.levelParams levels)
        | 0,_ => panic! "matcher normalization fuel exhausted"
        | _,_ => expr
      else expr
  | .app f a =>
      let applied := Expr.app (matcherNormal env fuel f) (matcherNormal env fuel a)
      let reduced := applied.headBeta
      if reduced == applied then applied else matcherNormal env fuel reduced
  | .lam name type body info => .lam name (matcherNormal env fuel type) (matcherNormal env fuel body) info
  | .forallE name type body info => .forallE name (matcherNormal env fuel type) (matcherNormal env fuel body) info
  | .letE name type value body nondep =>
      .letE name (matcherNormal env fuel type) (matcherNormal env fuel value) (matcherNormal env fuel body) nondep
  | .mdata _ value => matcherNormal env fuel value
  | .proj name index value => .proj name index (matcherNormal env fuel value)
  | other => other

run_meta do
  let env ← getEnv
  let wanted : Array Name := #[`Definitions.Def_TrulySubcubicAPSP_SourceSpecification, `Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax, `Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic, `Definitions.Def_ThreeSum1960614_Analysis]
  let modules := env.header.moduleNames
  let mut lines : Array String := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | continue
    unless wanted.contains mod do continue
    let value : Option Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo d => some d.value
      | .opaqueInfo o => some o.value
      | _ => none
    let isTheorem := match ci with | .thmInfo _ => true | _ => false
    lines := lines.push <| (Json.mkObj [
      ("name", toJson name.toString),
      ("userName", toJson ((privateToUserName? name).getD name).toString),
      ("module", toJson mod.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", toJson (reprStr ci.type)),
      ("value", toJson (value.map reprStr)),
      ("alphaType", toJson (reprStr (alpha ci.type))),
      ("alphaValue", toJson (value.map fun expr => reprStr (alpha expr))),
      ("matcherValue", toJson (if isTheorem then none else
        value.map fun expr => reprStr (alpha (matcherNormal env 64 expr))))]).compress
  IO.FS.writeFile "missions/3sum-1960614/verification/reuse-interfaces-platform.jsonl" (String.intercalate "\n" lines.toList ++ "\n")
  logInfo s!"wrote {lines.size} exact reusable interface records"

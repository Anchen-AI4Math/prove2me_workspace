import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_ThreeSum1960614_Analysis

open Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private partial def alphaExtendedReuse (expr : Expr) : Expr :=
  match expr with
  | .app f a => .app (alphaExtendedReuse f) (alphaExtendedReuse a)
  | .lam _ t b i => .lam .anonymous (alphaExtendedReuse t) (alphaExtendedReuse b) i
  | .forallE _ t b i => .forallE .anonymous (alphaExtendedReuse t) (alphaExtendedReuse b) i
  | .letE _ t v b d => .letE .anonymous (alphaExtendedReuse t) (alphaExtendedReuse v) (alphaExtendedReuse b) d
  | .mdata _ e => alphaExtendedReuse e
  | .proj n i e => .proj n i (alphaExtendedReuse e)
  | e => e

private partial def expandExtendedMatchers (env : Environment) (fuel : Nat) (expr : Expr) : Expr :=
  match expr with
  | .const n levels =>
      if Meta.isMatcherCore env n then
        match fuel,env.find? n with
        | fuel+1,some (.defnInfo value) => expandExtendedMatchers env fuel (value.value.instantiateLevelParams value.levelParams levels)
        | 0,_ => panic! "Generated matcher normalization fuel exhausted"
        | _,_ => expr
      else expr
  | .app f a =>
      let result := Expr.app (expandExtendedMatchers env fuel f) (expandExtendedMatchers env fuel a)
      let reduced := result.headBeta
      if result == reduced then result else expandExtendedMatchers env fuel reduced
  | .lam n t b i => .lam n (expandExtendedMatchers env fuel t) (expandExtendedMatchers env fuel b) i
  | .forallE n t b i => .forallE n (expandExtendedMatchers env fuel t) (expandExtendedMatchers env fuel b) i
  | .letE n t v b d => .letE n (expandExtendedMatchers env fuel t) (expandExtendedMatchers env fuel v) (expandExtendedMatchers env fuel b) d
  | .mdata _ e => expandExtendedMatchers env fuel e
  | .proj n i e => .proj n i (expandExtendedMatchers env fuel e)
  | e => e

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/extended-reuse-input-names.json"
  let inputNames ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut records : Array String := #[]
  let mut missing : Array String := #[]
  for item in inputNames do
    let text ← match item.getStr? with
      | .ok value => pure value
      | .error message => throwError message
    let name := text.toName
    let some ci := env.find? name | missing := missing.push text; continue
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let norm := fun e => alphaExtendedReuse (e.instantiateLevelParams ci.levelParams levels)
    let normBody := fun e => norm (expandExtendedMatchers env 64 e)
    let value : Option Expr := match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo o => some o.value
      | _ => none
    let kind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor"
      | .recInfo _ => "recursor"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quot"
    let shape := match ci with
      | .inductInfo d => Json.mkObj [
          ("numParams",toJson d.numParams),("numIndices",toJson d.numIndices),
          ("all",toJson (d.all.map Name.toString)),("ctors",toJson (d.ctors.map Name.toString)),
          ("numNested",toJson d.numNested),("recursive",toJson d.isRec),
          ("reflexive",toJson d.isReflexive),("unsafe",toJson d.isUnsafe)]
      | .ctorInfo c => Json.mkObj [("induct",toJson c.induct.toString),("index",toJson c.cidx),
          ("numParams",toJson c.numParams),("numFields",toJson c.numFields),("unsafe",toJson c.isUnsafe)]
      | .recInfo r => Json.mkObj [("all",toJson (r.all.map Name.toString)),
          ("numParams",toJson r.numParams),("numIndices",toJson r.numIndices),
          ("numMotives",toJson r.numMotives),("numMinors",toJson r.numMinors),
          ("k",toJson r.k),("unsafe",toJson r.isUnsafe),
          ("rules",toJson (r.rules.map fun rule =>
            (rule.ctor.toString,rule.nfields,reprStr (normBody rule.rhs))))]
      | .defnInfo d => Json.mkObj [("safety",toJson (reprStr d.safety)),
          ("abbrev",toJson (match d.hints with | .abbrev => true | _ => false))]
      | .opaqueInfo d => Json.mkObj [("unsafe",toJson d.isUnsafe)]
      | _ => Json.null
    let moduleName := ((env.getModuleIdxFor? name).bind fun i => env.header.moduleNames[i.toNat]?).getD Name.anonymous
    let axioms ← collectAxioms name
    records := records.push <| (Json.mkObj [
      ("name",toJson text),("module",toJson moduleName.toString),("kind",toJson kind),
      ("isProof",toJson (← Meta.isProp ci.type)),("universeCount",toJson ci.levelParams.length),
      ("rawType",toJson (reprStr ci.type)),("rawValue",toJson (value.map reprStr)),
      ("type",toJson (reprStr (norm ci.type))),
      ("value",toJson (value.map fun e => reprStr (normBody e))),
      ("shape",shape),("axioms",toJson (axioms.map Name.toString))]).compress
  IO.FS.writeFile "missions/3sum-1960614/verification/extended-reuse-public.jsonl"
    (String.intercalate "\n" records.toList ++ "\n")
  IO.FS.writeFile "missions/3sum-1960614/verification/extended-reuse-public-missing.json" (toJson missing).compress
  logInfo s!"read {records.size} complete CI records; {missing.size} names absent"

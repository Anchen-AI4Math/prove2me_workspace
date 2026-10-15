import Lean
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax

open Lean
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

run_meta do
  let originalRaw : Expr := (
    Lean.Expr.lam
      Lean.Name.anonymous
      (Lean.Expr.sort
        (Lean.Level.param
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `v.«_@».Submission.ThreeSumApsp.Lang.Syntax 4279789133) "_hygCtx") "_hyg") 6)))
      (Lean.Expr.lam
        Lean.Name.anonymous
        (Lean.Expr.const `Light.Op [])
        (Lean.Expr.lam
          Lean.Name.anonymous
          (Lean.Expr.const `Light.Op [])
          (Lean.Expr.lam
            Lean.Name.anonymous
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Light.Op []))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `noConfusionEnum
                              [Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.param
                                 (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `v.«_@».Submission.ThreeSumApsp.Lang.Syntax 4279789133) "_hygCtx") "_hyg") 6)])
                            (Lean.Expr.const `Light.Op []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instDecidableEqNat []))
                      (Lean.Expr.const `Light.Op.ctorIdx []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.implicit))
        (Lean.BinderInfo.implicit))
      (Lean.BinderInfo.implicit))
  let publishedRaw : Expr := (
    Lean.Expr.lam
      Lean.Name.anonymous
      (Lean.Expr.sort
        (Lean.Level.param
          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `v.«_@».Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax 4279789133) "_hygCtx") "_hyg") 6)))
      (Lean.Expr.lam
        Lean.Name.anonymous
        (Lean.Expr.const `Light.Op [])
        (Lean.Expr.lam
          Lean.Name.anonymous
          (Lean.Expr.const `Light.Op [])
          (Lean.Expr.lam
            Lean.Name.anonymous
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Light.Op []))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `noConfusionEnum
                              [Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.param
                                 (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `v.«_@».Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax 4279789133) "_hygCtx") "_hyg") 6)])
                            (Lean.Expr.const `Light.Op []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instDecidableEqNat []))
                      (Lean.Expr.const `Light.Op.ctorIdx []))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.implicit))
        (Lean.BinderInfo.implicit))
      (Lean.BinderInfo.implicit))
  let ci ← getConstInfo `Light.Op.noConfusion
  let originalParams := (collectLevelParams {} originalRaw).params.toList
  let publishedParams := (collectLevelParams {} publishedRaw).params.toList
  unless originalParams.length == ci.levelParams.length && publishedParams.length == ci.levelParams.length do
    throwError "Unexpected universe parameter count"
  let original := originalRaw.instantiateLevelParams originalParams (ci.levelParams.map Level.param)
  let published := publishedRaw.instantiateLevelParams publishedParams (ci.levelParams.map Level.param)
  unless (← Meta.isDefEq original published) do
    throwError "Definition bodies are not definitionally equal: Light.Op.noConfusion"
  let type ← Meta.mkEq original published
  let value ← Meta.mkEqRefl original
  addDecl <| .thmDecl {
    name := `ThreeSum1960614.ReuseAudit.interface_0
    levelParams := ci.levelParams
    type := (← instantiateMVars type)
    value := (← instantiateMVars value) }
  logInfo "Kernel checked definition-body equality: Light.Op.noConfusion"

#print axioms ThreeSum1960614.ReuseAudit.interface_0

run_meta do
  let originalRaw : Expr := (
    Lean.Expr.lam
      Lean.Name.anonymous
      (Lean.Expr.const `Light.Op [])
      (Lean.Expr.lam
        Lean.Name.anonymous
        (Lean.Expr.const `Light.Op [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.app
                    (Lean.Expr.const `Decidable [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Light.Op []))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.bvar 0))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instDecidableEqNat [])
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
            (Lean.Expr.lam
              Lean.Name.anonymous
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Decidable.isTrue [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Light.Op []))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Light.instDecidableEqOp._proof_1 []) (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.bvar 0)))
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam
            Lean.Name.anonymous
            (Lean.Expr.app
              (Lean.Expr.const `Not [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Decidable.isFalse [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Light.Op []))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.lam
                Lean.Name.anonymous
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Light.Op []))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Light.instDecidableEqOp._proof_2 []) (Lean.Expr.bvar 3))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.bvar 0))
                (Lean.BinderInfo.default)))
            (Lean.BinderInfo.default)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
  let publishedRaw : Expr := (
    Lean.Expr.lam
      Lean.Name.anonymous
      (Lean.Expr.const `Light.Op [])
      (Lean.Expr.lam
        Lean.Name.anonymous
        (Lean.Expr.const `Light.Op [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `dite [Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.app
                    (Lean.Expr.const `Decidable [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.const `Light.Op []))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.bvar 0))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instDecidableEqNat [])
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
            (Lean.Expr.lam
              Lean.Name.anonymous
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Decidable.isTrue [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Light.Op []))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Light.instDecidableEqOp._proof_1 []) (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.bvar 0)))
              (Lean.BinderInfo.default)))
          (Lean.Expr.lam
            Lean.Name.anonymous
            (Lean.Expr.app
              (Lean.Expr.const `Not [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 1)))
                (Lean.Expr.app (Lean.Expr.const `Light.Op.ctorIdx []) (Lean.Expr.bvar 0))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Decidable.isFalse [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Light.Op []))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Light.instDecidableEqOp._proof_2 []) (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.BinderInfo.default)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
  let ci ← getConstInfo `Light.instDecidableEqOp
  let originalParams := (collectLevelParams {} originalRaw).params.toList
  let publishedParams := (collectLevelParams {} publishedRaw).params.toList
  unless originalParams.length == ci.levelParams.length && publishedParams.length == ci.levelParams.length do
    throwError "Unexpected universe parameter count"
  let original := originalRaw.instantiateLevelParams originalParams (ci.levelParams.map Level.param)
  let published := publishedRaw.instantiateLevelParams publishedParams (ci.levelParams.map Level.param)
  unless (← Meta.isDefEq original published) do
    throwError "Definition bodies are not definitionally equal: Light.instDecidableEqOp"
  let type ← Meta.mkEq original published
  let value ← Meta.mkEqRefl original
  addDecl <| .thmDecl {
    name := `ThreeSum1960614.ReuseAudit.interface_1
    levelParams := ci.levelParams
    type := (← instantiateMVars type)
    value := (← instantiateMVars value) }
  logInfo "Kernel checked definition-body equality: Light.instDecidableEqOp"

#print axioms ThreeSum1960614.ReuseAudit.interface_1

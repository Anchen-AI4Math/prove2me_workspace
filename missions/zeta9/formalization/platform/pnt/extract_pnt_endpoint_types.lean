import missions.zeta9.formalization.PNTTransfer
import Lean
open Lean Meta
run_meta do
  let names := #[`MediumPNT, `ZetaNine.HarmonicStability.psi_pnt_rate,
    `ZetaNine.HarmonicStability.harmonic_log_den_rate,
    `ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate,
    `ZetaNine.HarmonicStability.logDen, `ZetaNine.HarmonicStability.harmonicPower,
    `ZetaNine.HarmonicStability.ThetaPNT, `ZetaNine.HarmonicStability.LcmPNT]
  let mut rows : Array Json := #[]
  for n in names do
    let ci ← getConstInfo n
    let typ ← ppExpr ci.type
    let count ← forallTelescope ci.type fun xs _ => pure xs.size
    let body ← match ci with
      | .defnInfo d => do
        let fmt ← ppExpr d.value
        pure (Json.str fmt.pretty)
      | _ => pure Json.null
    rows := rows.push (Json.mkObj [("name", Json.str n.toString),
      ("type", Json.str typ.pretty), ("parameterCount", toJson count),
      ("typeConstants", toJson (ci.type.getUsedConstants.toList.map Name.toString)),
      ("definitionValue", body)])
  IO.FS.writeFile "D:/users/self_projects/prove2me_workspace/missions/zeta9/formalization/platform/pnt/original-endpoint-types.json" (Json.arr rows).pretty
  logInfo s!"audited {rows.size} exact endpoint/object types"

import OutputsDefinitionsAudit
import Lean
open Lean
run_meta do
  let path ← findOLean `OutputsDefinitionsAudit
  IO.println (Json.mkObj [("module",Json.str "OutputsDefinitionsAudit"),("olean",Json.str path.toString)]).compress

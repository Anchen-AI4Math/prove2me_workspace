import Lean
open Lean

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-mixfix-priority-inputs.json"
  let items ← ofExcept (Json.parse raw >>= Json.getArr?)
  let mut output := #[]
  for item in items do
    let text ← ofExcept (item.getObjValAs? String "command")
    let cmd ← ofExcept (Parser.runParserCategory env `command text)
    unless cmd.isOfKind ``Parser.Command.mixfix do throwError "Expected mixfix"
    -- Parser.Syntax.mixfix: doc, attrs, attrKind, kind, precedence,
    -- optNamedName, optNamedPrio, notationItem, darrow, rhs.
    unless cmd[6].isNone do throwError "Unexpected existing notation priority"
    let some first := cmd[7].getPos? | throwError "Missing parsed notation item"
    let some last := cmd[7].getTailPos? | throwError "Missing notation item end"
    let fields ← ofExcept item.getObj?
    output := output.push <| Json.mkObj (fields.toList ++ [
      ("insertOffset",toJson first.byteIdx),
      ("notationItem",toJson (String.fromUTF8! (text.toUTF8.extract first.byteIdx last.byteIdx)))])
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-mixfix-priorities.json" (Json.arr output).pretty
  logInfo s!"Parsed {output.size} exact mixfix priority insertion slots"

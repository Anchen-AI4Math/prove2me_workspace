import Lean
open Lean Elab Parser

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]? | return 1
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  let inputCtx := Parser.mkInputContext input fileName
  let (header, _, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then return 1
  let some start := header.raw.getPos? | return 1
  let some stop := header.raw.getTailPos? | return 1
  IO.println (Json.mkObj [("kind", Json.str "header"),
    ("syntaxKind", Json.str header.raw.getKind.toString),
    ("start", posJson inputCtx.fileMap start),
    ("end", posJson inputCtx.fileMap stop)]).compress
  return 0

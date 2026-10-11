import Lean
open Lean Meta
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace IndependentLosslessExprDagV1
-- Versioned audit serialization only; mathematical source modules are unchanged.
def arr (xs : List Json) : Json := Json.arr xs.toArray
def tag (s : String) : Json := Json.str s
partial def nameJ : Name → Json
  | .anonymous => arr [tag "anonymous"]
  | .str p s => arr [tag "str", nameJ p, toJson s]
  | .num p n => arr [tag "num", nameJ p, toJson n]
partial def nameD (j : Json) : Except String Name := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "anonymous" => return .anonymous
  | "str" => return .str (← nameD a[1]!) (← a[2]!.getStr?)
  | "num" => return .num (← nameD a[1]!) (← a[2]!.getNat?)
  | _ => throw "unknown Name constructor"
partial def levelJ : Level → Json
  | .zero => arr [tag "zero"]
  | .succ u => arr [tag "succ", levelJ u]
  | .max u v => arr [tag "max", levelJ u, levelJ v]
  | .imax u v => arr [tag "imax", levelJ u, levelJ v]
  | .param n => arr [tag "param", nameJ n]
  | .mvar n => arr [tag "mvar", nameJ n.name]
partial def levelD (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => return .zero
  | "succ" => return .succ (← levelD a[1]!)
  | "max" => return .max (← levelD a[1]!) (← levelD a[2]!)
  | "imax" => return .imax (← levelD a[1]!) (← levelD a[2]!)
  | "param" => return .param (← nameD a[1]!)
  | "mvar" => return .mvar ⟨← nameD a[1]!⟩
  | _ => throw "unknown Level constructor"
def substringJ (s : Substring.Raw) : Json :=
  arr [toJson s.str, toJson s.startPos.byteIdx, toJson s.stopPos.byteIdx]
def substringD (j : Json) : Except String Substring.Raw := do
  let a ← j.getArr?
  return ⟨← a[0]!.getStr?, ⟨← a[1]!.getNat?⟩, ⟨← a[2]!.getNat?⟩⟩
def sourceJ : SourceInfo → Json
  | .none => arr [tag "none"]
  | .original l p t e => arr [tag "original",substringJ l,toJson p.byteIdx,substringJ t,toJson e.byteIdx]
  | .synthetic p e c => arr [tag "synthetic",toJson p.byteIdx,toJson e.byteIdx,toJson c]
def sourceD (j : Json) : Except String SourceInfo := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "none" => return .none
  | "original" => return .original (← substringD a[1]!) ⟨← a[2]!.getNat?⟩ (← substringD a[3]!) ⟨← a[4]!.getNat?⟩
  | "synthetic" => return .synthetic ⟨← a[1]!.getNat?⟩ ⟨← a[2]!.getNat?⟩ (← fromJson? a[3]!)
  | _ => throw "unknown SourceInfo constructor"
def preresolvedJ : Syntax.Preresolved → Json
  | .namespace n => arr [tag "namespace",nameJ n]
  | .decl n fs => arr [tag "decl",nameJ n,toJson fs]
def preresolvedD (j : Json) : Except String Syntax.Preresolved := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "namespace" => return .namespace (← nameD a[1]!)
  | "decl" => return .decl (← nameD a[1]!) (← fromJson? a[2]!)
  | _ => throw "unknown Syntax.Preresolved constructor"
partial def syntaxJ : Syntax → Json
  | .missing => arr [tag "missing"]
  | .node info kind args => arr [tag "node",sourceJ info,nameJ kind,Json.arr (args.map syntaxJ)]
  | .atom info s => arr [tag "atom",sourceJ info,toJson s]
  | .ident info raw n resolved => arr [tag "ident",sourceJ info,substringJ raw,nameJ n,arr (resolved.map preresolvedJ)]
partial def syntaxD (j : Json) : Except String Syntax := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "missing" => return .missing
  | "node" => return .node (← sourceD a[1]!) (← nameD a[2]!) (← (← a[3]!.getArr?).mapM syntaxD)
  | "atom" => return .atom (← sourceD a[1]!) (← a[2]!.getStr?)
  | "ident" => return .ident (← sourceD a[1]!) (← substringD a[2]!) (← nameD a[3]!) (← (← a[4]!.getArr?).toList.mapM preresolvedD)
  | _ => throw "unknown Syntax constructor"
def dataJ : DataValue → Json
  | .ofString v => arr [tag "ofString",toJson v]
  | .ofBool v => arr [tag "ofBool",toJson v]
  | .ofName v => arr [tag "ofName",nameJ v]
  | .ofNat v => arr [tag "ofNat",toJson v]
  | .ofInt v => arr [tag "ofInt",toJson v]
  | .ofSyntax v => arr [tag "ofSyntax",syntaxJ v]
def dataD (j : Json) : Except String DataValue := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "ofString" => return .ofString (← a[1]!.getStr?)
  | "ofBool" => return .ofBool (← fromJson? a[1]!)
  | "ofName" => return .ofName (← nameD a[1]!)
  | "ofNat" => return .ofNat (← a[1]!.getNat?)
  | "ofInt" => return .ofInt (← fromJson? a[1]!)
  | "ofSyntax" => return .ofSyntax (← syntaxD a[1]!)
  | _ => throw "unknown DataValue constructor"
def metadataJ (m : MData) : Json := arr (m.entries.map fun (n,v) => arr [nameJ n,dataJ v])
def metadataD (j : Json) : Except String MData := do
  let entries ← (← j.getArr?).toList.mapM fun j => do
    let a ← j.getArr?
    return (← nameD a[0]!, ← dataD a[1]!)
  return ⟨entries⟩
def binderJ : BinderInfo → Json
  | .default => tag "default"
  | .implicit => tag "implicit"
  | .strictImplicit => tag "strictImplicit"
  | .instImplicit => tag "instImplicit"
def binderD (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => throw "unknown BinderInfo constructor"
structure DagState where
  nodes : Array Json := #[]
  cache : ExprStructMap Nat := {}
partial def intern (e : Expr) : StateM DagState Nat := do
  let initial : DagState ← get
  if let some id := initial.cache[(ExprStructEq.mk e)]? then return id
  let node : Json ← match e with
    | .bvar n => pure (arr [tag "bvar",toJson n])
    | .fvar n => pure (arr [tag "fvar",nameJ n.name])
    | .mvar n => pure (arr [tag "mvar",nameJ n.name])
    | .sort u => pure (arr [tag "sort",levelJ u])
    | .const n us => pure (arr [tag "const",nameJ n,arr (us.map levelJ)])
    | .app f a => do pure (arr [tag "app",toJson (← intern f),toJson (← intern a)])
    | .lam n t b i => do pure (arr [tag "lam",nameJ n,toJson (← intern t),toJson (← intern b),binderJ i])
    | .forallE n t b i => do pure (arr [tag "forallE",nameJ n,toJson (← intern t),toJson (← intern b),binderJ i])
    | .letE n t v b d => do pure (arr [tag "letE",nameJ n,toJson (← intern t),toJson (← intern v),toJson (← intern b),toJson d])
    | .lit (.natVal n) => pure (arr [tag "litNat",toJson n])
    | .lit (.strVal s) => pure (arr [tag "litString",toJson s])
    | .mdata m b => do pure (arr [tag "mdata",metadataJ m,toJson (← intern b)])
    | .proj n i b => do pure (arr [tag "proj",nameJ n,toJson i,toJson (← intern b)])
  let st : DagState ← get
  let id := st.nodes.size
  set {st with nodes := st.nodes.push node, cache := st.cache.insert (ExprStructEq.mk e) id}
  return id
def encode (t v : Expr) : Json :=
  let ((tr,vr),st) := (do return (← intern t,← intern v)).run {}
  Json.mkObj [("format",tag "lean-expr-dag-v1"),("type_root",toJson tr),("value_root",toJson vr),("nodes",Json.arr st.nodes)]
def reference (built : Array Expr) (j : Json) : Except String Expr := do
  let id ← j.getNat?
  match built[id]? with
  | some e => return e
  | none => throw "Expr DAG reference is not topologically earlier"
def decodeNode (built : Array Expr) (j : Json) : Except String Expr := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "bvar" => return .bvar (← a[1]!.getNat?)
  | "fvar" => return .fvar ⟨← nameD a[1]!⟩
  | "mvar" => return .mvar ⟨← nameD a[1]!⟩
  | "sort" => return .sort (← levelD a[1]!)
  | "const" => return .const (← nameD a[1]!) (← (← a[2]!.getArr?).toList.mapM levelD)
  | "app" => return .app (← reference built a[1]!) (← reference built a[2]!)
  | "lam" => return .lam (← nameD a[1]!) (← reference built a[2]!) (← reference built a[3]!) (← binderD a[4]!)
  | "forallE" => return .forallE (← nameD a[1]!) (← reference built a[2]!) (← reference built a[3]!) (← binderD a[4]!)
  | "letE" => return .letE (← nameD a[1]!) (← reference built a[2]!) (← reference built a[3]!) (← reference built a[4]!) (← fromJson? a[5]!)
  | "litNat" => return .lit (.natVal (← a[1]!.getNat?))
  | "litString" => return .lit (.strVal (← a[1]!.getStr?))
  | "mdata" => return .mdata (← metadataD a[1]!) (← reference built a[2]!)
  | "proj" => return .proj (← nameD a[1]!) (← a[2]!.getNat?) (← reference built a[3]!)
  | _ => throw "unknown Expr constructor"
def decode (j : Json) : Except String (Expr × Expr) := do
  let nodes ← (← j.getObjVal? "nodes").getArr?
  let mut built : Array Expr := #[]
  for node in nodes do built := built.push (← decodeNode built node)
  return (← reference built (← j.getObjVal? "type_root"),
    ← reference built (← j.getObjVal? "value_root"))
def persistedRoundTrip (t v : Expr) : Except String Json := do
  let payload := encode t v
  let parsed ← Json.parse payload.compress
  let (rt,rv) ← decode parsed
  unless Expr.equal t rt && Expr.equal v rv do throw "Lossless Expr DAG roundtrip failed"
  return parsed
end IndependentLosslessExprDagV1

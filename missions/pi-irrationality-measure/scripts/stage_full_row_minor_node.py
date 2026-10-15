"""Pure, immutable staging for the exact full-row-minor source theorem.

Never starts Lean, reads credentials, or makes network requests. The root agent
alone runs the four sequential bounded compiler commands.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap8/minor"
SELF = Path(__file__).resolve()
MODULE = "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix"
NAME = "OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective"
SHORT_NAME = "exists_full_row_minor_of_surjective"
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_URL = f"https://github.com/openai/math/blob/{SOURCE_COMMIT}/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean#L135-L166"
SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean"
ORIGINAL = TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean"
AST = V / "ast-unit-inventory.json"
SCOPES = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
QUEUE = V / "ap7/next-after-comparison.json"
SNAPSHOT_CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
RUNTIME = V / "lean-runtime.json"
CONTEXT = TASK / "scripts/validate_namespace_context_providers.py"
SOURCE_OUTPUT = "Theorems/Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective.lean"
SOLUTION_OUTPUT = "Solutions/Sol_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective_ap8_global.lean"
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective_ap8_global"
SOURCE_SNAPSHOT = "SourceSnapshot.lean"
GENERATED_SNAPSHOT = "GeneratedSnapshotWithRefs.lean"
SOURCE_TYPE_JSON = "source-type.json"
GENERATED_TYPE_JSON = "generated-type.json"
SOURCE_REFS_JSON = "source-proof-references.json"
GENERATED_REFS_JSON = "generated-proof-references.json"
IMPORTS = ["Mathlib"]
SOURCE_SHA = "ab84501a2a29cb569118260ffd1adb30ca827936727fa868db0e829cb1bfde38"
UNIT_SHA = "38c65a74f979d50cb355f1d1f60ec74ae4d6ba6a0f89f1db689dd8508173ae57"
BYTE_RANGE = [6080, 7616]
FILES = [SOURCE_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ["modecheck", "emit-olean", "modecheck", "modecheck"]
MANIFESTS = [f"c{i}.json" for i in range(1, 5)]


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encode(document):
    return (json.dumps(document, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def source_evidence():
    raw = SOURCE.read_bytes()
    need(sha_bytes(raw) == SOURCE_SHA, "Pinned InterpolationMatrix port changed")
    unit = raw[6080:7616]
    need(sha_bytes(unit) == UNIT_SHA, "Pinned theorem AST bytes changed")
    module = next(x for x in read(AST)["modules"] if x["module"] == MODULE)
    ast = next(x for x in module["units"] if NAME in x["graph_names"])
    need(module["source_sha256"] == SOURCE_SHA and ast["graph_names"] == [NAME]
         and ast["graph_kinds"] == ["theorem"] and ast["privateTok"] is None
         and ast["start"]["offset"] == 6080 and ast["end"]["offset"] == 7616
         and ast["nameRange"]["start"]["offset"] == 6088
         and ast["nameRange"]["end"]["offset"] == 6123
         and ast["valueStart"]["offset"] == 6367
         and not ast["is_instance_command"] and not ast["is_local_instance"],
         "Exact AST declaration binding differs")
    scopes = next(x for x in read(SCOPES)["modules"]
                  if x["source"] == "OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean")
    scope = next(x for x in scopes["declarations"] if x["verified_name"] == NAME)
    need(scopes["source_sha256"] == SOURCE_SHA
         and scope["namespace"] == "OAI.PiExponent.InterpolationMatrix"
         and [x["name"] for x in scope["scope_stack"]] == ["OAI", "PiExponent", "InterpolationMatrix"]
         and all(x["kind"] == "namespace" for x in scope["scope_stack"])
         and len(scope["context_commands"]) == 1,
         "Actual theorem scope or section variable context differs")
    context = scope["context_commands"][0]
    need(context["syntaxKind"] == "Lean.Parser.Command.open"
         and context["range"]["start"]["offset"] == 126
         and context["range"]["end"]["offset"] == 150
         and raw[126:150] == b"open scoped BigOperators", "Source BigOperators context differs")
    row = next(json.loads(x) for x in GRAPH.read_text(encoding="utf-8").splitlines()
               if json.loads(x).get("name") == NAME)
    need(row["module"] == MODULE and row["kind"] == "theorem"
         and not row["isPrivate"] and not row["isInstance"]
         and row["typeDeps"] == [] and row["valueDeps"] == [], "Actual project graph changed")
    queue = read(QUEUE)["next_node"]
    need(queue["source_name"] == NAME and queue["source_commit"] == SOURCE_COMMIT
         and queue["source_sha256"] == SOURCE_SHA and queue["source_ast_bytes"] == BYTE_RANGE
         and queue["source_unit_sha256"] == UNIT_SHA, "Targeted queue provenance changed")
    binder = (b"{R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]\r\n"
              b"    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin)")
    need(binder in unit, "Source explicit type/instance binders changed")
    # This theorem has no version adaptation: original and port command match
    # modulo source line endings; preserve both complete inputs and hashes.
    original = ORIGINAL.read_bytes()
    normalized = unit.replace(b"\r\n", b"\n")
    need(original.replace(b"\r\n", b"\n").count(normalized) == 1,
         "Original source theorem differs from pinned port command")
    return unit, ast, scope, row


def assembly():
    unit, _, _, _ = source_evidence()
    value_start = 6367 - 6080
    need(unit[value_start:value_start + 5] == b":= by", "AST proof start differs")
    preamble = (b"import Mathlib\n\nnamespace OAI\n\nopen scoped BigOperators\n\n"
                b"namespace PiExponent.InterpolationMatrix\n\n")
    formal = unit[:value_start] + b":= by\n  sorry\n\nend PiExponent.InterpolationMatrix\n\nend OAI\n"
    solution_preamble = b"import Mathlib\n\nopen scoped BigOperators\n\n"
    renamed = unit[:8] + b"solution" + unit[43:]
    need(renamed.startswith(b"theorem solution\r\n"), "Global literal solution rename failed")
    need(renamed[renamed.find(b" := by"):] == unit[unit.find(b" := by"):],
         "Source proof body bytes changed")
    return preamble, formal, preamble + formal, solution_preamble + renamed


def source_unit():
    return source_evidence()[0]


PROBE = r'''
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
'''


def snapshot(side, module, name):
    output = workspace_rel(STAGE / (side + "-type.json"))
    refs_output = workspace_rel(STAGE / (side + "-proof-references.json"))
    return ("import Lean\nimport " + module + "\n\n"
            + SNAPSHOT_CORE.read_text(encoding="utf-8").rstrip() + "\n\n"
            + "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`" + name + "] "
            + json.dumps(output) + "\n#print axioms " + name + "\n" + PROBE
            + "\nrun_meta do\n  FullRowMinorProofSnapshot.exportEvidence "
            + " ".join(json.dumps(x) for x in [side, refs_output, name, module]) + "\n").encode("utf-8")


def metadata():
    return {
        "title": "A surjective matrix has a nonzero full-row minor",
        "statement": "Let R and C be finite types, let K be a field, and let A be an R-by-C matrix over K. If the associated linear map from C-indexed vectors to R-indexed vectors is surjective, then there is an injective selection of columns indexed by R whose square minor has nonzero determinant.",
        "explanation": "Choose a matrix right inverse. Expand the determinant of their product, which is the identity, as a sum over column selections. Some summand is nonzero, so its minor has nonzero determinant. Repeated selected columns would make that determinant zero, hence the selected columns are distinct.",
        "tags": ["linear-algebra", "number-theory", "openai-pi-exponent-017"],
        "source_commit": SOURCE_COMMIT, "source_url": SOURCE_URL,
    }


def stage_files():
    unit, ast, scope, row = source_evidence()
    preamble, formal, target, solution = assembly()
    generated = {
        SOURCE_OUTPUT: target, SOLUTION_OUTPUT: solution,
        SOURCE_SNAPSHOT: snapshot("source", MODULE, NAME),
        GENERATED_SNAPSHOT: snapshot("generated", SOLUTION_MODULE, "solution"),
        "wire-theorem-source.lean": target,
        "source-command.lean.txt": unit,
        "academic-metadata.json": encode(metadata()),
    }
    inputs = {rel(p): sha(p) for p in [SELF, SOURCE, ORIGINAL, AST, SCOPES, GRAPH,
             QUEUE, SNAPSHOT_CORE, RUNTIME, Path(runner.__file__), CONTEXT]}
    imports = [IMPORTS, IMPORTS, ["Lean", MODULE], ["Lean", SOLUTION_MODULE]]
    commands = {}
    files = {}
    for output, mode, manifest_file, import_list in zip(FILES, MODES, MANIFESTS, imports, strict=True):
        files[output] = {"sha256": sha_bytes(generated[output]), "mode": mode,
                         "emit_olean": mode == "emit-olean", "imports": import_list,
                         "manifest": manifest_file}
        generated[manifest_file] = encode({
            "schema_version": 1, "artifact_kind": "ap8-full-row-minor-bounded-compiler-manifest",
            "output": workspace_rel(STAGE / output), "output_sha256": sha_bytes(generated[output]),
            "imports": import_list, "input_hashes": inputs, "runtime_sha256": sha(RUNTIME),
            "mode": mode, "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
            "validated": False, "submission_ready": False,
        })
        commands[output] = ("python scripts/preflight_staged_module.py " + verification_rel(STAGE / output)
            + " --root ap8/minor --imports-manifest " + verification_rel(STAGE / manifest_file)
            + " --timeout-seconds 300" + (" --emit-olean" if mode == "emit-olean" else ""))
    generated["preparation.json"] = encode({
        "schema_version": 1, "artifact_kind": "ap8-full-row-minor-node-preparation",
        "status": "prepared-uncompiled", "source_name": NAME, "source_module": MODULE,
        "source_commit": SOURCE_COMMIT, "source_url": SOURCE_URL,
        "source_path": rel(SOURCE), "source_sha256": sha(SOURCE),
        "original_source_path": rel(ORIGINAL), "original_source_sha256": sha(ORIGINAL),
        "original_port_command_equal_modulo_line_endings": True,
        "source_byte_range": BYTE_RANGE, "source_line_range": [135, 166],
        "source_unit_sha256": sha_bytes(unit), "source_ast_unit": MODULE + ":6080",
        "source_ast_row": ast, "source_scope_row": scope, "decl_graph_row": row,
        "source_context_commands": ["open scoped BigOperators"],
        "explicit_type_and_instance_binders": "{R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]",
        "preamble": preamble.decode(), "formal_statement": formal.decode(),
        "compiled_statement_assembly_sha256": sha_bytes(target),
        "compiled_statement_equals_preamble_plus_formal_statement": True,
        "solution_source_sha256": sha_bytes(solution), "solution_module": SOLUTION_MODULE,
        "solution_name": "solution", "solution_binding": "Global top-level literal theorem solution",
        "solution_exact_source_transform": "Only the AST nameRange is replaced by solution; actual BigOperators context is retained globally. Statement binders and entire source proof bytes are unchanged.",
        "proof_body_sha256": sha_bytes(unit[6367 - 6080:]),
        "target_comparator_modecheck_only": True, "target_comparator_emits_olean": False,
        "solution_emits_olean": True, "snapshot_theorem_values_null": True,
        "snapshot_refs_policy": "Actual closed proof type/value references and Std3; no full theorem proof JSON. Same-owner helper CI is discovered from actual proof references recursively.",
        "input_hashes": inputs, "runtime_sha256": sha(RUNTIME), "files": files,
        "compile_commands": commands, "academic_metadata": metadata(),
        "single_compiler_sequential": True, "Lean_started": False, "API_used": False,
        "validated": False, "submission_ready": False, "proposal_status": "Draft",
    })
    return generated


def check_only():
    generated = stage_files()
    for output, raw in generated.items():
        need((STAGE / output).is_file() and (STAGE / output).read_bytes() == raw,
             "Exact stage reconstruction differs: " + output)
    manifests = []
    for output, manifest in zip(FILES, MANIFESTS, strict=True):
        document = read(STAGE / manifest)
        runner.verify_manifest_inputs(document)
        runner.verify_source_certificate(STAGE / output, document)
        manifests.append({"source": rel(STAGE / output), "manifest": rel(STAGE / manifest),
                          "mode": document["mode"], "emit_olean": document["emit_olean"]})
    return {"checked_files": len(generated), "all_hashes_match": True,
            "manifests": manifests, "Lean_started": False, "API_used": False,
            "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare:
        for output, raw in stage_files().items():
            path = STAGE / output
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to overwrite immutable stage: " + output)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

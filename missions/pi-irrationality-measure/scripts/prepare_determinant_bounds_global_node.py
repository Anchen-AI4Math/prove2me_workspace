"""Stage the exact source theorem determinant_bounds_inconsistent for bounded review.

Pure Python only: extracts the source AST byte range, builds a sorry comparator
and a separately named solution carrying the unchanged source proof, and writes
four <=300-second compiler manifests. It never runs Lean or calls an API.
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
STAGE = V / "ap7/determinant-bounds-global-v2"
OLD_STAGE = V / "ap7/determinant-bounds-inconsistent"
SELF = Path(__file__).resolve()
SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/Comparison.lean"
AST = V / "ast-unit-inventory.json"
GRAPH = V / "decl_graph.jsonl"
NAME = "OAI.PiExponent.determinant_bounds_inconsistent"
MODULE = "OAI.NumberTheory.PiExponent.Approximation.Comparison"
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_URL = f"https://github.com/openai/math/blob/{SOURCE_COMMIT}/lean/OAI/NumberTheory/PiExponent/Approximation/Comparison.lean#L10-L26"
IMPORTS = ["Mathlib.Tactic.Linarith", "Mathlib.Topology.Instances.Real.Lemmas"]
SOURCE_OUTPUT = "Theorems/Thm_OAI_PiExponent_determinant_bounds_inconsistent.lean"
SOLUTION_OUTPUT = "Solutions/Sol_OAI_PiExponent_determinant_bounds_inconsistent_global.lean"
SOURCE_SNAPSHOT = "SourceSnapshot.lean"
GENERATED_SNAPSHOT = "GeneratedSnapshotWithRefs.lean"
SNAPSHOT_CORE = V / "TypedSnapshotCore.inc"
OLD_TARGET = OLD_STAGE / SOURCE_OUTPUT
OLD_SOLUTION = OLD_STAGE / "Solutions/Sol_OAI_PiExponent_determinant_bounds_inconsistent.lean"
OLD_SOLUTION_PREFLIGHT = OLD_SOLUTION.with_suffix(".lean.preflight.json")
OLD_SOLUTION_OLEAN = V / "staged-build/lib/lean/Solutions/Sol_OAI_PiExponent_determinant_bounds_inconsistent.olean"
OLD_GENERATED_SNAPSHOT = OLD_STAGE / "GeneratedSnapshotWithRefs.lean"
OLD_GENERATED_SNAPSHOT_PREFLIGHT = OLD_GENERATED_SNAPSHOT.with_suffix(".lean.preflight.json")


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.relative_to(TASK).as_posix()


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def write_exact(path: Path, raw: bytes) -> None:
    if path.exists():
        need(path.read_bytes() == raw, "Refusing to overwrite differing evidence: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def source_unit() -> bytes:
    ast = read(AST)
    module = next(x for x in ast["modules"] if x["module"] == MODULE)
    unit = next(x for x in module["units"] if x["nameText"] == "determinant_bounds_inconsistent")
    need(unit["graph_names"] == [NAME] and unit["graph_kinds"] == ["theorem"],
         "Exact source AST identity changed")
    raw = SOURCE.read_bytes()[unit["start"]["offset"]:unit["end"]["offset"]]
    need((raw.startswith(b"theorem determinant_bounds_inconsistent\n") or
          raw.startswith(b"theorem determinant_bounds_inconsistent\r\n")) and raw.find(b" := by") > 0,
         "Exact theorem source slice or proof separator changed")
    return raw


def graph_row():
    rows = [json.loads(line) for line in GRAPH.read_text(encoding="utf-8").splitlines() if line]
    row = next(x for x in rows if x["name"] == NAME)
    need(row["module"] == MODULE and row["kind"] == "theorem" and
         row["typeDeps"] == [] and row["valueDeps"] == [],
         "Source graph no longer confirms the theorem is self-contained")
    return row


def assembly():
    source = source_unit()
    separator = source.find(b" := by")
    statement = source[:separator] + b" := by\n  sorry"
    solution = source.replace(b"theorem determinant_bounds_inconsistent", b"theorem solution", 1)
    need(solution != source and solution.count(b"theorem solution") == 1,
         "Could not rename only the declaration binder for the solution module")
    imports = "".join(f"import {module}\n" for module in IMPORTS) + "\n"
    context_open = "namespace OAI\nnamespace PiExponent\nopen Filter Topology\n\n"
    context_close = "\n\nend PiExponent\nend OAI\n"
    preamble = (imports + context_open).encode("utf-8")
    formal_statement = statement + context_close.encode("utf-8")
    target_bytes = preamble + formal_statement
    need(target_bytes == preamble + formal_statement, "Target assembly invariant failed")
    global_solution_preamble = (imports + "open Filter Topology\n\n").encode("utf-8")
    solution_bytes = global_solution_preamble + solution
    old_target = OLD_STAGE / SOURCE_OUTPUT
    need(old_target.is_file() and old_target.read_bytes() == target_bytes,
         "Global variant target bytes differ from the preserved original namespace-framed target")
    return preamble, formal_statement, target_bytes, solution_bytes


PROBE = r'''
open Lean Meta

namespace DeterminantBoundsSnapshot

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
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid module owner index: {name}"
    pure <| Json.mkObj [("kind", toJson "ImportedModule"),
      ("moduleIndex", toJson i.toNat), ("module", toJson owner.toString)]

def exportEvidence (side output name : String) : MetaM Unit := do
  let env ← getEnv
  let declName := name.toName
  let some ci := env.find? declName | throwError "Missing theorem CI: {declName}"
  let some value := valueOf ci | throwError "Theorem CI has no proof value: {declName}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Theorem type is not closed"
  if value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Theorem value is not closed"
  let axioms ← Lean.collectAxioms declName
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Proof has axioms outside Std3"
  let used := refs value
  let helperPrefix := declName.toString ++ "._proof_"
  let helpers := used.filter (fun n => n.toString.startsWith helperPrefix)
  let mut helperRows : Array Json := #[]
  for helperName in helpers do
    let some helperCI := env.find? helperName | throwError "Missing inline proof CI: {helperName}"
    let some helperValue := valueOf helperCI | throwError "Inline proof CI has no value: {helperName}"
    if helperCI.type.hasMVar || helperCI.type.hasFVar || helperCI.type.hasLooseBVars ||
       helperValue.hasMVar || helperValue.hasFVar || helperValue.hasLooseBVars then
      throwError "Inline proof CI is not closed: {helperName}"
    let helperAxioms ← Lean.collectAxioms helperName
    unless helperAxioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Inline proof uses axioms outside Std3: {helperName}"
    let helperOwner ← ownerOf env helperName
    helperRows := helperRows.push <| Json.mkObj [
      ("name", toJson helperName.toString),
      ("levelParams", toJson (helperCI.levelParams.map Name.toString)),
      ("closedType", toJson true), ("closedValue", toJson true),
      ("type", PiExponentInterfaceSnapshot.exprJson helperCI.type),
      ("value", PiExponentInterfaceSnapshot.exprJson helperValue),
      ("typeRefs", toJson ((refs helperCI.type).map Name.toString)),
      ("valueRefs", toJson ((refs helperValue).map Name.toString)),
      ("axioms", toJson ((helperAxioms.map Name.toString).qsort (fun a b => a < b))),
      ("owner", helperOwner)]
  let owner ← ownerOf env declName
  let row := Json.mkObj [
    ("name", toJson declName.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson (used.map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner), ("automaticInlineHelpers", Json.arr helperRows)]
  let report := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString), ("theorem", row)]
  IO.FS.writeFile output report.compress

end DeterminantBoundsSnapshot
'''


def source_snapshot_bytes() -> bytes:
    prefix = "import Lean\nimport " + MODULE + "\n\n"
    exporter = PROBE + '\nrun_meta do\n  DeterminantBoundsSnapshot.exportEvidence "source" "' + \
        (TASK.relative_to(ROOT) / rel(STAGE) / "source-proof-references.json").as_posix() + '" "' + NAME + '"\n'
    # Keep the typed serializer and the source theorem's actual axiom report in this bounded probe.
    exp = '\n\nset_option pp.universes true\nset_option pp.fullNames true\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`' + NAME + '] "' + \
        (TASK.relative_to(ROOT) / rel(STAGE) / "source-type.json").as_posix() + '"\n'
    return (prefix + SNAPSHOT_CORE.read_text(encoding="utf-8") + exp + "#print axioms " + NAME + "\n" + exporter).encode("utf-8")


def generated_snapshot_bytes() -> bytes:
    imports = "import Lean\nimport Solutions.Sol_OAI_PiExponent_determinant_bounds_inconsistent_global\n\n"
    exp = '\n\nset_option pp.universes true\nset_option pp.fullNames true\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`solution] "' + \
        (TASK.relative_to(ROOT) / rel(STAGE) / "generated-type.json").as_posix() + '"\n'
    exporter = PROBE + '\nrun_meta do\n  DeterminantBoundsSnapshot.exportEvidence "generated" "' + \
        (TASK.relative_to(ROOT) / rel(STAGE) / "generated-proof-references.json").as_posix() + '" "solution"\n'
    return (imports + SNAPSHOT_CORE.read_text(encoding="utf-8") + exp + "#print axioms solution\n" + exporter).encode("utf-8")


def metadata():
    statement = (
        "For real numbers \\(\\nu,\\theta,x,b,e_{\\rm ar},e_{\\rm an},e_{\\rm r},c,d\\), the following hypotheses are inconsistent:\n\n"
        "$$\\begin{aligned}\n"
        "1&<\\nu,\\qquad 0\\le b\\le\\theta,\\\\\n"
        "e_{\\rm ar}+e_{\\rm an}+e_{\\rm r}&<\\nu(x-\\theta)-(1-\\theta),\\\\\n"
        "1+e_{\\rm ar}+e_{\\rm an}+e_{\\rm r}&<c,\\\\\n"
        "-(1-b)-e_{\\rm ar}&\\le d\\le e_{\\rm an}+e_{\\rm r}+\\max\\{-c,-\\nu(x-b)\\}.\n"
        "\\end{aligned}$$\n\n"
        "The result isolates the contradiction between a lower determinant estimate and the competing analytic/collision upper estimate."
    )
    return {
        "title": "Incompatible determinant bounds",
        "statement": statement,
        "explanation": "The theorem shows that the stated arithmetic lower bound and analytic/collision upper bound cannot hold simultaneously. It is a self-contained real-inequality step used inside the campaign's determinant contradiction; it introduces no new approximation measure or additional mathematical assumptions.",
        "tags": ["number-theory", "analysis", "openai-pi-exponent-017"],
        "source_commit": SOURCE_COMMIT,
        "source_url": SOURCE_URL,
    }


def build_plan():
    preamble, formal, target, solution = assembly()
    row = graph_row()
    source_hash = sha(SOURCE)
    ast_inventory = read(AST)
    module = next(x for x in ast_inventory["modules"] if x["module"] == MODULE)
    unit = next(x for x in module["units"] if x["nameText"] == "determinant_bounds_inconsistent")
    runtime = runner.validate_runtime()[1]
    core_hash = sha(SNAPSHOT_CORE)
    source_snap = source_snapshot_bytes()
    generated_snap = generated_snapshot_bytes()
    files = {
        SOURCE_OUTPUT: {"bytes": target, "imports": IMPORTS, "mode": "modecheck", "emit_olean": False},
        SOLUTION_OUTPUT: {"bytes": solution, "imports": IMPORTS, "mode": "emit-olean", "emit_olean": True},
        SOURCE_SNAPSHOT: {"bytes": source_snap, "imports": ["Lean", MODULE], "mode": "modecheck", "emit_olean": False},
        GENERATED_SNAPSHOT: {"bytes": generated_snap, "imports": ["Lean", "Solutions.Sol_OAI_PiExponent_determinant_bounds_inconsistent_global"], "mode": "modecheck", "emit_olean": False},
    }
    input_hashes = {
        rel(SOURCE): source_hash,
        rel(AST): sha(AST),
        rel(GRAPH): sha(GRAPH),
        rel(SNAPSHOT_CORE): core_hash,
        rel(TASK / "scripts/preflight_staged_module.py"): sha(TASK / "scripts/preflight_staged_module.py"),
        rel(TASK / "platform/source-theorem-name-overrides.json"): sha(TASK / "platform/source-theorem-name-overrides.json"),
        rel(OLD_TARGET): sha(OLD_TARGET),
        rel(OLD_SOLUTION): sha(OLD_SOLUTION),
        rel(OLD_SOLUTION_PREFLIGHT): sha(OLD_SOLUTION_PREFLIGHT),
        rel(OLD_SOLUTION_OLEAN): sha(OLD_SOLUTION_OLEAN),
        rel(OLD_GENERATED_SNAPSHOT): sha(OLD_GENERATED_SNAPSHOT),
        rel(OLD_GENERATED_SNAPSHOT_PREFLIGHT): sha(OLD_GENERATED_SNAPSHOT_PREFLIGHT),
        rel(TASK / read(OLD_GENERATED_SNAPSHOT_PREFLIGHT)["log"]): read(OLD_GENERATED_SNAPSHOT_PREFLIGHT)["log_sha256"],
        rel(TASK / "scripts/prepare_determinant_bounds_node.py"): sha(TASK / "scripts/prepare_determinant_bounds_node.py"),
        rel(TASK / "scripts/certify_determinant_bounds_node_existing.py"): sha(TASK / "scripts/certify_determinant_bounds_node_existing.py"),
    }
    manifests = {}
    outputs = {}
    for path, spec in files.items():
        out = STAGE / path
        raw = spec["bytes"]
        outputs[path] = {"sha256": sha_bytes(raw), "mode": spec["mode"], "emit_olean": spec["emit_olean"], "imports": spec["imports"]}
        manifests[path] = {
            "schema_version": 1,
            "artifact_kind": "determinant-bounds-bounded-compiler-manifest",
            "output": (TASK / rel(out)).relative_to(ROOT).as_posix(),
            "output_sha256": sha_bytes(raw),
            "imports": spec["imports"],
            "input_hashes": input_hashes,
            "runtime_sha256": runtime,
            "mode": spec["mode"],
            "emit_olean": spec["emit_olean"],
            "timeout_seconds": 300,
            "node_validated": False,
            "Lean_started": False,
            "submission_ready": False,
        }
    formal_text = formal.decode("utf-8")
    preamble_text = preamble.decode("utf-8")
    need(target == (preamble_text + formal_text).encode("utf-8"), "Compiled theorem bytes do not equal preamble + formal_statement")
    return {
        "schema_version": 1,
        "artifact_kind": "ap7-exact-source-determinant-bounds-node-preparation",
        "status": "prepared-uncompiled",
        "source_name": NAME,
        "solution_name": "solution",
        "source_module": MODULE,
        "source_commit": SOURCE_COMMIT,
        "source_url": SOURCE_URL,
        "source_path": rel(SOURCE),
        "source_sha256": source_hash,
        "source_ast_unit": f"{MODULE}:{unit['start']['offset']}",
        "source_byte_range": [unit["start"]["offset"], unit["end"]["offset"]],
        "source_line_range": [unit["start"]["line"], unit["end"]["line"]],
        "source_unit_sha256": sha_bytes(source_unit()),
        "decl_graph_row": row,
        "declared_dependencies": {"type": [], "value": [], "inline_helpers": []},
        "platform_name_override": None,
        "platform_collision_check": "source theorem override inventory has no row for this source name",
        "preamble": preamble_text,
        "formal_statement": formal_text,
        "compiled_statement_assembly_sha256": sha_bytes(target),
        "solution_source_sha256": sha_bytes(solution),
        "solution_exact_source_transform": "Exact AST theorem unit bytes from the pinned source, with only the leading declaration identifier renamed to solution; the source theorem's namespace wrapper is removed, the exact open Filter Topology context is retained, and the proof body and binder/type bytes are unchanged.",
        "solution_binding": "Global top-level theorem solution, required by the platform; it is emitted under a fresh _global solution module identity.",
        "academic_metadata": metadata(),
        "runtime_sha256": runtime,
        "input_hashes": input_hashes,
        "files": outputs,
        "compile_commands": {path: f"python scripts/preflight_staged_module.py {rel(STAGE / path)} --root {rel(STAGE)} --imports-manifest {rel(STAGE / (Path(path).name + '.json'))} --timeout-seconds 300" + (" --emit-olean" if spec["emit_olean"] else "") for path, spec in files.items()},
        "compiled_statement_equals_preamble_plus_formal_statement": True,
        "target_comparator_modecheck_only": True,
        "target_comparator_emits_olean": False,
        "solution_emits_olean": True,
        "solution_module": "Solutions.Sol_OAI_PiExponent_determinant_bounds_inconsistent_global",
        "preserved_namespaced_stage": {
            "stage": rel(OLD_STAGE),
            "target_source_sha256": sha(OLD_TARGET),
            "namespaced_solution_sha256": sha(OLD_SOLUTION),
            "namespaced_solution_preflight_sha256": sha(OLD_SOLUTION_PREFLIGHT),
            "namespaced_solution_olean": rel(OLD_SOLUTION_OLEAN),
            "namespaced_solution_olean_sha256": sha(OLD_SOLUTION_OLEAN),
            "failed_generated_snapshot": rel(OLD_GENERATED_SNAPSHOT),
            "failed_generated_snapshot_preflight": rel(OLD_GENERATED_SNAPSHOT_PREFLIGHT),
            "failed_generated_snapshot_preflight_sha256": sha(OLD_GENERATED_SNAPSHOT_PREFLIGHT),
            "failed_generated_snapshot_log": read(OLD_GENERATED_SNAPSHOT_PREFLIGHT)["log"],
            "failed_generated_snapshot_log_sha256": read(OLD_GENERATED_SNAPSHOT_PREFLIGHT)["log_sha256"],
            "new_solution_olean_module_is_distinct": True,
            "target_bytes_unchanged": True},
        "single_compiler_sequential": True,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }, files, manifests


def check_only():
    plan, files, manifests = build_plan()
    prep_path = STAGE / "preparation.json"
    need(read(prep_path) == plan, "Preparation record differs from deterministic source reconstruction")
    write_expect = {"manifest.json": plan, "preparation.json": plan}
    for path, spec in files.items():
        write_expect[path] = spec["bytes"]
        write_expect[Path(path).name + ".json"] = manifests[path]
    for name, expected in write_expect.items():
        target = STAGE / name
        if isinstance(expected, bytes):
            need(target.read_bytes() == expected, "Staged source bytes changed: " + name)
        else:
            need(read(target) == expected, "Staged JSON changed: " + name)
    need(read(STAGE / "academic-metadata.json") == plan["academic_metadata"], "Academic metadata changed")
    need((STAGE / "wire-theorem-source.lean").read_bytes() ==
         (plan["preamble"] + plan["formal_statement"]).encode("utf-8"), "Exact wire theorem assembly changed")
    for path, spec in files.items():
        source = STAGE / path
        manifest = manifests[path]
        runner.verify_manifest_inputs(manifest)
        runner.verify_source_certificate(source, manifest)
        need(runner.certified_imports(source, manifest) == spec["imports"], "Manifest imports differ: " + path)
    return {"prepared": True, "stage": rel(STAGE), "outputs": {p: x["sha256"] for p, x in plan["files"].items()},
            "Lean_started": False, "API_used": False, "validated": False}


def prepare():
    plan, files, manifests = build_plan()
    for path, spec in files.items():
        write_exact(STAGE / path, spec["bytes"])
        write_exact(STAGE / (Path(path).name + ".json"), (json.dumps(manifests[path], indent=2, ensure_ascii=False) + "\n").encode())
    write_exact(STAGE / "manifest.json", (json.dumps(plan, indent=2, ensure_ascii=False) + "\n").encode())
    write_exact(STAGE / "preparation.json", (json.dumps(plan, indent=2, ensure_ascii=False) + "\n").encode())
    write_exact(STAGE / "academic-metadata.json", (json.dumps(plan["academic_metadata"], indent=2, ensure_ascii=False) + "\n").encode())
    write_exact(STAGE / "wire-theorem-source.lean", (plan["preamble"] + plan["formal_statement"]).encode())
    return check_only()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check_only(), indent=2))

"""Stage paired actual-CI probes for three compiler-generated proof references.

The requests come from the successful generated proof-reference export. The
source and generated parent declarations are reconstructed from frozen AST
components. Two new probes run in separate <=300s Lean files; this script
does no compilation or API call and preserves all previous attempts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import generate_equation_provenance_probe as equations
import prepare_dimension_margin_node as base
import prepare_dimension_margin_node_repair as repair
import preflight_staged_module as runner

TASK, ROOT, V = base.TASK, base.ROOT, base.V
OLD = base.STAGE
STAGE = V / "dm-extra-ci"
SELF = Path(__file__).resolve()
PARENTS = ["OAI.PiExponent.tendsto_nat_add_one_div_pow",
           "OAI.PiExponent.dimensionW", "OAI.PiExponent.dimensionV"]
EXTRAS = ["OAI.PiExponent.tendsto_nat_add_one_div_pow._simp_1_1",
          "OAI.PiExponent.dimensionW.eq_1", "OAI.PiExponent.dimensionV._proof_1"]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text(encoding="utf-8"))
def rel(path): return path.relative_to(TASK).as_posix()


def need(ok, message):
    if not ok: raise ValueError(message)


def put_exact(path, raw):
    if path.exists(): need(path.read_bytes() == raw, "Existing extra-CI evidence differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


PROBE = r'''
namespace DimensionMarginExtraCI
open Lean Meta

def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)

def export (side output : String) : MetaM Unit := do
  let env ← getEnv
  let parent ← getConstInfo `OAI.PiExponent.tendsto_nat_add_one_div_pow
  let .thmInfo theoremInfo := parent
    | throwError "Expected actual inline theorem parent"
  let theoremRefs := refs theoremInfo.value
  unless theoremRefs.contains "OAI.PiExponent.tendsto_nat_add_one_div_pow._simp_1_1" do
    throwError "Automatic simp helper is not literal in actual parent proof"
  let primaryV ← getConstInfo `OAI.PiExponent.dimensionV
  let .defnInfo d := primaryV | throwError "Expected actual dimensionV Definition"
  let definitionRefs := refs d.value
  unless definitionRefs.contains "OAI.PiExponent.dimensionV._proof_1" do
    throwError "Automatic proof helper is not literal in full Definition value"
  let primaryW := `OAI.PiExponent.dimensionW
  let equations? ← Lean.Meta.getEqnsFor? primaryW
  let names := equations?.getD #[]
  unless names.contains `OAI.PiExponent.dimensionW.eq_1 do
    throwError "Actual dimensionW equation getter omitted required referenced CI"
  let inverse? ← Lean.Meta.isEqnThm? `OAI.PiExponent.dimensionW.eq_1
  unless inverse? == some primaryW do
    throwError "Actual equation inverse primary differs"
  let result := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("sourceDerivedFrom", toJson "actual-primitive-proof-reference-set"),
    ("theoremParent", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.tendsto_nat_add_one_div_pow),
    ("theoremParentValueRefs", toJson theoremRefs),
    ("simpHelper", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.tendsto_nat_add_one_div_pow._simp_1_1),
    ("definitionWParent", ← PiExponentEquationProvenanceProbe.checkedCI primaryW),
    ("definitionWEquationNames", toJson (names.map Name.toString)),
    ("definitionWEquationInverse", toJson (inverse?.map Name.toString)),
    ("dimensionWEquation", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionW.eq_1),
    ("definitionVParent", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionV),
    ("definitionVFullValueRefs", toJson definitionRefs),
    ("dimensionVHelper", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionV._proof_1),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end DimensionMarginExtraCI
'''.replace("def export (", "def exportExtra (")


def authority():
    m = base.inputs()
    repair.check()
    pf = read(repair.NEW.with_suffix(".lean.preflight.json"))
    need(pf["exit_code"] == 0 and pf["timed_out"] is False and 0 < pf["seconds"] <= 300,
         "Repaired exact generated proof-reference run not successful")
    refs = read(OLD / "proof-references.json")
    rows = {r["name"]: r for r in refs["rows"]}
    need(set(EXTRAS) <= set().union(*(set(x["valueRefs"]) for x in rows.values())),
         "Extra requests are not actual generated proof references")
    need(EXTRAS[0] in rows[PARENTS[0]]["valueRefs"]
         and EXTRAS[1] in rows["OAI.PiExponent.dimensionK_div_W_le"]["valueRefs"]
         and EXTRAS[2] in rows["OAI.PiExponent.dimensionV_geometric_lower"]["valueRefs"],
         "Extra CI literal parent references differ")
    requests = {r["source_graph_name"]: r for r in m["public_inline_ci_requests"]}
    need(requests[PARENTS[0]]["source_unit"] == "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:115",
         "Parent source AST unit differs")
    defs = m["definition_dependency_witnesses"][0]
    need(set(defs["selected_units"]) >= {
        "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400",
        "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460"}, "Definition parent AST units differ")
    return m, pf, refs


def render(side):
    m, pf, refs = authority()
    if side == "original":
        imports = ["Lean", "Lean.Meta.Eqns", base.MODULE]
        head = "".join("import " + x + "\n" for x in imports) + "\n"
    elif side == "generated":
        imports = sorted(set(["Lean.Meta.Eqns", *m["imports"]]))
        frozen = (OLD / Path(m["statement"]).name).read_bytes()
        skeleton = m["mathematical_preamble"].encode("utf-8")
        need(frozen.startswith(skeleton), "Generated source does not begin with exact public skeleton")
        need(b"sorry" not in skeleton, "Generated helper skeleton contains target sorry")
        head = "".join("import " + x + "\n" for x in imports)
        # Only the already imported module declarations are removed from the
        # copied skeleton; all seven source command bytes and scopes stay exact.
        first_decl = skeleton.find(b"\nsection\n")
        need(first_decl > 0, "Cannot locate frozen first source section")
        head += skeleton[first_decl:].decode("utf-8") + m["scope_closing"] + "\n"
    else: raise ValueError("Unexpected probe side")
    core = (V / "TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
    out = (STAGE / (side + "-extra.json")).relative_to(ROOT).as_posix()
    source = head + core + equations.PROBE + PROBE + "\nrun_meta do\n  DimensionMarginExtraCI.exportExtra " + json.dumps(side) + " " + json.dumps(out) + "\n"
    return source.encode("utf-8"), imports


def plan():
    m, pf, refs = authority()
    inputs = {rel(p): sha(p) for p in [SELF, Path(base.__file__), Path(repair.__file__),
              Path(equations.__file__), OLD / "manifest.json", OLD / Path(m["statement"]).name,
              OLD / "proof-references.json", repair.NEW.with_suffix(".lean.preflight.json"),
              V / "TypeOnlyTheoremSnapshotCore.inc", V / "decl_graph.jsonl"]}
    definition = base.dimension_interface(m)
    inputs[definition["certificate"]] = definition["certificate_sha256"]
    inputs[definition["output_olean"]] = definition["output_olean_sha256"]
    for row in m["source_components"]:
        for field in ("source", "facts", "original_source"):
            inputs[Path(row[field]).relative_to("missions/pi-irrationality-measure").as_posix()] = row[field + "_sha256"]
    files = {}
    for side, name in (("original", "ProbeOriginal"), ("generated", "ProbeGenerated")):
        raw, imports = render(side)
        path = STAGE / (name + ".lean")
        files[name] = {"side": side, "source": rel(path), "source_sha256": hashlib.sha256(raw).hexdigest(),
                       "manifest": rel(STAGE / (side + ".json")), "imports": imports}
    return {"schema_version": 1, "artifact_kind": "dimension-margin-extra-ci-preparation",
            "node": base.KEY, "source_commit": m["source_commit"],
            "parents": PARENTS, "actual_generated_reference_names": EXTRAS,
            "definition": definition, "input_hashes": inputs,
            "runtime_sha256": m["runtime_sha256"], "files": files,
            "Lean_started": False, "validated": False, "submission_ready": False}


def manifests(p):
    return {name: {"schema_version": 1, "artifact_kind": "dimension-margin-extra-ci-file-import-certificate",
            "output": (TASK / row["source"]).relative_to(ROOT).as_posix(),
            "output_sha256": row["source_sha256"], "imports": row["imports"],
            "input_hashes": p["input_hashes"], "runtime_sha256": p["runtime_sha256"],
            "timeout_seconds": 300, "node_validated": False,
            "Lean_started": False, "submission_ready": False} for name, row in p["files"].items()}


def prepare():
    p = plan()
    docs = manifests(p)
    for name, row in p["files"].items():
        raw, _ = render(row["side"])
        put_exact(TASK / row["source"], raw)
        put_exact(TASK / row["manifest"], (json.dumps(docs[name], indent=2, ensure_ascii=False) + "\n").encode())
    put_exact(STAGE / "preparation.json", (json.dumps(p, indent=2, ensure_ascii=False) + "\n").encode())
    return check()


def check():
    p = plan()
    need(read(STAGE / "preparation.json") == p, "Extra-CI preparation changed")
    docs = manifests(p)
    for name, row in p["files"].items():
        source, mp = TASK / row["source"], TASK / row["manifest"]
        raw, _ = render(row["side"])
        need(source.read_bytes() == raw and read(mp) == docs[name], "Exact extra-CI probe source/manifest differs")
        runner.verify_manifest_inputs(docs[name])
        runner.verify_source_certificate(source, docs[name])
        need(runner.certified_imports(source, docs[name]) == row["imports"], "Probe imports differ")
    return {"prepared": True, "stage": rel(STAGE), "files": p["files"],
            "Lean_started": False, "validated": False, "submission_ready": False}


if __name__ == "__main__":
    a = argparse.ArgumentParser(description=__doc__)
    mode = a.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = a.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2))

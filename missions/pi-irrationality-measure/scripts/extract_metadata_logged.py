"""Resume exact Lean metadata extraction only after the full build and axiom gates pass."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from validate_ast_facts import validate_facts

sys.stdout.reconfigure(encoding="utf-8")
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--priority", action="append", default=[],
                    help="Extract an explicit port/lean relative module before the remaining sorted files")
parser.add_argument("--only", action="append", default=[],
                    help="Extract only these exact modules for a serial intermediate stage; never mark an incomplete tree complete")
args = parser.parse_args()
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
state_path = DEST / "extraction-state.json"
preflight_script = TASK / "scripts/preflight_logged.py"
graph_script = DEST / "extract_decl_graph.lean"
oracle = DEST / "TargetAxioms/SketchOracle.lean"
oracle_runner = DEST / "RunSketchOracle.lean"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

build = json.loads((DEST / "latest-build.json").read_text(encoding="utf-8"))
if build["exit_code"] != 0:
    raise SystemExit("The complete mission build must succeed before extracting the upload tree")
log = (ROOT / build["log"]).read_text(encoding="utf-8")
trusted = {"propext", "Classical.choice", "Quot.sound"}
targets = ["OAI.PiExponent.pi_eventual_lower_bound",
           "OAI.PiExponent.pi_integer_eventual_lower_bound",
           "OAI.PiExponent.pi_irrationalityExponent_eq_two",
           "OAI.PiExponent.main",
           "OAI.PiExponent.pi_approximation_determinant_sequences"]
for name in targets:
    prefix = f"'{name}' depends on axioms: ["
    audits = [line[line.index(prefix):] for line in log.splitlines() if prefix in line]
    if not audits:
        raise SystemExit(f"No clean axiom audit found for {name}")
    for line in audits:
        axioms = {x.strip() for x in line[len(prefix):].removesuffix("]").split(",") if x.strip()}
        if not axioms <= trusted:
            raise SystemExit(f"Unexpected axioms in {name}: {sorted(axioms - trusted)}")
integration_audits = [line for line in log.splitlines()
                      if "Sol_PiIrrationality_openai_bound_two_transfer.lean" in line
                      and "'solution' depends on axioms:" in line]
if not integration_audits or any(
        "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" not in line
        for line in integration_audits):
    raise SystemExit("The platform integration solution must also have its axiom audit")
files = sorted((TASK / "port/lean").rglob("*.lean"))
inputs = {p.relative_to(ROOT).as_posix(): digest(p) for p in files}
validated = json.loads((DEST / "validated-port-manifest.json").read_text(encoding="utf-8"))
for source in files:
    relative = source.relative_to(TASK / "port/lean").as_posix()
    if inputs[source.relative_to(ROOT).as_posix()] != validated["port_files_sha256"][relative]:
        raise SystemExit(f"The proof tree changed after its full validation: {relative}")
inputs[graph_script.relative_to(ROOT).as_posix()] = digest(graph_script)
inputs[oracle.relative_to(ROOT).as_posix()] = digest(oracle)
inputs[oracle_runner.relative_to(ROOT).as_posix()] = digest(oracle_runner)
input_key = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
state = json.loads(state_path.read_text(encoding="utf-8")) if state_path.exists() else {}
if state.get("input_key") != input_key:
    state = {"input_key": input_key, "inputs": inputs, "build_gate": build,
             "stage1": None, "stage2": {}}

def save():
    state["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    state_path.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")

def run_preflight(mode, source):
    save()
    latest = DEST / ("latest-sketch.json" if mode == "--sketch" else "latest-preflight.json")
    before = latest.read_bytes() if latest.exists() else None
    result = subprocess.run([sys.executable, str(preflight_script), mode, source], cwd=ROOT)
    after = latest.read_bytes() if latest.exists() else None
    expected_source = ((TASK / "port/lean" / source) if mode == "--sketch"
                       else DEST / source).relative_to(ROOT).as_posix()
    if after is None or after == before:
        state["last_failure"] = {"source": expected_source, "exit_code": result.returncode or 1,
                                 "phase": "preflight_setup", "compilation_result_available": False,
                                 "reason": "No fresh preflight record was emitted; preserve previous successful results",
                                 "at_utc": datetime.now(timezone.utc).isoformat()}
        save()
        raise SystemExit(result.returncode or 1)
    record = json.loads(latest.read_text(encoding="utf-8"))
    if record["source"] != expected_source:
        raise SystemExit("The preflight record belongs to another input; it cannot certify this file")
    if result.returncode != 0 or record["exit_code"] != 0 or not record["source_unchanged"]:
        state["last_failure"] = record
        save()
        raise SystemExit(result.returncode or 1)
    state.pop("last_failure", None)
    return record

graph_path = DEST / "decl_graph.jsonl"
if not state["stage1"] or not graph_path.exists() or digest(graph_path) != state["stage1"]["facts_sha256"]:
    record = run_preflight("--verification", graph_script.name)
    rows = [json.loads(line) for line in graph_path.read_text(encoding="utf-8").splitlines()]
    names = {row["name"] for row in rows}
    if not set(targets) <= names:
        raise SystemExit("The declaration graph omitted a required source target")
    state["stage1"] = {"preflight": record, "facts_sha256": digest(graph_path), "declarations": len(rows)}
    save()
    print(f"Stage 1: {len(rows)} project declarations", flush=True)

by_relative = {p.relative_to(TASK / "port/lean").as_posix(): p for p in files}
if any(relative not in by_relative for relative in args.priority + args.only):
    raise SystemExit("A priority module must belong to the immutable validated input tree")
priority = list(dict.fromkeys(args.priority))
ordered_files = [by_relative[relative] for relative in priority]
ordered_files += [p for p in files if p.relative_to(TASK / "port/lean").as_posix() not in priority]
if args.only:
    ordered_files = [p for p in ordered_files if p.relative_to(TASK / "port/lean").as_posix() in args.only]
for source in ordered_files:
    key = source.relative_to(TASK / "port/lean").as_posix()
    previous = state["stage2"].get(key)
    if previous and (ROOT / previous["facts"]).exists() and digest(ROOT / previous["facts"]) == previous["facts_sha256"]:
        continue
    print(f"Stage 2 [{len(state['stage2']) + 1}/{len(files)}]: {key}", flush=True)
    record = run_preflight("--sketch", key)
    fact_path = ROOT / record["log"]
    facts = [json.loads(line) for line in fact_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    positions = validate_facts(source, facts, record["source_sha256"])
    state["stage2"][key] = {"preflight": record, "facts": fact_path.relative_to(ROOT).as_posix(),
                          "facts_sha256": digest(fact_path), "fact_count": len(facts),
                          "raw_byte_validation": positions}
    save()
state["complete"] = set(state["stage2"]) == set(by_relative)
save()
print(f"Authoritative facts: {len(state['stage2'])}/{len(files)}; complete={state['complete']}", flush=True)

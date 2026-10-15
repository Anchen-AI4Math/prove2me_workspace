"""Pure AP11 staging of the original grouped collision-rate proof.

This script only reads source/certificates and writes immutable stage inputs. It
does not run Lean, call Prove2Me, or read credentials. The root agent owns the
four sequential 300-second compiler preflights and any later publication.
"""
from __future__ import annotations

import argparse
import gc
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner
import stage_core_parent_data_providers as ap10
import stage_full_row_minor_node as ap8
import stage_weighted_simplex_domains_providers as ap9

TASK, ROOT, V = ap9.TASK, ap9.ROOT, ap9.V
SELF = Path(__file__).resolve()
STAGE = V / "ap11/collision-rate"
COMMIT = ap9.COMMIT
AST, SCOPES, GRAPH, RUNTIME, SNAPSHOT_CORE = ap9.AST, ap9.SCOPES, ap9.GRAPH, ap9.RUNTIME, ap8.SNAPSHOT_CORE
TARGET = "OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate"
TARGET_MODULE = "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_ap11_global"
TARGET_OUTPUT = "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate.lean"
SOLUTION_OUTPUT = SOLUTION_MODULE.replace(".", "/") + ".lean"
SOURCE_SNAPSHOT, GENERATED_SNAPSHOT = "SourceSnapshot.lean", "GeneratedSnapshot.lean"
SOURCE_TYPE_JSON, GENERATED_TYPE_JSON = "source-types.json", "generated-types.json"
SOURCE_REFS_JSON, GENERATED_REFS_JSON = "source-proof-references.json", "generated-proof-references.json"
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MANIFESTS = [f"c{i}.json" for i in range(1, 5)]
MODES = ["modecheck", "emit-olean", "modecheck", "modecheck"]

# The exact graph closure is checked below. These are the source commands that
# remain after the actual published and AP9/AP10 provider declaration sets are
# subtracted; each group is emitted in original source order and scope.
HELPER_NAMES = {
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting": [
        "natWeightedSimplex", "mem_natWeightedSimplex", "residueRectangle",
        "mem_residueRectangle", "card_residueRectangle", "simplex_count_lower_sandwich",
        "simplex_count_upper_sandwich", "natWeightedSimplex_one",
        "tendsto_card_natWeightedSimplex", "mem_realWeightedSimplex",
        "mem_strictWeightedSimplex", "realWeightedSimplex_scaled",
        "tendsto_card_realWeightedSimplex_scaled",
        "tendsto_card_strictWeightedSimplex_scaled",
    ],
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights": [
        "positive_rational_weights_common_denominator",
    ],
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational": [
        "common_denominator_simplex_constant",
        "tendsto_card_realWeightedSimplex_rational",
        "tendsto_card_strictWeightedSimplex_rational",
    ],
    "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix": ["row_card"],
    "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic": ["ceil_log_weight_pos"],
    "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting": [
        "rowCount", "lowIndexCount", "rationalLogWeights",
        "rationalLogWeights_cast", "rationalLogWeights_pos",
        "tendsto_rowCount_normalized", "tendsto_lowIndexCount_normalized",
        "tendsto_row_lowIndex_ratio", "tendsto_collisionRatio",
    ],
    TARGET_MODULE: ["finiteDenominators_two_le"],
}
PREFIXES = {
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting": "OAI.PiExponent.",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights": "OAI.PiExponent.",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational": "OAI.PiExponent.",
    "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix": "OAI.PiExponent.InterpolationMatrix.",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic": "OAI.PiExponent.MatrixArithmetic.",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting": "OAI.PiExponent.MatrixCounting.",
    TARGET_MODULE: "OAI.PiExponent.DeterminantContradiction.",
}
GROUP_HEADERS = {
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting": b"namespace OAI\n\nopen scoped BigOperators\n\nnamespace PiExponent\n\n",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights": b"namespace OAI\n\nopen scoped BigOperators\n\nnamespace PiExponent\n\n",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational": b"namespace OAI\n\nopen scoped BigOperators\nopen Filter Topology\n\nnamespace PiExponent\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix": b"namespace OAI\n\nopen scoped BigOperators\n\nnamespace PiExponent.InterpolationMatrix\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic": b"namespace OAI\n\nnamespace PiExponent\n\nopen scoped BigOperators\n\nnamespace MatrixArithmetic\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting": b"namespace OAI\n\nopen scoped BigOperators\nopen Filter Topology\n\nnamespace PiExponent.MatrixCounting\n\n",
    TARGET_MODULE: b"namespace OAI\n\nopen Filter\nopen scoped Topology\n\nnamespace PiExponent.DeterminantContradiction\n\n",
}
GROUP_FOOTERS = {
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting": b"end PiExponent\n\nend OAI\n\n",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights": b"end PiExponent\n\nend OAI\n\n",
    "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational": b"end PiExponent\n\nend OAI\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix": b"end PiExponent.InterpolationMatrix\n\nend OAI\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic": b"end MatrixArithmetic\n\nend PiExponent\n\nend OAI\n\n",
    "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting": b"end PiExponent.MatrixCounting\n\nend OAI\n\n",
    TARGET_MODULE: b"end PiExponent.DeterminantContradiction\n\nend OAI\n\n",
}
IMPORTS = [
    "Mathlib",
    "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexFloor",
    "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted",
    ap10.config("determinant")["platform_module"],
]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(x):
    return (json.dumps(x, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def source_path(module, tree="port"):
    return TASK / tree / "lean" / Path(*module.split(".")).with_suffix(".lean")


def published_floor_names(pins):
    coverage = read(ap9.COVERAGE)
    records = {r["definition_name"]: r for r in coverage["records"]}
    names = set()
    for short in ["SimplexFloor", "SimplexUnweighted"]:
        key = "OAI_NumberTheory_PiExponent_Polynomials_" + short
        r = records[key]
        pub = TASK / r["publication_record"]
        cert = pub.parent / "provider-validation-fast.json"
        p, c = read(pub), read(cert)
        body = p["publish_intent"]["payload"]["definition"].encode()
        need(sha(pub) == r["publication_record_sha256"] and
             body == p["target_readback"]["body"]["definition"].encode() and
             sha_bytes(body) == r["literal_source_sha256"] and
             c["validated"] is True and c["provider_source_sha256"] == sha_bytes(body),
             "Published Simplex provider body/certificate changed: " + short)
        names.update(x["name"] for x in c["declarations"])
        pins.update({rel(pub): sha(pub), rel(cert): sha(cert)})
    return names


def authority():
    need(COMMIT == "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
         "Pinned OpenAI math commit differs")
    for key in ap9.CONFIGS:
        ap9.check_only(key)
    for key in ap10.CONFIGS:
        ap10.check_only(key)
    bindings, pins, _ = ap10.published_bindings()
    provided = set(bindings) | published_floor_names(pins)
    for key in ap10.CONFIGS:
        c = ap10.config(key)
        provided.update(c["names"])
        pins[rel(c["stage"] / "preparation.json")] = sha(c["stage"] / "preparation.json")
        pins[rel(c["stage"] / c["provider_file"])] = sha(c["stage"] / c["provider_file"])
    graph = {x["name"]: x for x in map(json.loads, GRAPH.read_text(encoding="utf-8").splitlines())}
    closure = set()
    todo = [TARGET]
    while todo:
        name = todo.pop()
        if name in closure:
            continue
        need(name in graph, "Missing exact source graph name: " + name)
        closure.add(name)
        todo.extend(graph[name]["typeDeps"] + graph[name]["valueDeps"])
    helper_set = {PREFIXES[m] + short for m, shorts in HELPER_NAMES.items() for short in shorts}
    need(len(closure) == 71 and len(helper_set) == 30 and
         closure - provided == helper_set | {TARGET},
         "Actual 71-name dependency closure does not equal provider names plus 30 helpers and target")
    ast_modules = {x["module"]: x for x in read(AST)["modules"]}
    scope_modules = {x["source"]: x for x in read(SCOPES)["modules"]}
    rows = []
    raw_commands = {}
    for module, shorts in HELPER_NAMES.items():
        port, original = source_path(module), source_path(module, "source")
        raw, original_raw = port.read_bytes(), original.read_bytes().replace(b"\r\n", b"\n")
        am = ast_modules[module]
        sm = scope_modules[module.replace(".", "/") + ".lean"]
        need(am["source_sha256"] == sha_bytes(raw) and sm["source_sha256"] == sha_bytes(raw),
             "AST/scope source hash differs: " + module)
        pins.update({rel(port): sha(port), rel(original): sha(original)})
        selected = []
        for short in shorts:
            name = PREFIXES[module] + short
            unit = next(x for x in am["units"] if name in x["graph_names"])
            scope = next(x for x in sm["declarations"] if x["verified_name"] == name)
            a, b = unit["start"]["offset"], unit["end"]["offset"]
            command = raw[a:b]
            contexts = [raw[x["range"]["start"]["offset"]:x["range"]["end"]["offset"]].decode()
                        for x in scope["context_commands"]]
            expected_contexts = ["open scoped BigOperators"]
            if module in ["OAI.NumberTheory.PiExponent.Polynomials.SimplexRational",
                          "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting"]:
                expected_contexts.append("open Filter Topology")
            if module == TARGET_MODULE:
                expected_contexts = ["open Filter", "open scoped Topology"]
            if module == "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting" and a >= 5000:
                expected_contexts.append("open Filter Topology")
            need(unit["graph_names"] == [name] and unit["graph_kinds"] == [graph[name]["kind"]]
                 and unit["privateTok"] is None and not unit["is_instance_command"]
                 and not unit["is_local_instance"] and
                 scope["namespace"] == PREFIXES[module].rstrip(".") and
                 all(s["kind"] == "namespace" for s in scope["scope_stack"]) and
                 contexts == expected_contexts and
                 original_raw.count(command.replace(b"\r\n", b"\n")) == 1,
                 "Exact original AST/context differs: " + name)
            selected.append((a, name, command))
            rows.append({"name": name, "module": module, "kind": graph[name]["kind"],
                         "port_path": rel(port), "port_sha256": sha(port),
                         "original_path": rel(original), "original_sha256": sha(original),
                         "start": a, "end": b,
                         "source_lines": [unit["start"]["line"], unit["end"]["line"]],
                         "command_sha256": sha_bytes(command),
                         "ast_row_sha256": sha_bytes(encode(unit)),
                         "scope_row_sha256": sha_bytes(encode(scope)),
                         "decl_graph_row_sha256": sha_bytes(encode(graph[name]))})
        need([n for _, n, _ in sorted(selected)] == [PREFIXES[module] + x for x in shorts],
             "Helper order differs from source order: " + module)
        raw_commands[module] = selected
    return graph, closure, provided, rows, raw_commands, pins


def assemble(raw_commands):
    parts = [("import " + "\nimport ".join(IMPORTS) + "\n\n").encode()]
    for module, selected in raw_commands.items():
        parts.append(GROUP_HEADERS[module])
        for _, name, command in selected:
            if module.endswith("SimplexCounting") and name == "OAI.PiExponent.tendsto_card_natWeightedSimplex":
                parts.append(b"open Filter Topology\n\n")
            parts.append(command.replace(b"\r\n", b"\n") + b"\n\n")
        parts.append(GROUP_FOOTERS[module])
    target_raw = source_path(TARGET_MODULE).read_bytes()
    ast_module = next(x for x in read(AST)["modules"] if x["module"] == TARGET_MODULE)
    unit = next(x for x in ast_module["units"] if TARGET in x["graph_names"])
    a, b = unit["start"]["offset"], unit["end"]["offset"]
    command = target_raw[a:b]
    original = source_path(TARGET_MODULE, "source").read_bytes().replace(b"\r\n", b"\n")
    ns, ne = unit["nameRange"]["start"]["offset"]-a, unit["nameRange"]["end"]["offset"]-a
    vs = unit["valueStart"]["offset"]-a
    need(command[ns:ne] == b"tendsto_collisionRate" and command[vs:vs+5] == b":= by" and
         command[:vs].count(b"tendsto_collisionRate") == 1 and
         original.count(command.replace(b"\r\n", b"\n")) == 1,
         "Original target AST name or proof boundary differs")
    formal = command[:vs] + b":= by\n  sorry\n"
    target = (("import " + "\nimport ".join(IMPORTS) + "\n\n").encode() +
              GROUP_HEADERS[TARGET_MODULE] + formal.replace(b"\r\n", b"\n") +
              b"\n" + GROUP_FOOTERS[TARGET_MODULE])
    renamed = command[:ns] + b"solution" + command[ne:]
    need(renamed[renamed.find(b":= by"):] == command[command.find(b":= by"):],
         "Original target proof bytes changed")
    parts.append(b"open OAI.PiExponent\nopen OAI.PiExponent.DeterminantContradiction\nopen Filter\nopen scoped Topology\n\n")
    parts.append(renamed.replace(b"\r\n", b"\n") + b"\n")
    return target, b"".join(parts), command, formal, unit


def snapshot(side, module, names):
    type_output = workspace_rel(STAGE / (SOURCE_TYPE_JSON if side == "source" else GENERATED_TYPE_JSON))
    refs_output = workspace_rel(STAGE / (SOURCE_REFS_JSON if side == "source" else GENERATED_REFS_JSON))
    target_name = TARGET if side == "source" else "solution"
    quoted_names = ", ".join("`" + n for n in names)
    probe = ap8.PROBE.replace("FullRowMinorProofSnapshot", "GroupedCollisionProofSnapshot")
    return ("import Lean\nimport " + module + "\n\n" +
            SNAPSHOT_CORE.read_text(encoding="utf-8").rstrip() + "\n\n" +
            "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[" + quoted_names + "] " +
            json.dumps(type_output) + "\n#print axioms " + target_name + "\n" + probe +
            "\nrun_meta do\n  GroupedCollisionProofSnapshot.exportEvidence " +
            " ".join(json.dumps(x) for x in [side, refs_output, target_name, module]) + "\n").encode()


def stage_files():
    graph, closure, provided, rows, raw_commands, pins = authority()
    target, solution, command, formal, unit = assemble(raw_commands)
    helper_names = [r["name"] for r in rows]
    generated = {
        TARGET_OUTPUT: target, SOLUTION_OUTPUT: solution,
        SOURCE_SNAPSHOT: snapshot("source", TARGET_MODULE, helper_names + [TARGET]),
        GENERATED_SNAPSHOT: snapshot("generated", SOLUTION_MODULE, helper_names + ["solution"]),
        "original-target-command.lean.txt": command,
        "wire-theorem-source.lean": target,
    }
    inputs = {rel(p): sha(p) for p in [SELF, AST, SCOPES, GRAPH, RUNTIME, SNAPSHOT_CORE,
                                       Path(runner.__file__), Path(ap8.__file__),
                                       Path(ap9.__file__), Path(ap10.__file__)]}
    inputs.update(pins)
    imports = [IMPORTS, IMPORTS, ["Lean", TARGET_MODULE], ["Lean", SOLUTION_MODULE]]
    files, commands = {}, {}
    for output, mode, manifest, dep_imports in zip(FILES, MODES, MANIFESTS, imports, strict=True):
        files[output] = {"sha256": sha_bytes(generated[output]), "mode": mode,
                         "emit_olean": mode == "emit-olean", "imports": dep_imports,
                         "manifest": manifest}
        generated[manifest] = encode({
            "schema_version": 1, "artifact_kind": "ap11-grouped-collision-rate-bounded-compiler-manifest",
            "output": workspace_rel(STAGE / output), "output_sha256": sha_bytes(generated[output]),
            "imports": dep_imports, "input_hashes": inputs, "runtime_sha256": sha(RUNTIME),
            "mode": mode, "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
            "validated": False, "submission_ready": False,
        })
        commands[output] = ("python scripts/preflight_staged_module.py " +
            verification_rel(STAGE / output) + " --root ap11/collision-rate --imports-manifest " +
            verification_rel(STAGE / manifest) + " --timeout-seconds 300" +
            (" --emit-olean" if mode == "emit-olean" else ""))
    generated["preparation.json"] = encode({
        "schema_version": 1, "artifact_kind": "ap11-grouped-collision-rate-node-preparation",
        "status": "prepared-uncompiled", "source_commit": COMMIT,
        "source_name": TARGET, "source_module": TARGET_MODULE,
        "source_url": ("https://github.com/openai/math/blob/" + COMMIT +
                       "/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L108-L125"),
        "target_ast": unit, "target_source_command_sha256": sha_bytes(command),
        "target_original_command_equal_modulo_line_endings": True,
        "target_proof_suffix_sha256": sha_bytes(command[unit["valueStart"]["offset"]-unit["start"]["offset"]:]),
        "formal_statement": formal.decode(), "global_solution_name": "solution",
        "global_solution_preserves_literal_source_proof": True,
        "graph_closure_names": sorted(closure), "provider_subtracted_names": sorted(closure & provided),
        "inline_helper_names": helper_names, "inline_exact_source_units": rows,
        "source_type_only_names": helper_names + [TARGET],
        "generated_type_only_names": helper_names + ["solution"],
        "source_and_generated_theorem_values_null": True,
        "source_and_generated_actual_proof_ref_probe": True,
        "provider_modules_imported": IMPORTS[1:], "requires_AP9_AP10_actual_imports": True,
        "target_comparator_modecheck_only": True, "solution_emits_olean": True,
        "input_hashes": inputs, "runtime_sha256": sha(RUNTIME), "files": files,
        "compile_commands": commands, "single_compiler_sequential": True,
        "Lean_started": False, "API_used": False, "validated": False,
        "submission_ready": False, "proposal_status": "Draft",
    })
    return generated


def check_only(generated=None):
    if generated is None:
        generated = stage_files()
    for output, raw in generated.items():
        need((STAGE / output).is_file() and (STAGE / output).read_bytes() == raw,
             "Exact stage reconstruction differs: " + output)
    gc.collect()
    for output, manifest in zip(FILES, MANIFESTS, strict=True):
        doc = read(STAGE / manifest)
        runner.verify_manifest_inputs(doc)
        runner.verify_source_certificate(STAGE / output, doc)
    return {"checked_files": len(generated), "all_hashes_match": True,
            "inline_helpers": 30, "closure_names": 71, "Lean_started": False,
            "API_used": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = None
    if args.prepare:
        generated = stage_files()
        for output, raw in generated.items():
            path = STAGE / output
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to overwrite immutable AP11 stage: " + output)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

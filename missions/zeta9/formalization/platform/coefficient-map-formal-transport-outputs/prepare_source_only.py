"""Pure Outputs platform SOURCE candidate; no Lean/Lake, API or credentials.

Lexical staging is explicitly provisional. The real author must compile a
fresh project and run actual graph/parser/full kernel/value controls before
this candidate can become a reviewed platform payload. No old proof object
is copied or loaded as a proof into this preparation.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
NATIVE_IND = TASK / "verification/formalization-coefficient-map-formal-transport-outputs-independent-2026-10-07"
ROOT_GATE = TASK / "verification/formalization-project-handoff-2026-10-07/root-outputs-independent-complete-binding-rehash.json"
IND_SHA = "0e1aca998987f190d91bf36e2c89dc6cdb8f93e1f86f3e9130a3295add2a3b08"
SOURCE_SHA = "8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6"
JETS_SHA = "ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02"
NS = "ZetaNine.CoefficientMapFormalTransportOutputs"
TAG = "CoefficientMapFormalTransportOutputs"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
TARGETS = [("actual_chosen_constantTerm_transport", "constant", "n hn r"),
           ("actual_chosen_five_output_transport", "five", "n hn r"),
           ("actual_five_output_matrix_transport", "matrix", "n hn")]


def sha(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write(path, data):
    assert not path.exists(), "Preserve all prior SOURCE/artifacts: " + str(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))


def dump(path, value):
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def binding(path):
    p = path.resolve()
    row = {"bytes": p.stat().st_size, "sha256": sha(p)}
    if p.is_relative_to(TASK.resolve()):
        row["task_relative"] = p.relative_to(TASK.resolve()).as_posix()
    elif p.is_relative_to(ROOT.resolve()):
        row["root_relative"] = p.relative_to(ROOT.resolve()).as_posix()
    else:
        row["absolute_path"] = str(p)
    return row


def bound_path(row):
    if row.get("task_relative"):
        return TASK / row["task_relative"]
    if row.get("root_relative"):
        return ROOT / row["root_relative"]
    return Path(row["absolute_path"])


def checked(row):
    path = bound_path(row)
    assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"], str(path)
    return path


def lexical_declarations(text):
    """A SOURCE-only hint, never substituted for the genuine Lean parser."""
    starts = list(re.finditer(r"^(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|theorem|lemma)\s+(\w+)", text, re.M))
    namespace = re.findall(r"^namespace\s+(\S+)", text, re.M)
    assert len(namespace) == 1, "This provisional stager only accepts one native namespace"
    namespace = namespace[0]
    finish = text.rfind("end " + namespace)
    assert finish >= 0
    rows = []
    for i, match in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else finish
        source = text[match.start():end].rstrip() + "\n"
        rows.append({"kind": match.group(1), "name": match.group(2), "full_name": namespace + "." + match.group(2),
                     "start": match.start(), "end": end, "header": source.split(":=", 1)[0].rstrip(), "source": source})
    return namespace, rows


def canonical_definition_closure():
    modules, seen, order = {}, set(), []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        assert path.is_file()
        text = path.read_text(encoding="utf-8-sig")
        for dependency in re.findall(r"^import\s+(Definitions\.\S+)", text, re.M):
            visit(dependency)
        modules[module] = {"module": module, "binding": binding(path), "SOURCE": text}
        order.append(module)

    for module in ["Definitions.Def_ZetaNine_CoefficientMapMatrix", "Definitions.Def_ZetaNine_CoefficientMapConnection", "Definitions.Def_ZetaNine_CoefficientMapNumeratorPF"]:
        visit(module)
    # Namespace/declaration names only, not a proof dependency graph.
    inventory = set()
    for module in order:
        text = modules[module]["SOURCE"]
        namespaces = re.findall(r"^namespace\s+(\S+)", text, re.M)
        if len(namespaces) == 1:
            namespace = namespaces[0]
            inventory.update(namespace + "." + n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+(\w+)", text, re.M))
        else:
            active = None
            for line in text.splitlines():
                match = re.match(r"namespace\s+(\S+)", line)
                if match:
                    active = match.group(1)
                match = re.match(r"(?:noncomputable\s+)?(?:def|abbrev)\s+(\w+)", line)
                if match and active:
                    inventory.add(active + "." + match.group(1))
                if line.startswith("end "):
                    active = None
    return modules, order, inventory


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    assert not (OUT / "source-preparation.json").exists()
    assert not (OUT / "staged").exists()
    planned = TASK / ".rt/opfa1"
    assert not planned.exists(), "Future author project must initially be absent"
    ind_path = NATIVE_IND / "independent-review.json"
    assert sha(ind_path) == IND_SHA
    ind = load(ind_path)
    assert ind["verdict"] == "PASS" and len(ind["stable_files"]) == 1085
    assert len(ind["checks"]) == 7618 and all(row["passed"] for row in ind["checks"])
    gate = load(ROOT_GATE)
    assert gate["independent_report_sha256"] == IND_SHA and gate["stable_bindings"] == 1085
    assert gate["mismatches"] == 0 and gate["Root_personally_stream_rehashed_all"] is True
    native_rehash = []
    for row in ind["stable_files"]:
        path = checked(row)
        native_rehash.append({**row, "actual_sha256": sha(path)})
    prep_path = NATIVE_IND / "source-preparation.json"
    prep = load(prep_path)
    assert len(prep["native_sources"]) == 21
    texts, sources = {}, []
    for row in prep["native_sources"]:
        source = checked(row["snapshot"])
        data = source.read_bytes()
        destination = OUT / "native-source-snapshots" / row["project_relative"]
        write(destination, data)
        text = data.decode("utf-8-sig")
        texts[row["module"]] = text
        sources.append({"module": row["module"], "original_snapshot": row["snapshot"], "own_snapshot": binding(destination),
                        "future_native_project_path": row["project_relative"]})
    output_module = "missions.zeta9.formalization.CoefficientMapFormalTransportOutputs"
    jets_module = "missions.zeta9.formalization.CoefficientMapFormalTransportJets"
    assert hashlib.sha256(texts[output_module].encode()).hexdigest() == SOURCE_SHA
    assert hashlib.sha256(texts[jets_module].encode()).hexdigest() == JETS_SHA
    _, output_rows = lexical_declarations(texts[output_module])
    assert len(output_rows) == 16 and all(r["kind"] == "theorem" for r in output_rows)
    expected_headers = {r["name"].rsplit(".", 1)[-1]: r["header"] for r in ind["original_exact_headers"]}
    assert len(expected_headers) == 16
    for row in output_rows:
        assert row["header"] == expected_headers[row["name"]], row["name"]
    assert len(ind["all_actual_complete_definition_records"]) == 18
    modules, order, canonical_names = canonical_definition_closure()
    for module in order:
        row = modules[module]
        write(OUT / "canonical-definition-source-snapshots" / (module.replace(".", "/") + ".lean"), row["SOURCE"])
    data_module = "missions.zeta9.formalization.CoefficientMapFormalTransportData"
    shift_module = "missions.zeta9.formalization.CoefficientMapParameterShift"
    connection_module = "missions.zeta9.formalization.CoefficientMapConnection"
    data_ns, data_rows = lexical_declarations(texts[data_module])
    shift_ns, shift_rows = lexical_declarations(texts[shift_module])
    _, connection_rows = lexical_declarations(texts[connection_module])
    data_defs = [r for r in data_rows if r["kind"] == "def" and r["full_name"] not in canonical_names]
    shift_defs = [r for r in shift_rows if r["kind"] == "def" and r["full_name"] not in canonical_names]
    assert len(data_defs) == 10 and len(shift_defs) == 2
    unique = next(r for r in connection_rows if r["name"] == "connection_five_systems_unique")
    local_proofs = []
    for row in connection_rows:
        if row["kind"] == "theorem":
            local = row["source"].replace("theorem " + row["name"], "have " + row["name"], 1)
            local_proofs.append("\n".join("    " + line if line else "" for line in local.rstrip().splitlines()))
    unique_type = "∀ (n : ℕ) (hn : 1 ≤ n) (r : Fin 5), ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧ connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 = (connectionTarget n r.val).comp (connectionU n)"
    term = "((by\n" + "\n".join(local_proofs) + "\n    exact connection_five_systems_unique\n  ) : (" + unique_type + "))"
    new_data = []
    for row in data_defs:
        source = row["source"]
        if row["name"] == "connectionPair":
            assert source.count("connection_five_systems_unique") == 1
            source = source.replace("connection_five_systems_unique", term, 1)
        new_data.append(source)
    imports = "\n".join("import " + module for module in ["Definitions.Def_ZetaNine_CoefficientMapMatrix", "Definitions.Def_ZetaNine_CoefficientMapConnection", "Definitions.Def_ZetaNine_CoefficientMapNumeratorPF"])
    definition_path = "Definitions/Def_ZetaNine_" + TAG + ".lean"
    definition = imports + "\nimport Mathlib\n\nset_option autoImplicit false\nset_option maxHeartbeats 12000000\nnoncomputable section\nopen scoped BigOperators Matrix\nopen Finset Polynomial\n\n"
    definition += "namespace " + shift_ns + "\nopen CoefficientMapKernelBridge CoefficientMapConnection\n\n" + "\n".join(r["source"] for r in shift_defs) + "\nend " + shift_ns + "\n\n"
    definition += "namespace " + data_ns + "\nopen CoefficientMapConnection CoefficientMapJet CoefficientMapInjectivity\n\n" + "\n".join(new_data) + "\nend " + data_ns + "\n"
    staged = OUT / "staged"
    write(staged / definition_path, definition)
    new_names = {r["full_name"] for r in data_defs + shift_defs}
    proof_source = "import " + definition_path[:-5].replace("/", ".") + "\nimport Mathlib\n\n"
    retained_proofs, retained_uncanonical_defs = [], []
    for module in texts:
        if module == "Definitions.Def_ZetaNine_HarmonicStability":
            continue
        text = texts[module]
        namespace, rows = lexical_declarations(text)
        # Provisional lexical pruning; exact parser/reference-span authority is pending.
        removals = [(r["start"], r["end"]) for r in rows if r["kind"] in {"def", "abbrev"} and r["full_name"] in canonical_names | new_names]
        for begin, end in sorted(removals, reverse=True):
            text = text[:begin] + text[end:]
        text = re.sub(r"^import\s+.*\n", "", text, flags=re.M)
        text = re.sub(r"^#print\s+.*\n", "", text, flags=re.M)
        assert not re.search(r"^import\s+(?:missions|Theorems|Solutions)\.", text, re.M)
        proof_source += "\n/- SOURCE module " + module + "; full proof bodies preserved. -/\n" + text.rstrip() + "\n"
        retained_proofs += [{"module": module, "name": r["full_name"], "header": r["header"]} for r in rows if r["kind"] in {"theorem", "lemma"}]
        retained_uncanonical_defs += [{"module": module, "name": r["full_name"]} for r in rows if r["kind"] in {"def", "abbrev"} and r["full_name"] not in canonical_names | new_names]
    targets, payloads = [], [{"kind": "uncompiled_definition_SOURCE_candidate", "path": definition_path, "binding": binding(staged / definition_path)}]
    byname = {r["name"]: r for r in output_rows}
    for short, suffix, args in TARGETS:
        row = byname[short]
        header = row["header"].replace("theorem " + short, "theorem " + NS + "." + short, 1)
        preamble = "import " + definition_path[:-5].replace("/", ".") + "\nset_option autoImplicit false\nopen scoped BigOperators Matrix\nopen Finset Polynomial\nopen ZetaNine.CoefficientMapFormalTransportOutputs\nopen ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData"
        reference = preamble + "\n\n" + header + " := by sorry\n"
        local_ref = "Theorems/Thm_ZetaNine_" + TAG + "_" + suffix + ".lean"
        local_sol = "Solutions/Sol_ZetaNine_" + TAG + "_" + suffix + ".lean"
        solution = proof_source + "\nopen scoped BigOperators Matrix\nopen Finset Polynomial\nopen ZetaNine.CoefficientMapFormalTransportOutputs\nopen ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData\n\n"
        solution += row["header"].replace("theorem " + short, "theorem solution", 1) + " := by\n  exact " + NS + "." + short + " " + args + "\n\n#print axioms solution\n"
        write(staged / local_ref, reference)
        write(staged / local_sol, solution)
        payloads += [{"kind": "statement_type_catalog_only_SOURCE_candidate", "path": local_ref, "binding": binding(staged / local_ref)},
                     {"kind": "uncompiled_complete_solution_SOURCE_candidate", "path": local_sol, "binding": binding(staged / local_sol)}]
        targets.append({"theorem_name": NS + "." + short, "local_reference": local_ref, "local_solution": local_sol,
                        "wrapper_arguments": args, "exact_original_header": row["header"], "formal_statement": header + " := by sorry",
                        "preamble": preamble, "full_original_forall_not_n_one_test": True})
    dump(OUT / "native-input-rehash.json", {"at": datetime.now(timezone.utc).isoformat(), "native_independent_sha256": IND_SHA,
        "stable_bindings": 1085, "mismatches": 0, "records": native_rehash, "Root_gate": binding(ROOT_GATE), "Lean_calls": 0, "API_calls": 0})
    dump(OUT / "target-plan.json", {"definition": "ZetaNine_" + TAG, "local_definition": definition_path, "targets": targets,
        "existing_definitions": [{"module": module, **modules[module]["binding"]} for module in order], "payloads": payloads,
        "Mathlib_ENV": REV, "native_all16_exact_headers": [{"name": r["full_name"], "header": r["header"]} for r in output_rows],
        "all18_definition_controls_required": [r["declaration"] for r in ind["all_actual_complete_definition_records"]],
        "additional_whole_definition_controls_required": [r["full_name"] for r in shift_defs], "raw_references_never_used_as_proof": True,
        "candidate_not_kernel_checked": True, "API_publication_forbidden_until_author_independent_and_Root_gates": True})
    dump(OUT / "source-preparation.json", {"at": datetime.now(timezone.utc).isoformat(), "status": "PURE_UNCOMPILED_OUTPUTS_PLATFORM_SOURCE_CANDIDATE",
        "native_source_sha256": SOURCE_SHA, "genuine_compiled_Jets_source_sha256": JETS_SHA, "native_independent_report": binding(ind_path),
        "Root_native_1085_full_rehash": binding(ROOT_GATE), "own_personally_rehashed_native_bindings": 1085,
        "native_SOURCE_closure": sources, "native_SOURCE_count": 21, "all16_exact_original_headers_preserved": True,
        "all18_whole_definition_type_value_kernel_rfl_controls_planned": True,
        "typed_boundaries_count_planned": 9, "all_generated_and_reachable_helpers_fulltype_fullvalue_inferType_Std3_required": True,
        "actual_own_import_object_resolver_required": True, "strict_lossless_DAG_required": True,
        "planned_project": planned.relative_to(TASK).as_posix(), "planned_project_initially_absent": True,
        "planned_project_created": False, "Lean_lane_grant_present": False, "Lean_calls": 0, "API_calls": 0, "credentials_reads": 0,
        "source_staging_is_lexical_provisional_never_a_genuine_Lean_parser_or_graph": True,
        "choice_proof_term": {"original_name": unique["full_name"], "local_complete_Connection_theorem_bodies": len(local_proofs),
                              "only_proof_term_in_connectionPair_replaced": True, "whole_value_kernel_and_rfl_still_required": True},
        "retained_proof_SOURCE_inventory": retained_proofs, "retained_uncanonical_definition_SOURCE_inventory": retained_uncanonical_defs,
        "candidate_payloads": payloads, "author_PASS_claimed": False, "platform_independent_PASS_claimed": False,
        "foreign_proof_objects_copied_or_used": False, "scope": {"finite_B": True, "five_actual_outputs": True,
          "LEFT_Gamma_matrix_transport_forall_n_ge_one": True, "HasSum_parameter17": False, "integer_height": False, "J": False, "irrationality": False}})
    stable = [binding(p) for p in sorted(OUT.rglob("*")) if p.is_file() and p.name != "preparation-binding-check.json"]
    for row in stable:
        checked(row)
    dump(OUT / "preparation-binding-check.json", {"at": datetime.now(timezone.utc).isoformat(), "stable_files": stable,
        "differences": 0, "source_preparation_sha256": sha(OUT / "source-preparation.json"), "Lean_calls": 0, "API_calls": 0})
    print(json.dumps({"status": "UNCOMPILED_SOURCE_CANDIDATE_ONLY", "payloads": 7, "native_sources": 21,
                      "preserved_original_foralls": 16, "planned_whole_definition_controls": 18,
                      "all_native_bindings_rehashed": 1085, "choice_complete_local_proofs": len(local_proofs),
                      "retained_proof_SOURCE_declarations": len(retained_proofs), "source_preparation_sha256": sha(OUT / "source-preparation.json"),
                      "Lean_calls": 0, "API_calls": 0, "credentials_reads": 0, "future_project_created": False}, indent=2))


if __name__ == "__main__":
    main()

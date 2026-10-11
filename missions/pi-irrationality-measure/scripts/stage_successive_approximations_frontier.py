"""Generate an isolated, source-faithful three-node approximation frontier.

This producer copies no proof result from platform sorry placeholders. It only
promotes the exact source command units in a private side plan and generates
reviewable Thm/Sol/snapshot artifacts. It does not run Lean or use the API.
"""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import generate_platform_bundles as bundles
import generate_platform_provider_nodes as node_impl
import plan_platform_artifacts as artifact_planner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification/ap4"
SELF = Path(__file__).resolve()

MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
UNIT_KEYS = {
    "exists_successive_approximations": MODULE + ":164",
    "exists_normalized_selection_of_selector": MODULE + ":4368",
    "exists_normalized_successive_approximations": MODULE + ":5926",
    "exists_large_log_approximation": "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection:131",
}
STAGES = {
    "exists_successive_approximations": DEST / "n1",
    "exists_normalized_selection_of_selector": DEST / "n2",
    "exists_normalized_successive_approximations": DEST / "n3",
}
TARGETS = tuple(STAGES)
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_URL = ("https://github.com/openai/math/blob/" + SOURCE_COMMIT
              + "/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean")
SOURCE_LINES = {
    "exists_successive_approximations": (8, 55),
    "exists_normalized_selection_of_selector": (97, 132),
    "exists_normalized_successive_approximations": (134, 147),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


class ShortDestination:
    def __truediv__(self, slug: str) -> Path:
        for name, stage in STAGES.items():
            if slug == ("OAI.PiExponent." + name).replace(".", "_"):
                return stage
        raise ValueError("Unexpected node slug from source generator: " + str(slug))


def promoted_generator():
    generator = node_impl.ProviderNodeGenerator()
    g = generator.g
    custom_unit_plan = copy.deepcopy(g.unit_plan)
    by_id = {row["id"]: row for row in custom_unit_plan["units"]}
    for key in UNIT_KEYS.values():
        row = by_id.get(key)
        if row is None:
            raise ValueError("Required authoritative command unit is missing: " + key)
        if row["category"] == "node":
            continue
        if row["category"] != "inline":
            raise ValueError("Only ordinary inline theorem units may be promoted: " + key)
        if row["graph_kinds"] != ["theorem"] or row["is_instance_command"] or row["private"]:
            raise ValueError("Promoted command is not one public ordinary theorem: " + key)
        row["category"] = "node"
        row["promotion_reasons"] = list(row.get("promotion_reasons", [])) + [
            "isolated ap4 SuccessiveApproximations dependency frontier"]
    custom_artifact_plan = artifact_planner.build_artifacts(custom_unit_plan, g.scopes, g.reuse)
    custom_artifact_plan["provisional"] = True
    if set(custom_artifact_plan["nodes"]).issuperset(UNIT_KEYS.values()) is False:
        raise ValueError("Promoted side plan omitted one requested theorem node")
    # The node generator still verifies all global source, AST, runtime, and
    # existing plan hashes in its constructor. Replace only in-memory plans for
    # this isolated generation; the campaign's frozen plan files stay untouched.
    g.unit_plan = custom_unit_plan
    g.units = {row["id"]: row for row in custom_unit_plan["units"]}
    g.artifact_plan = custom_artifact_plan
    return generator, custom_unit_plan, custom_artifact_plan


def metadata(name: str) -> dict:
    first, last = SOURCE_LINES[name]
    common = {"tags": ["openai-pi-exponent-017", "number-theory", "rational-approximation"],
              "source_commit": SOURCE_COMMIT,
              "source_url": SOURCE_URL + f"#L{first}-L{last}"}
    if name == "exists_successive_approximations":
        common.update({
            "theorem_title": "Successive rational approximations with increasing logarithmic weights",
            "natural_language_statement": (
                "Let $\\nu>0$ and let $T$ map finite lists of real numbers to real numbers. "
                "Assume that approximations to $\\pi$ with exponent $\\nu$ exist above every "
                "natural denominator threshold. Then there are integer numerators $p_n$ and "
                "natural denominators $q_n$ such that, for every $n$,\n\n"
                "$$2\\le q_n,\\quad p_n\\ne0,\\quad |\\pi-p_n/q_n|\\le q_n^{-\\nu},\\quad "
                "1\\le\\lceil\\log q_n\\rceil,\\quad "
                "T([\\lceil\\log q_{n-1}\\rceil,\\ldots,\\lceil\\log q_0\\rceil])"
                "<\\lceil\\log q_n\\rceil. $$\n\n"
                "The list is empty when $n=0$. The uniform approximation premise is assumed; "
                "the theorem does not assert it unconditionally for $\\pi$."
            ),
            "explanation": (
                "For each finite history of logarithmic weights, apply the assumed approximation "
                "property at a denominator threshold chosen large enough that its logarithm exceeds "
                "$T$ of that history. The established large-log approximation lemma also ensures "
                "the denominator is at least two and the numerator is nonzero. Classical choice "
                "selects one such pair for each history, and recursion forms the two sequences. "
                "The induction identifying each history with the reversed list of prior weights "
                "gives the stated strict growth condition."
            ),
        })
    elif name == "exists_normalized_selection_of_selector":
        common.update({
            "theorem_title": "Normalize a selector sequence and obtain product growth",
            "natural_language_statement": (
                "Let $\\nu,X,D\\in\\mathbb R$. Suppose that for every threshold rule "
                "$T$ on finite lists there are integer numerators $p_n$ and natural denominators "
                "$q_n$ with $q_n\\ge2$, $p_n\\ne0$, the bound "
                "$|\\pi-p_n/q_n|\\le q_n^{-\\nu}$, and logarithmic ceiling weights that exceed "
                "$T$ applied to earlier weights in reverse order. Then there are sequences "
                "$p_n,q_n,x_n$ with $x_0=1$ and $x_{n+1}=\\lceil\\log q_n\\rceil$ such that\n\n"
                "$$x_i\\ge1,\\quad X<x_{n+1},\\quad "
                "D\\prod_{j<i}x_j<x_i\\quad(i>0),$$\n\n"
                "while every pair $(p_n,q_n)$ retains the same power-law approximation and "
                "nonzero-numerator conditions. The hypothesis on the selector is part of the theorem."
            ),
            "explanation": (
                "Apply the selector with threshold equal to the maximum of $X$ and $D$ times the "
                "product of the supplied history. Define $x_0=1$ and let each later $x$ value be "
                "the ceiling logarithm of the corresponding denominator. The selector's first "
                "inequalities give the approximation, positivity, and $X$ margin. The product "
                "identity for normalized logarithmic weights converts the history product in the "
                "selector condition into $\\prod_{j<i}x_j$, yielding the strict product growth. "
                "No sign assumptions on $X$ or $D$ are needed for this implication."
            ),
        })
    elif name == "exists_normalized_successive_approximations":
        common.update({
            "theorem_title": "Normalized successive approximations under a uniform power-law hypothesis",
            "natural_language_statement": (
                "Let $\\nu>0$ and $X,D\\in\\mathbb R$. Assume that for every natural "
                "number $Q$ there are an integer $p$ and a natural number $q$ with $Q\\le q$ "
                "and $|\\pi-p/q|\\le q^{-\\nu}$. Then there are sequences of integer numerators "
                "$p_n$, natural denominators $q_n$, and real weights $x_n$ such that\n\n"
                "$$x_0=1,\\quad x_{n+1}=\\lceil\\log q_n\\rceil,\\quad "
                "q_n\\ge2,\\quad p_n\\ne0,\\quad |\\pi-p_n/q_n|\\le q_n^{-\\nu},\\quad "
                "1\\le\\lceil\\log q_n\\rceil,\\quad X<x_{n+1},$$\n\n"
                "and $D\\prod_{j<i}x_j<x_i$ for each $i>0$. The uniform approximation property "
                "is a hypothesis, not an unconditional conclusion about \\pi."
            ),
            "explanation": (
                "First construct successive approximants whose logarithmic ceiling weights exceed "
                "any prescribed function of their finite history. Then apply the selector "
                "normalization with threshold $\\max\\{X,D\\prod_{j<i}x_j\\}$, using the exact "
                "finite-product identity for the normalized weight sequence. This transfers the "
                "uniform approximation bound while enforcing both the requested lower margin and "
                "the strict product-growth condition. The proof uses the stated uniform hypothesis "
                "throughout."
            ),
        })
    else:
        raise ValueError("Unknown theorem metadata key: " + name)
    return common


def rfl_helper_ast_witness(generator, n2_manifest: dict) -> dict:
    g = generator.g
    raw, facts, _, provenance = generator.load_module(MODULE)
    originals = (TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean").read_bytes()
    if raw.replace(b"\r\n", b"\n") != originals.replace(b"\r\n", b"\n"):
        # This module's current version port changes imports and line endings
        # only; reject any body-level difference rather than infer mappings.
        port_lines = raw.splitlines()
        original_lines = originals.splitlines()
        if port_lines[4:] != original_lines[4:]:
            raise ValueError("Original/port SuccessiveApproximations bodies differ beyond imports/line endings")
    requested = {row["source_unit"]: row for row in n2_manifest["public_inline_ci_requests"]}
    records = []
    for key in (MODULE + ":3651", MODULE + ":3805"):
        unit = g.units[key]
        graph_name = unit["graph_names"][0]
        if (unit["category"] != "inline" or unit["graph_kinds"] != ["theorem"]
                or unit["private"] or unit["deprivate"] or unit["is_instance_command"]
                or len(unit["graph_names"]) != 1 or unit["privateTok"] is not None):
            raise ValueError("n2 helper command is not one public ordinary theorem: " + key)
        request = requested.get(key)
        if request is None or request["source_graph_name"] != graph_name:
            raise ValueError("n2 helper is absent from exact public CI request domain: " + key)
        start = unit["start"]["offset"]
        end = unit["end"]["offset"]
        source_command = raw[start:end]
        syntax_rows = [row for row in facts if row.get("kind") == "command"
                       and row.get("syntax", {}).get("range", {}).get("start", {}).get("offset") == start]
        if len(syntax_rows) != 1:
            raise ValueError("No unique authoritative AST command row at exact helper offset: " + key)
        syntax = syntax_rows[0]
        ast_range = syntax["syntax"]["range"]
        if (ast_range["start"]["offset"] != start or ast_range["end"]["offset"] != end
                or syntax.get("isDeclaration") is not True):
            raise ValueError("AST helper source range differs from owner unit: " + key)
        graph = g.graph[graph_name]
        proof_start = unit["valueStart"]["offset"] - start
        proof_bytes = source_command[proof_start:]
        original_line_start = unit["start"]["line"] - 1
        original_line_end = unit["end"]["line"]
        original_command = b"\n".join(originals.splitlines()[original_line_start:original_line_end])
        if original_command != source_command.replace(b"\r\n", b"\n").rstrip(b"\n"):
            raise ValueError("Raw original helper command differs after CRLF/LF normalization: " + key)
        records.append({
            "source_unit": key,
            "source_graph_name": graph_name,
            "generated_name": request["generated_name"],
            "source_command_range": {"start": unit["start"], "end": unit["end"]},
            "source_value_start": unit["valueStart"],
            "raw_command_utf8": source_command.decode("utf-8"),
            "raw_command_sha256": hashlib.sha256(source_command).hexdigest(),
            "raw_proof_suffix_utf8": proof_bytes.decode("utf-8"),
            "raw_proof_suffix_sha256": hashlib.sha256(proof_bytes).hexdigest(),
            "source_ast_command": syntax,
            "ast_command_sha256": hashlib.sha256(json.dumps(syntax, sort_keys=True, ensure_ascii=False,
                                                               separators=(",", ":")).encode("utf-8")).hexdigest(),
            "graph_kind": graph["kind"],
            "source_private": graph["isPrivate"],
            "source_instance": graph["isInstance"],
            "type_dependencies": graph["typeDeps"],
            "value_dependencies": graph["valueDeps"],
            "generated_companion": request["generated_companion"],
            "no_companion_identity_inferred": request["generated_companion"] is False,
            "source_line_span": [unit["start"]["line"], unit["end"]["line"]],
            "source_port_path": provenance["source"],
            "source_port_sha256": provenance["source_sha256"],
            "source_original_path": provenance["original_source"],
            "source_original_sha256": provenance["original_source_sha256"],
            "source_original_command_normalized_to_port": True,
        })
    return {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n2-inline-helper-ast-witness",
        "source_commit": SOURCE_COMMIT,
        "source_module": MODULE,
        "source_facts": provenance["facts"],
        "source_facts_sha256": provenance["facts_sha256"],
        "helpers": records,
        "interpretation": "The simp-rfl helper is an ordinary public theorem command. Its exact source proof suffix is retained; no private/equation companion is guessed.",
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }


def published_weight_definition_binding() -> dict:
    cert_path = TASK / "verification/ap3/s/probes/provider-validation.json"
    stage_path = TASK / "verification/ap3/stage-manifest.json"
    publication_path = TASK / "verification/ap3/publication/Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations/publication.json"
    olean = TASK / "verification/staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations.olean"
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    stage = json.loads(stage_path.read_text(encoding="utf-8"))
    publication = json.loads(publication_path.read_text(encoding="utf-8"))
    checks = {
        "validated": cert.get("validated") is True,
        "source_commit": cert.get("source_commit") == SOURCE_COMMIT,
        "source_name": cert.get("source_name") == "OAI.PiExponent.normalizedLogWeights",
        "source_module": cert.get("source_module") == MODULE,
        "generated_module": cert.get("generated_module") == "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations",
        "exact_public_name": cert.get("exact_public_name") is True,
        "kernel_type_equal": cert.get("kernel_type_equal") is True,
        "complete_definition_value_equal": cert.get("complete_definition_value_equal") is True,
        "axioms_equal_and_std3": cert.get("axioms_equal_and_std3") is True,
        "actual_module_owners_checked": cert.get("actual_module_owners_checked") is True,
        "no_174_reuse": cert.get("source174_certificate_used") is False,
        "provider_olean_exists": olean.is_file(),
        "provider_olean_hash_matches": cert.get("provider_preflight", {}).get("output_olean_sha256") == sha(olean),
        "published": publication.get("definition_id") == "74cfcd7f-9e25-450a-a16f-f6d00a7187e2"
        and publication.get("last_publish_verdict", {}).get("body", {}).get("status") == "PUBLISHED",
    }
    if not all(checks.values()):
        raise ValueError("Existing normalizedLogWeights publication certificate no longer matches: "
                         + str([key for key, value in checks.items() if not value]))
    return {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n2-actual-definition-input",
        "source_module": MODULE,
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations",
        "source_name": "OAI.PiExponent.normalizedLogWeights",
        "certificate": cert_path.relative_to(TASK).as_posix(),
        "certificate_sha256": sha(cert_path),
        "stage_manifest": stage_path.relative_to(TASK).as_posix(),
        "stage_manifest_sha256": sha(stage_path),
        "publication": publication_path.relative_to(TASK).as_posix(),
        "publication_sha256": sha(publication_path),
        "definition_id": publication["definition_id"],
        "output_olean": olean.relative_to(TASK).as_posix(),
        "output_olean_sha256": sha(olean),
        "checks": checks,
        "source174_certificate_used": False,
        "Lean_started": False,
        "API_used": False,
        "validated": True,
        "proposal_status": "Draft",
    }


def generate():
    generator, unit_plan, artifact_plan = promoted_generator()
    old_dest = node_impl.DEST
    try:
        node_impl.DEST = ShortDestination()
        reports = []
        for name in TARGETS:
            key = UNIT_KEYS[name]
            report = generator.generate(key)
            stage = STAGES[name]
            manifest = json.loads((stage / "manifest.json").read_text(encoding="utf-8"))
            if report["node"] != key or manifest["source_graph_name"] != "OAI.PiExponent." + name:
                raise ValueError("Generated target identity differs from the requested source theorem")
            if manifest["source_components"][0]["source_module"] != MODULE:
                raise ValueError("Generated source component is not the pinned SuccessiveApproximations module")
            # The theorem output module is imported by later nodes under the
            # stable Theorems namespace; keep the module root itself short.
            statement_name, solution_name = Path(manifest["statement"]).name, Path(manifest["solution"]).name
            routed = [(stage / statement_name, stage / "Theorems" / statement_name, "statement"),
                      (stage / solution_name, stage / "Solutions" / solution_name, "solution")]
            for old_path, new_path, field in routed:
                new_path.parent.mkdir(parents=True, exist_ok=True)
                if old_path != new_path:
                    if new_path.exists() and new_path.read_bytes() != old_path.read_bytes():
                        raise ValueError("Existing routed theorem output differs: " + str(new_path))
                    if not new_path.exists():
                        new_path.write_bytes(old_path.read_bytes())
                    old_path.unlink()
                manifest[field] = new_path.relative_to(ROOT).as_posix()
                manifest[field + "_sha256"] = sha(new_path)
                manifest["outputs_sha256"][new_path.name] = sha(new_path)
                manifest["outputs_sha256"].pop(old_path.name, None)
            write_json(stage / "manifest.json", manifest)
            write_json(stage / "academic-metadata.json", metadata(name))
            reports.append({**report,
                "theorem_name": manifest["theorem_name"],
                "source_statement_file": manifest["statement"],
                "source_solution_file": manifest["solution"],
                "metadata": (stage / "academic-metadata.json").relative_to(TASK).as_posix(),
                "metadata_sha256": sha(stage / "academic-metadata.json"),
                "child_dependencies": manifest["child_nodes"],
                "definition_dependency_witnesses": manifest["definition_dependency_witnesses"],
                "Lean_started": False, "validated": False, "submission_ready": False})
    finally:
        node_impl.DEST = old_dest

    n2_manifest = json.loads((STAGES["exists_normalized_selection_of_selector"] / "manifest.json").read_text(encoding="utf-8"))
    ast_witness = rfl_helper_ast_witness(generator, n2_manifest)
    ast_path = STAGES["exists_normalized_selection_of_selector"] / "inline-helper-ast-witness.json"
    write_json(ast_path, ast_witness)
    weight_binding = published_weight_definition_binding()
    binding_path = STAGES["exists_normalized_selection_of_selector"] / "definition-input.json"
    write_json(binding_path, weight_binding)

    plan_path = DEST / "frontier-plan.json"
    write_json(plan_path, {
        "schema_version": 1,
        "artifact_kind": "isolated-successive-approximations-frontier-plan",
        "source_commit": SOURCE_COMMIT,
        "source_module": MODULE,
        "source_original_sha256": sha(TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean"),
        "source_port_sha256": sha(TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean"),
        "global_plan_mutated": False,
        "promoted_units": list(UNIT_KEYS.values()),
        "node_order": artifact_plan["node_order"],
        "nodes": reports,
        "n2_inline_helper_ast_witness": ast_path.relative_to(TASK).as_posix(),
        "n2_inline_helper_ast_witness_sha256": sha(ast_path),
        "n2_definition_input": binding_path.relative_to(TASK).as_posix(),
        "n2_definition_input_sha256": sha(binding_path),
        "runtime_sha256": generator.runtime_sha,
        "generator_sha256": sha(SELF),
        "artifact_plan_preview_sha256": sha(TASK / "verification/platform-artifact-plan-preview.json"),
        "unit_plan_preview_sha256": sha(TASK / "verification/platform-unit-plan-preview.json"),
        "output_paths_under_ap4": True,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "proposal_status": "Draft",
        "pending": [
            "actual local child theorem compilation and certificates",
            "each generated file compiled under the 300 second budget",
            "source/generated type and actual proof axiom comparison",
            "platform proposal preparation after local certification",
        ],
    })
    return {"plan": plan_path.relative_to(TASK).as_posix(), "nodes": reports,
            "Lean_started": False, "API_used": False, "validated": False}


if __name__ == "__main__":
    print(json.dumps(generate(), indent=2, ensure_ascii=False))

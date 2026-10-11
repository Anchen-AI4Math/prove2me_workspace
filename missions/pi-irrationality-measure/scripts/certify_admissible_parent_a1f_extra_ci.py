"""Strict pure consumer for the paired a1f auto-generated CI probes."""
from __future__ import annotations

from datetime import datetime
import hashlib
import json
from pathlib import Path

import prepare_admissible_parent_a1f_extra_ci_v3 as prep
import stage_admissible_parent_a1f as parent
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context

STAGE = prep.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "extra-ci-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
PRIVATE_GENERATED = (
    "OAI.PiExponent.interpolationSeparationConstant._proof_1",
    "OAI.PiExponent.weightErrorCoefficient._proof_1",
    "OAI.PiExponent.weightErrorCoefficient._proof_2",
    "OAI.PiExponent.dimension_volume_lt_one._proof_1_1",
)
PRIOR_NAME = "OAI.PiExponent.dimensionV._proof_1"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def expr_refs(expr):
    found = set()
    def walk(node):
        if not isinstance(node, list):
            return
        if len(node) == 3 and node[0] == "const" and isinstance(node[1], str):
            found.add(node[1])
        elif len(node) >= 3 and node[0] == "projection" and isinstance(node[1], str):
            found.add(node[1])
        for item in node[1:]:
            walk(item)
    walk(expr)
    return sorted(found)


def norm_type(ci):
    levels = {name: "u" + str(i) for i, name in enumerate(ci["levelParams"])}
    def walk(node):
        if isinstance(node, list):
            if len(node) == 2 and node[0] == "param" and node[1] in levels:
                return ["param", levels[node[1]]]
            return [walk(item) for item in node]
        return node
    return len(levels), walk(ci["type"])


def owner(ci, kind, module):
    row = ci["owner"]
    need(isinstance(row, dict) and set(row) == {"kind", "moduleIndex", "module"}
         and row["kind"] == kind and row["module"] == module,
         "Actual CI owner module/kind differs: " + ci["name"])
    if kind == "ImportedModule":
        need(type(row["moduleIndex"]) is int and row["moduleIndex"] >= 0,
             "Actual imported module index missing: " + ci["name"])
    else:
        need(row["moduleIndex"] is None,
             "Own-module CI has an imported module index: " + ci["name"])


def full_ci(ci, name, kind, owner_kind, owner_module):
    need(isinstance(ci, dict) and set(ci) == {
        "name", "kind", "levelParams", "closedType", "closedValue", "type", "value",
        "prettyType", "typeRefs", "valueRefs", "axioms", "owner"},
        "Full CI row schema differs: " + name)
    need(ci["name"] == name and ci["kind"] == kind
         and ci["closedType"] is True and ci["closedValue"] is True
         and isinstance(ci["prettyType"], str) and ci["prettyType"],
         "Actual CI name/kind/closedness differs: " + name)
    levels = ci["levelParams"]
    need(isinstance(levels, list) and all(isinstance(x, str) for x in levels)
         and len(levels) == len(set(levels)), "Actual CI universe parameters differ: " + name)
    kernel.checked_expr(ci["type"], set(levels))
    kernel.checked_expr(ci["value"], set(levels))
    for field, expression in (("typeRefs", ci["type"]), ("valueRefs", ci["value"])):
        refs = ci[field]
        need(isinstance(refs, list) and refs == expr_refs(expression),
             "Actual CI references differ from kernel Expr: " + name + "/" + field)
    axioms = ci["axioms"]
    need(isinstance(axioms, list) and axioms == sorted(set(axioms)) and set(axioms) <= STD3,
         "Actual CI axioms differ from Std3: " + name)
    owner(ci, owner_kind, owner_module)
    return ci


def output_json(path, pf):
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Actual JSON output outside exact compiler run: " + str(path))
    return json.loads(path.read_text(encoding="utf-8"))


def verify_prior_dimension_v():
    need(prep.sha(prep.PRIOR_DM_CI) == prep.PRIOR_DM_SHA256,
         "Prior dimensionV private CI certificate changed")
    cert = prep.read(prep.PRIOR_DM_CI)
    need(cert.get("validated") is True and PRIOR_NAME in cert.get("provided_names", []),
         "Prior dimensionV private CI certificate incomplete")
    source = prep.V / "dm-extra-ci/original-extra.json"
    generated = prep.V / "dm-extra-ci/generated-extra.json"
    need(prep.sha(source) == cert["outputs_sha256"][prep.rel(source)]
         and prep.sha(generated) == cert["outputs_sha256"][prep.rel(generated)],
         "Prior dimensionV paired private CI JSON changed")
    src = prep.read(source)["dimensionVHelper"]
    gen = prep.read(generated)["dimensionVHelper"]
    need(src["actualName"] == gen["actualName"] == PRIOR_NAME
         and src["kind"] == gen["kind"] == "theorem"
         and src["value"] is None and gen["value"] is None
         and src["levelParams"] == gen["levelParams"] == []
         and src["type"] == gen["type"]
         and set(src["axioms"]) <= STD3 and set(gen["axioms"]) <= STD3
         and src["owner"]["module"] == prep.SOURCE_MODULES[1]
         and gen["owner"]["module"] == parent.DEF_DIMENSION,
         "Prior dimensionV actual paired CI/type/owner/axioms differ")
    return {"name": PRIOR_NAME, "certificate": prep.rel(prep.PRIOR_DM_CI),
            "certificate_sha256": prep.sha(prep.PRIOR_DM_CI),
            "source_json_sha256": prep.sha(source), "generated_json_sha256": prep.sha(generated),
            "type_sha256": hashlib.sha256(json.dumps(src["type"], sort_keys=True,
                                            separators=(",", ":")).encode()).hexdigest(),
            "source_owner": src["owner"], "generated_owner": gen["owner"],
            "source_axioms": src["axioms"], "generated_axioms": gen["axioms"]}


def validate(*, write):
    prep.check()
    p = prep.read(STAGE / "preparation.json")
    need(p["status"] == "prepared-uncompiled" and p["validated"] is False
         and p["API_used"] is False and p["Lean_started"] is False,
         "Extra-CI prepared state changed")
    records = {}
    outputs = {}
    for side, filename in (("source", "SourceExtraCI.lean"),
                           ("generated", "GeneratedExtraCI.lean")):
        source = STAGE / filename
        manifest = STAGE / (side + ".json")
        pf = context.record(source, manifest, "modecheck", source.stem, STAGE)
        need(pf["data"].get("exit_code") == 0 and pf["data"].get("timed_out") is False
             and pf["data"].get("seconds", 10**9) <= 300
             and pf["data"].get("output_olean") is None
             and pf["data"].get("output_olean_sha256") is None,
             "Exact extra-CI modecheck did not pass: " + side)
        records[side] = pf
        outputs[side] = output_json(STAGE / (side + "-extra.json"), pf)
    prior = verify_prior_dimension_v()
    rows = {}
    discovered = {}
    parent_owner = {
        prep.PARENTS[0]: (prep.SOURCE_MODULES[0], parent.DEF_ADMISSIBLE, "definition"),
        prep.PARENTS[1]: (prep.SOURCE_MODULES[0], parent.DEF_ADMISSIBLE, "definition"),
        prep.PARENTS[2]: (prep.SOURCE_MODULES[1], "GeneratedExtraCI", "theorem"),
    }
    for side in ("source", "generated"):
        doc = outputs[side]
        need(isinstance(doc, dict) and set(doc) == {
            "schemaVersion", "artifactKind", "side", "probeMainModule", "sourceParents",
            "dynamicallyDiscoveredHelperNames", "std3AllowedAxioms"}
            and doc["schemaVersion"] == 1
            and doc["artifactKind"] == "admissible-parent-auto-ci-paired-probe"
            and doc["side"] == side
            and doc["probeMainModule"] == ("SourceExtraCI" if side == "source" else "GeneratedExtraCI")
            and doc["std3AllowedAxioms"] == ["propext", "Classical.choice", "Quot.sound"]
            and isinstance(doc["sourceParents"], list) and len(doc["sourceParents"]) == 3,
            "Exact extra-CI probe envelope differs: " + side)
        actual_names = []
        for index, item in enumerate(doc["sourceParents"]):
            name = prep.PARENTS[index]
            src_owner, gen_owner, kind = parent_owner[name]
            need(isinstance(item, dict) and set(item) == {
                "parent", "immediateAutoProofRefs", "helpers"},
                "Actual parent/helper grouping differs: " + side + "/" + name)
            own_kind = "ImportedModule" if side == "source" or index < 2 else "OwnModule"
            own_module = src_owner if side == "source" else gen_owner
            main = full_ci(item["parent"], name, kind, own_kind, own_module)
            refs = item["immediateAutoProofRefs"]
            helpers = item["helpers"]
            need(isinstance(refs, list) and refs == sorted(set(refs))
                 and isinstance(helpers, list) and len(refs) == len(helpers)
                 and refs == [r for r in main["valueRefs"] if r.startswith(name + "._proof_")],
                 "Immediate private child names differ from actual parent value: " + side + "/" + name)
            if index < 2:
                need(refs == prep.EXPECTED_PARENT_HELPERS[name],
                     "Published Definition private helper names differ: " + side + "/" + name)
            else:
                need(len(refs) == 1, "Dimension inline helper must have one immediate private CI")
                if side == "generated":
                    frefs = prep.read(prep.BASE / "proof-references.json")["rows"]
                    observed = [r["name"] for r in frefs
                                if r.get("name") == name
                                and PRIVATE_GENERATED[-1] in r.get("valueRefs", [])]
                    need(observed == [name] and refs == [PRIVATE_GENERATED[-1]],
                         "Generated inline private name differs from frozen actual f proof references")
            actual_names.extend(refs)
            for expected, helper in zip(refs, helpers, strict=True):
                full_ci(helper, expected, "theorem", own_kind, own_module)
                need(expected not in helper["valueRefs"],
                     "Private theorem CI contains self reference")
            rows[(side, name)] = main
            discovered[(side, name)] = helpers
        need(doc["dynamicallyDiscoveredHelperNames"] == sorted(actual_names)
             and len(actual_names) == len(set(actual_names)) == 4,
             "Actual private CI domain differs from exactly four finite refs: " + side)
    paired = []
    for name in prep.PARENTS:
        source_parent, generated_parent = rows[("source", name)], rows[("generated", name)]
        need(norm_type(source_parent) == norm_type(generated_parent),
             "Source/generated parent kernel types differ: " + name)
        if name != prep.PARENTS[2]:
            need(source_parent["levelParams"] == generated_parent["levelParams"]
                 and source_parent["value"] == generated_parent["value"],
                 "Published Definition parent full values differ: " + name)
        src_helpers, gen_helpers = discovered[("source", name)], discovered[("generated", name)]
        for src, gen in zip(src_helpers, gen_helpers, strict=True):
            need(norm_type(src) == norm_type(gen),
                 "Actual private child kernel types differ: " + name)
            if name != prep.PARENTS[2]:
                need(src["name"] == gen["name"],
                     "Published Definition private child name differs")
            paired.append({"parent": name, "source_name": src["name"],
                           "generated_name": gen["name"], "source_owner": src["owner"],
                           "generated_owner": gen["owner"],
                           "source_type_sha256": hashlib.sha256(json.dumps(src["type"], sort_keys=True,
                               separators=(",", ":")).encode()).hexdigest(),
                           "generated_type_sha256": hashlib.sha256(json.dumps(gen["type"], sort_keys=True,
                               separators=(",", ":")).encode()).hexdigest(),
                           "source_axioms": src["axioms"], "generated_axioms": gen["axioms"]})
    need([r["generated_name"] for r in paired] == list(PRIVATE_GENERATED),
         "Finite four generated auto-CI names differ from exact a1 proof references")
    parent_manifest = prep.read(prep.BASE / "manifest.json")
    allowed = set(parent_manifest["allowed_project_proof_references"]) | set(PRIVATE_GENERATED) | {PRIOR_NAME}
    allowed |= {r["source_name"] for r in paired}
    project_refs = set()
    for side in ("source", "generated"):
        for item in outputs[side]["sourceParents"]:
            for ci in [item["parent"], *item["helpers"]]:
                project_refs.update(ref for key in ("typeRefs", "valueRefs") for ref in ci[key]
                                    if ref.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.")))
    need(project_refs <= allowed,
         "Extra-CI project proof dependencies exceed finite certified closure: "
         + str(sorted(project_refs - allowed)))
    max_seconds = max(pf["data"]["seconds"] for pf in records.values())
    report = {"schema_version": 1, "artifact_kind": "ap6-a1-paired-private-ci-finite-closure-certificate",
        "validated": True, "stage": prep.rel(STAGE), "source_stage": prep.rel(prep.BASE),
        "theorem_name": parent.NAME, "source_commit": parent.COMMIT,
        "preparation_sha256": prep.sha(STAGE / "preparation.json"),
        "source_manifest_sha256": prep.sha(STAGE / "source.json"),
        "generated_manifest_sha256": prep.sha(STAGE / "generated.json"),
        "source_probe_sha256": prep.sha(STAGE / "SourceExtraCI.lean"),
        "generated_probe_sha256": prep.sha(STAGE / "GeneratedExtraCI.lean"),
        "frozen_solution_sha256": prep.sha(prep.SOLUTION),
        "frozen_proof_references_sha256": prep.sha(prep.BASE / "proof-references.json"),
        "source_json_sha256": prep.sha(STAGE / "source-extra.json"),
        "generated_json_sha256": prep.sha(STAGE / "generated-extra.json"),
        "prior_dimension_v": prior, "private_ci_pairs": paired,
        "certified_generated_private_names": list(PRIVATE_GENERATED),
        "finite_project_reference_extension": sorted(set(PRIVATE_GENERATED) | {PRIOR_NAME}),
        "all_extra_ci_project_references_covered": True,
        "no_new_axioms_or_proof_assumptions": True, "Std3_only": True,
        "max_file_seconds": max_seconds,
        "source_preflight_replay": records["source"],
        "generated_preflight_replay": records["generated"],
        "implementation_hashes": {prep.rel(SELF): prep.sha(SELF),
            prep.rel(Path(prep.__file__)): prep.sha(Path(prep.__file__)),
            prep.rel(Path(parent.__file__)): prep.sha(Path(parent.__file__)),
            prep.rel(Path(context.__file__)): prep.sha(Path(context.__file__)),
            prep.rel(Path(kernel.__file__)): prep.sha(Path(kernel.__file__))},
        "Lean_started_by_consumer": False, "API_used": False, "submission_ready": False}
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    if write:
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Existing extra-CI certificate differs; refusing overwrite")
        else:
            CERT.write_bytes(raw)
    else:
        need(CERT.is_file() and CERT.read_bytes() == raw,
             "Existing extra-CI certificate differs from exact evidence replay")
    return report


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = validate(write=args.certify_existing)
    print(json.dumps({"validated": True, "certificate": prep.rel(CERT),
                      "certificate_sha256": prep.sha(CERT),
                      "private_ci_count": len(result["private_ci_pairs"]),
                      "max_file_seconds": result["max_file_seconds"],
                      "Lean_started": False, "API_used": False}, indent=2))

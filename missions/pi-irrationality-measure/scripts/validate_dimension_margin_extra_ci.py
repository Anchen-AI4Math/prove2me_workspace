"""Read-only paired kernel certificate for Dimension-margin automatic CIs."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_dimension_margin_extra_ci as producer
import validate_namespace_context_providers as context
import validate_formal_log_truncation_provider as formalci
import validate_formal_log_f3_extra_ci as comparator
import formal_log_node_refs as refs

TASK, ROOT, STAGE = producer.TASK, producer.ROOT, producer.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "extra-ci-validation.json"
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file
KIND = {"theoremParent": "theorem", "simpHelper": "theorem",
        "definitionWParent": "def", "dimensionWEquation": "theorem",
        "definitionVParent": "def", "dimensionVHelper": "theorem"}
NAMES = {"theoremParent": producer.PARENTS[0], "simpHelper": producer.EXTRAS[0],
         "definitionWParent": producer.PARENTS[1], "dimensionWEquation": producer.EXTRAS[1],
         "definitionVParent": producer.PARENTS[2], "dimensionVHelper": producer.EXTRAS[2]}


def output(side, row, pf, m):
    path = STAGE / (side + "-extra.json")
    formalci.written_during(path, pf)
    data = read(path)
    fail(set(data) != {"schemaVersion", "side", "probeMainModule", "sourceDerivedFrom",
            "theoremParent", "theoremParentValueRefs", "simpHelper",
            "definitionWParent", "definitionWEquationNames", "definitionWEquationInverse",
            "dimensionWEquation", "definitionVParent", "definitionVFullValueRefs",
            "dimensionVHelper", "theoremProofValuesExported"}
         or data["schemaVersion"] != 1 or data["side"] != side
         or data["probeMainModule"] != pf["data"]["actual_module_identity"]
         or data["sourceDerivedFrom"] != "actual-primitive-proof-reference-set"
         or data["theoremProofValuesExported"] is not False,
         "Actual paired extra-CI probe schema/provenance differs")
    parent_module = "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits" if side == "original" else data["probeMainModule"]
    definition_module = producer.base.MODULE if side == "original" else producer.base.PLATFORM
    for field in KIND:
        expected_module = parent_module if field in {"theoremParent", "simpHelper"} else definition_module
        formalci.checked_api_ci(data[field], KIND[field], NAMES[field], expected_module, data["probeMainModule"])
    if side == "original":
        fail(any(data[field]["owner"]["kind"] != "ImportedModule" for field in KIND),
             "Original generated companions must come from source imports")
    else:
        fail(data["theoremParent"]["owner"]["kind"] != "OwnModule"
             or data["simpHelper"]["owner"]["kind"] != "OwnModule"
             or data["definitionWParent"]["owner"]["kind"] != "ImportedModule"
             or data["definitionVParent"]["owner"]["kind"] != "ImportedModule"
             or data["dimensionVHelper"]["owner"]["kind"] != "ImportedModule",
             "Actual generated helper/Definition owner differs")
    theorem_refs = data["theoremParentValueRefs"]
    def_refs = data["definitionVFullValueRefs"]
    fail(theorem_refs != sorted(set(theorem_refs)) or producer.EXTRAS[0] not in theorem_refs
         or def_refs != sorted(set(def_refs)) or producer.EXTRAS[2] not in def_refs,
         "Extra helper is not literal in actual parent proof/full Definition value")
    fail(data["definitionWEquationNames"] != sorted(set(data["definitionWEquationNames"]))
         or producer.EXTRAS[1] not in data["definitionWEquationNames"]
         or data["definitionWEquationInverse"] != producer.PARENTS[1],
         "Equation API getter/inverse primary differs")
    return data, path


def certify():
    p = producer.plan()
    fail(read(STAGE / "preparation.json") != p, "Extra-CI preparation changed")
    manifests = producer.manifests(p)
    preflights, sides, output_hashes = {}, {}, {}
    for name, row in p["files"].items():
        source, mp = TASK / row["source"], TASK / row["manifest"]
        raw, _ = producer.render(row["side"])
        fail(source.read_bytes() != raw or read(mp) != manifests[name],
             "Exact paired extra-CI probe source/manifest changed")
        pf = context.record(source, mp, "modecheck", name, STAGE)
        if row["side"] == "generated":
            dep = next((x for x in pf["data"]["dependency_oleans"] if x["module"] == producer.base.PLATFORM), None)
            fail(dep is None or dep["sha256_before"] != p["definition"]["output_olean_sha256"],
                 "Generated paired probe imported an unvalidated Definition OLean")
        actual, path = output(row["side"], row, pf, p)
        preflights[row["side"]] = pf
        sides[row["side"]] = actual
        output_hashes[rel(path)] = sha(path)
    old, new = sides["original"], sides["generated"]
    for field, kind in KIND.items():
        comparator.source_equal(old[field], new[field], kind)
    fail(old["definitionWEquationNames"] != new["definitionWEquationNames"],
         "Actual source/generated equation getter domains differ")
    actual_refs = read(producer.OLD / "proof-references.json")["rows"]
    graph_names = {json.loads(line)["name"] for line in (producer.V / "decl_graph.jsonl").read_bytes().splitlines()}
    provided = set(p["definition"]["provided_names"])
    inline = {x["generated_name"] for x in read(producer.OLD / "manifest.json")["public_inline_ci_requests"]}
    project_refs = {x for row in actual_refs for x in row["typeRefs"] + row["valueRefs"]
                    if x in graph_names or x.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
    unexpected = project_refs - provided - inline
    fail(unexpected != set(producer.EXTRAS), "Actual proof-reference extra-CI domain differs: " + str(sorted(unexpected)))
    return {"schema_version": 1, "artifact_kind": "dimension-margin-automatic-extra-ci-kernel-certificate",
            "validated": True, "provided_names": producer.EXTRAS,
            "source_commit": p["source_commit"], "source_parent_units": [
                "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:115",
                "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400",
                "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460"],
            "actual_primitive_reference_set_equal": True,
            "paired_names_types_Std3": True, "paired_complete_definition_values": True,
            "actual_equation_getter_and_inverse": True,
            "actual_parent_proof_and_value_literal_references": True,
            "theorem_values_null": True, "source_and_generated_owners": {
                field: {"source": old[field]["owner"], "generated": new[field]["owner"]} for field in KIND},
            "preparation": rel(STAGE / "preparation.json"),
            "preparation_sha256": sha(STAGE / "preparation.json"),
            "source_proof_reference_output": rel(producer.OLD / "proof-references.json"),
            "source_proof_reference_output_sha256": sha(producer.OLD / "proof-references.json"),
            "definition": p["definition"], "input_hashes": p["input_hashes"],
            "implementation_hashes": {rel(x): sha(x) for x in
                [SELF, Path(producer.__file__), Path(comparator.__file__),
                 Path(formalci.__file__), Path(context.__file__), Path(refs.__file__)]},
            "preflights": preflights, "outputs_sha256": output_hashes,
            "max_file_seconds": max(x["data"]["seconds"] for x in preflights.values()),
            "Std3_only": True, "submission_ready": False}


def validate_extra_ci():
    cert = certify()
    fail(not CERT.is_file() or read(CERT) != cert, "Saved paired extra-CI certificate missing/stale")
    return {"path": rel(CERT), "sha256": sha(CERT), "data": cert}


if __name__ == "__main__":
    a = argparse.ArgumentParser(description=__doc__)
    mode = a.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--validate-only", action="store_true")
    args = a.parse_args()
    if args.certify_existing:
        c = certify()
        context.write_exact(CERT, c)
        result = {"validated": True, "certificate": rel(CERT), "sha256": sha(CERT),
                  "provided_names": c["provided_names"], "submission_ready": False}
    else:
        result = validate_extra_ci()
    print(json.dumps(result, indent=2))

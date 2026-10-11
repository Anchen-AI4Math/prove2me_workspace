"""Prepare/review Dimension-margin publication, then advance one API step.

Reuses the already deployed standalone publisher's at-most-once POST driver.
Only --advance uses the API. Each advance checks the saved actual kernel
certificate and immutable payload pins, without rebuilding the 875 graph.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import prepare_dimension_margin_node as inputs
import validate_dimension_margin_node_complete as validation
import publish_standalone_platform_node as driver

TASK, ROOT, STAGE = inputs.TASK, inputs.ROOT, inputs.STAGE
PUB = STAGE / "dimension-margin-publication-v2"
SELF = Path(__file__).resolve()
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def encode(value): return driver.encode(value)
def read(path): return json.loads(path.read_text(encoding="utf-8"))


def need(condition, message):
    if not condition: raise ValueError(message)


def put_exact(path, data):
    if path.exists():
        need(path.read_bytes() == data, "Publication artifact changed; preserve its history: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def metadata(m, certificate):
    w = certificate["source_command_witness"]
    need(w["source_module"] == inputs.MODULE and w["source_graph_name"] == m["theorem_name"]
         and w["port_kernel_type_actual_source_snapshot_verified"] is True
         and w["original_command_boundaries_from_full_file_equal_line_correspondence"] is True,
         "Actual target source command witness differs")
    original = ROOT / w["original_source"]
    source = original.read_bytes()
    start, end = w["original_command_range"]["start"], w["original_command_range"]["end"]
    need(0 <= start < end <= len(source) and sha(original) == w["original_source_sha256"]
         and hashlib.sha256(source[start:end]).hexdigest() == w["original_command_sha256"],
         "Original target command bytes differ")
    first, last = source.count(bytes([10]), 0, start) + 1, source.count(bytes([10]), 0, end - 1) + 1
    need((first, last) == (143, 166), "Original target source line range changed")
    url = ("https://github.com/openai/math/blob/" + SOURCE_COMMIT +
           "/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/Dimension.lean#L143-L166")
    need(len(m["source_components"]) == 2 and [x["source_module"] for x in m["source_components"]] ==
         ["OAI.NumberTheory.PiExponent.Analysis.DimensionLimits", inputs.MODULE],
         "Two source components/order changed")
    witness = {"source_commit": SOURCE_COMMIT, "source_url": url,
               "target_source_module": inputs.MODULE, "target_original_lines": {"start": first, "end": last},
               "target_command": w, "source_components": m["source_components"]}
    return {"theorem_name": m["theorem_name"],
            "theorem_title": "A common index satisfying dimension-error and growth margins",
            "natural_language_statement":
                "Let $\\theta,A,B,C,\\eta,a,b,\\varepsilon,T\\in\\mathbb R$ satisfy "
                "$\\theta>0$, $B>0$, $C>1$, $CB<1$, $C\\theta/B>1$, "
                "$B/A>1$, $\\eta>0$, $a,b\\geq0$, and $\\varepsilon>0$. "
                "There exists an integer $m\\geq1$ for which\n\n"
                "$$\\frac{am+b}{V_m}+100\\frac{K_m}{W_m}<\\varepsilon,\\qquad "
                "T<\\frac{\\eta^2(B/A)^m}{2(m+1)}.$$\n\n"
                "Here $K_m=\\lfloor C^m\\rfloor$, $W_m=(B^m)^{-1}$, and "
                "$V_m=2K_m\\theta^mW_m$. This common large index balances "
                "a decaying dimension error with a growing collision margin.",
            "explanation":
                "The geometric upper bound for the dimension error tends to zero because "
                "$CB<1$ and $C\\theta/B>1$. The collision expression "
                "$\\eta^2(B/A)^m/(2(m+1))$ tends to infinity because $B/A>1$ and $\\eta>0$. "
                "Eventually $C^m\\geq2$ and $m\\geq1$ as well. Intersect these four eventual "
                "conditions and choose one common index $m$. The floor bound for "
                "$\\lfloor C^m\\rfloor$ transfers the upper bound to the actual dimension "
                "error, giving the first strict inequality; the collision limit gives the second. "
                "Source: OpenAI math family 017, commit " + SOURCE_COMMIT + ".",
            "tags": ["openai-pi-exponent-017", "number-theory", "asymptotic-estimate"],
            "source_witness": witness}


def artifacts():
    status = validation.validate_saved()
    need(status["validated"] is True and status["submission_ready"] is False,
         "Actual local Dimension-margin certificate unavailable")
    m = read(STAGE / "manifest.json")
    c = read(validation.CERT)
    meta = metadata(m, c)
    payloads = driver.payloads(PUB, m, meta)
    pins = {"theorem_name": m["theorem_name"], "environment": driver.ENV,
            "proposal_status": "Draft", "manifest_sha256": sha(STAGE / "manifest.json"),
            "validation_sha256": sha(validation.CERT), "metadata_sha256": driver.sha_bytes(encode(meta)),
            "publisher_sha256": sha(Path(driver.__file__)),
            "wrapper_sha256": sha(SELF), "consumer_sha256": sha(Path(validation.__file__)),
            "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
            "payload_sha256": {name: driver.sha_bytes(data) for name, data in payloads.items()},
            "local_node_validated": True, "submission_ready": False,
            "full_tree_ready": False, "verification_payload_is_offline_descriptor": True,
            "verification_theorem_id_late_bound_only": True,
            "definition_id": inputs.dimension_interface(m)["definition_id"]}
    return m, c, meta, payloads, pins


def prepare():
    m, c, meta, payloads, pins = artifacts()
    put_exact(PUB / "manifest.json", (STAGE / "manifest.json").read_bytes())
    put_exact(PUB / "validation.json", validation.CERT.read_bytes())
    put_exact(PUB / "metadata.json", encode(meta))
    for name, data in payloads.items(): put_exact(PUB / name, data)
    put_exact(PUB / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "stage": inputs.rel(PUB),
            "certificate_sha256": sha(validation.CERT), "payload_sha256": pins["payload_sha256"],
            "proposal_status": "Draft", "submission_ready": False}


def advance():
    m, c, meta, payloads, pins = artifacts()
    need(PUB.is_dir() and read(PUB / "preparation.json") == pins,
         "Run --prepare-only once and review exact immutable payloads")
    for name, source in (("manifest.json", STAGE / "manifest.json"),
                         ("validation.json", validation.CERT)):
        need((PUB / name).read_bytes() == source.read_bytes(), "Publication frozen input changed: " + name)
    need((PUB / "metadata.json").read_bytes() == encode(meta), "Publication metadata changed")
    for name, data in payloads.items():
        need((PUB / name).read_bytes() == data, "Publication payload changed: " + name)
    # The reused driver guards every request before and after network I/O.
    # Its one standalone-only global-plan gate is replaced by this saved actual
    # provider-node certificate gate. All other guards and durable POST intents
    # remain the deployed driver's original code.
    def exact_certificate_gate(_manifest):
        fresh = validation.validate_saved()
        need(fresh["sha256"] == pins["validation_sha256"]
             and sha(Path(validation.__file__)) == pins["consumer_sha256"]
             and sha(SELF) == pins["wrapper_sha256"]
             and sha(validation.CERT) == pins["validation_sha256"],
             "Saved actual kernel certificate changed during API step")
    with patch.object(driver.validator, "strict_inputs", exact_certificate_gate):
        driver.advance(PUB, m, meta, pins, payloads)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = p.parse_args()
    print(json.dumps(prepare(), ensure_ascii=False, indent=2) if args.prepare_only else advance())

"""Publish actual analytic and inverse-lattice reductions into the new mission.

No writes are possible until Root freezes independently reviewed exact source.
Every operation has a unique pinned wire; polling and canonical readback are GETs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

import graph_platform_client_2026_10_08 as g

TASK, OUT = g.TASK, g.OUT
PARENTS = {"two": "691b1665-f122-47f7-a3e4-2c28a06055f2", "one": "60c1cf49-6b01-448c-b38a-88dc2fcb8ba0"}
NAMES = {
    "A": ("ZetaNine_AnalyticUniformWeighted", "ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one"),
    "two": ("ZetaNine_GraphBridge_TwoForm", "ZetaNine.GraphBridge.selected_inverse_unbounded_short_independent_pairs"),
    "one": ("ZetaNine_GraphBridge_OneForm", "ZetaNine.GraphBridge.selected_inverse_positive_cone_margin"),
}
TITLES = {
    "A": ("Actual uniform weighted analytic bounds", "Actual quartic-weighted kernel: coefficient-uniform exponential decay"),
    "two": ("Actual selected inverse and weighted two-row margin", "Z9.J route — two short independent integer outputs on unbounded even scales"),
    "one": ("Actual selected inverse and positive Taylor cone", "Z9.TP route — a short integer output in the actual positive Taylor cone"),
}
DESCRIPTIONS = {
    "A": r"""For the actual factorial rational kernel $R_n$ and every rational polynomial $W$ of degree at most four, there is one error sequence $\varepsilon_n\to0$, independent of $W$, such that

$$\left|\sum_{m\ge0}W((m+1)(m+1+n))R_n(m+1)\right|\le e^{(-2641/250+\varepsilon_n)n}\sum_{r=0}^4 |W_r|n^{2r}\qquad(n\ge1).$$

This is an upper bound for the genuine infinite sum and allows arbitrary changing rational quartics. The complete proof establishes the true moments and summability rather than assuming either. It provides analytic decay; it does not construct short integer outputs, prove the lattice margin J, or assert irrationality. The rate is the certified rational lower precision used by the local analytic proof, not a claim of the exact saddle exponent.""",
    "two": r"""Let $F_k$ be the actual five-output matrix on rational quartics, in the order $(B,\rho_3,\rho_5,\rho_7,\rho_9)$, and let $S$ select the constant and ninth-zeta outputs. For integers $b,a$, define

$$E_k(b,a)=(b,a)SF_k^{-1},\qquad H_k(b,a)=\sum_{r=0}^4|E_k(b,a)_r|k^{2r}.$$

The open construction obligation is that a fixed $\delta>0$ exists and, above every cutoff $N$, there is an even $k\ge\max(N,2)$ and two integer pairs $(b_1,a_1),(b_2,a_2)$ with nonzero determinant and both $H_k(b_i,a_i)\le e^{(2641/250-\delta)k}$. This asks for actual inverse coefficient sizes, not small values of the zeta linear forms. Both pairs share the same scale and margin. Only unbounded even scales are required; no eventual-every-scale or density hypothesis is added.

Status: Open. This is a concrete sufficient lattice/height condition of the J route. The selected inverse polynomials are rational; their coefficients are not asserted to be integers. The proved coordinate and HasSum endpoints and the proved uniform analytic estimate turn this condition into two independent exponentially small integer linear forms.""",
    "one": r"""Use the same actual inverse rows $E_k(b,a)$ and weighted norm $H_k(b,a)$ as the two-form branch. For a selected integer output $(b,a)$, its rational quartic is the genuine $W=\operatorname{selectedIntegerMultiplier}(k,b,a)$. Set $u_0=(k+1)(2k+1)$.

The open construction obligation requires a fixed $\delta>0$ and, above every cutoff, an even $k\ge2$ with integers $b,a$, $H_k(b,a)\le e^{(2641/250-\delta)k}$, every Taylor coefficient of the real polynomial $W$ about $u_0$ nonnegative, and $W((k+2)(2k+2))>0$.

The last condition is a finite polynomial sample certificate, not an assumption that the complete zeta linear form is nonzero. Zero initial kernel terms must be removed before using positivity of the tail. The actual HasSum identity then identifies its strictly positive sum with $b+a\zeta(9)$, and the uniform analytic estimate gives exponential smallness. Only unbounded even construction scales are required. Status: Open; neither a Taylor-cone short vector nor the arithmetic height margin is claimed to have been constructed.""",
}
EXPLANATIONS = {
    "A": DESCRIPTIONS["A"] + "\n\nThe submitted file contains the complete original analytic SOURCE proof chain. Each original declaration and whole definition was checked in native author and independent projects and in a fresh platform transplant author and independent project; no imported open theorem is used to close this estimate.",
    "two": r"""This is a genuine reduction of the original two-form obligation to the actual inverse-lattice margin.

The matrix coordinate theorem identifies the selected polynomial's coefficients with $(b,a)SF_k^{-1}$. Its exact HasSum theorem identifies the true kernel sum with $b+a\zeta(9)$. The coefficient-uniform analytic theorem bounds its absolute value by $e^{(-\tau+\varepsilon_k)k}H_k$, where $\tau=2641/250$ and $\varepsilon_k\to0$.

For the fixed open margin $\delta>0$, choose a threshold where $\varepsilon_k<\delta/2$. For any target scale $n$, the open geometric child supplies a common even construction scale $k\ge n$ beyond that threshold and two independent integer outputs. Combining the height and analytic bounds gives each value strictly below $e^{-\delta k/2}\le e^{-\delta n/2}$. Thus $c=\delta/2$ satisfies the original complete quantified statement. The integer determinant is retained. The new child remains Open: this submission proves the implication, not the missing short-vector construction.""",
    "one": r"""This reduction joins the actual positive Taylor tail, exact integer-output sum, inverse coefficient height, and coefficient-uniform analytic bound.

At a construction scale $k$, the actual kernel vanishes at the initial $k$ positive integers. On the remaining tail its factorial product is strictly positive. The Taylor-cone certificate supplies nonnegative values and a strictly positive finite sample; the proved Taylor positivity criterion yields a strictly positive tail sum. Removing the zero head and using the genuine HasSum endpoint identifies this sum with $b+a\zeta(9)$, hence the form is nonzero.

The coordinate theorem equates the polynomial's weighted coefficient height with $H_k(b,a)$. Combining $H_k\le e^{(\tau-\delta)k}$ with the uniform analytic bound and $\varepsilon_k<\delta/2$ gives absolute value below $e^{-\delta k/2}$. A cofinal even scale $k\ge n$ gives the original bound at target scale $n$, with fixed $c=\delta/2$. The new positive-cone short-vector child stays Open; no sign or arithmetic-margin construction is claimed here.""",
}
DEFINITION_DESCRIPTIONS = {
    "A": "Definitions of the actual analytic moment functions, explicit uniform constants and error sequence, actual quartic-weighted rational kernel sequence, and its weighted coefficient height. All functions are built from the original CoefficientMap kernel and the same actual phase function. The uniform estimate is a separate theorem; these definitions introduce no integer-output construction or lattice-margin axiom.",
    "two": "Define the actual row (b,a) S F_n inverse and its five-coordinate weighted absolute norm. Define the missing cofinal-even short-pair margin using two integer output pairs with nonzero determinant and a fixed positive exponential gap. This is a predicate describing an Open geometric construction obligation, not a proof that the predicate holds.",
    "one": "Define the missing cofinal-even positive Taylor-cone margin for the same actual selected inverse polynomial and weighted norm. The predicate requires nonnegative Taylor coefficients at u0 and one positive finite polynomial sample, together with the fixed height gap. It introduces no assertion that such outputs exist and no hypothesis that a zeta sum is already nonzero.",
}


def normalize(text):
    return text.replace("\r\n", "\n")


def reference_parts(raw: bytes):
    text = raw.decode("utf-8")
    match = re.search(r"(?m)^(?:namespace\s|theorem\s)", text)
    assert match and "by sorry" in text
    preamble, formal = text[:match.start()].rstrip(), text[match.start():].rstrip()
    assert not re.search(r"(?m)^\s*(?:def|axiom)\s", preamble)
    return preamble, formal


def prepare():
    config = g.load(OUT / "Root-reviewed-source-plan.json")
    assert config["all_required_native_and_platform_independent_checks_passed"]
    assert config["reviewed_labels"] == list(config["sources"])
    assert config["sources"] and set(config["sources"]) <= set(NAMES)
    result = {}
    for label in config["sources"]:
        files = config["sources"][label]
        snapshots = {}
        for role in ("definition", "reference", "solution"):
            row = files[role]
            path = TASK / row["task_relative"]
            assert path.stat().st_size == row["bytes"] and g.sha(path) == row["sha256"]
            raw = path.read_bytes()
            target = OUT / "source" / label / (role + ".lean")
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                assert target.read_bytes() == raw
            else:
                target.write_bytes(raw)
            snapshots[role] = {"task_relative": target.relative_to(TASK).as_posix(), "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
        preamble, formal = reference_parts((TASK / snapshots["reference"]["task_relative"]).read_bytes())
        definition_name, theorem_name = NAMES[label]
        definition = {"definition_name": definition_name, "definition_title": TITLES[label][0], "definition": (TASK / snapshots["definition"]["task_relative"]).read_bytes().decode("utf-8"), "natural_language_statement": DEFINITION_DESCRIPTIONS[label], "source": config["citations"][label], "env": g.ENV, "private": False}
        problem = {"env": g.ENV, "private": False, "problems": [{"theorem_name": theorem_name, "theorem_title": TITLES[label][1], "formal_statement": formal, "preamble": preamble, "natural_language_statement": DESCRIPTIONS[label], "source": config["citations"][label]}]}
        g.save(OUT / "prepared" / (label + "-definition.json"), definition)
        g.save(OUT / "prepared" / (label + "-problem.json"), problem)
        result[label] = dict(snapshots, theorem_name=theorem_name, definition_name=definition_name)
    g.save(OUT / "prepared" / "source-manifest.json", result)
    print("Exact reviewed source snapshots and full statements prepared; no API or credentials")


def operation_pin(operation, method, path, body, content_type):
    pin_path = OUT / "Root-reviewed-publication-pin.json"
    pin = g.load(pin_path)
    assert pin["all_required_native_and_platform_independent_checks_passed"]
    value = {"method": method, "path": path, "body_sha256": hashlib.sha256(body).hexdigest(), "body_bytes": len(body), "content_type": content_type}
    if operation in pin["operations"]:
        assert pin["operations"][operation] == value
    else:
        pin["operations"][operation] = value
        g.save(pin_path, pin)


def registration(label, kind):
    if kind == "problem":
        assert g.load(OUT / "jobs" / (label + "-definition.json"))["status"] == "PUBLISHED"
        assert g.load(OUT / "canonical" / (label + "-definition.json"))["visibility"] == "public"
    if label == "one" and kind == "definition":
        assert g.load(OUT / "jobs" / "two-definition.json")["status"] == "PUBLISHED"
    body = g.json_wire(g.load(OUT / "prepared" / (label + "-" + kind + ".json")))
    operation, path = label + "-register-" + kind, "/submit-" + kind
    operation_pin(operation, "POST", path, body, "application/json")
    client = g.Client()
    receipt = client.business(operation, "POST", path, body, "application/json")
    assert isinstance(receipt, dict)
    if kind == "definition":
        assert receipt.get("job_id")
    else:
        assert not receipt.get("errors") and len(receipt["jobs"]) == 1
    g.save(OUT / "registrations" / (label + "-" + kind + ".json"), receipt)
    print(label, kind, json.dumps(receipt, ensure_ascii=False))


def poll_job(label, kind):
    receipt = g.load(OUT / "registrations" / (label + "-" + kind + ".json"))
    job_id = receipt["job_id"] if kind == "definition" else receipt["jobs"][0]["job_id"]
    client = g.Client()
    job = client.call("GET", "/publish-jobs/" + job_id)
    g.save(OUT / "jobs" / (label + "-" + kind + ".json"), job)
    print(label, kind, job["status"], job.get("theorem_id"), job.get("error_message", ""))
    assert job["status"] not in {"FAILED", "ERROR"}
    if job["status"] != "PUBLISHED":
        return
    expected = g.load(OUT / "prepared" / (label + "-" + kind + ".json"))
    canonical = client.call("GET", "/theorems/" + job["theorem_id"])
    assert canonical["visibility"] == "public" and canonical["mathlib_rev"] == g.ENV
    if kind == "definition":
        assert canonical["status"] == "Definition"
        assert canonical["theorem_name"] == expected["definition_name"]
        assert canonical["definition"] == expected["definition"]
        assert canonical["theorem_title"] == expected["definition_title"]
        assert canonical["natural_language_statement"] == expected["natural_language_statement"]
        assert canonical["source"] == expected["source"]
    else:
        for field in ("theorem_name", "theorem_title", "formal_statement", "preamble", "natural_language_statement", "source"):
            assert normalize(canonical[field]) == normalize(expected["problems"][0][field]), field
    g.save(OUT / "canonical" / (label + "-" + kind + ".json"), canonical)


def verify(label):
    manifest = g.load(OUT / "prepared" / "source-manifest.json")
    assert g.load(OUT / "jobs" / (label + "-problem.json"))["status"] == "PUBLISHED"
    assert g.load(OUT / "canonical" / (label + "-problem.json"))["visibility"] == "public"
    if label != "A":
        assert g.load(OUT / "proofs" / "A-current.json")["status"] == "ACCEPTED"
    theorem_id = PARENTS[label] if label in PARENTS else g.load(OUT / "jobs" / "A-problem.json")["theorem_id"]
    source_path = TASK / manifest[label]["solution"]["task_relative"]
    assert g.sha(source_path) == manifest[label]["solution"]["sha256"]
    body, content_type = g.multipart_wire(theorem_id, source_path.read_bytes(), EXPLANATIONS[label], "GraphIntegration" + label + "20261008")
    operation_pin(label + "-verify", "POST", "/verify", body, content_type)
    receipt = g.Client().business(label + "-verify", "POST", "/verify", body, content_type)
    assert receipt.get("submission_id")
    g.save(OUT / "proofs" / (label + "-receipt.json"), receipt)
    print(label, "submission", receipt["submission_id"])


def poll_proof(label):
    receipt = g.load(OUT / "proofs" / (label + "-receipt.json"))
    value = g.Client().call("GET", "/verify?submission_id=" + receipt["submission_id"])
    g.save(OUT / "proofs" / (label + "-current.json"), value)
    print(label, value["status"], value.get("error_message", ""))
    assert value["status"] in {"PENDING", "ACCEPTED", "SKETCH_ACCEPTED"}
    if value["status"] != "PENDING":
        assert value["status"] == ("ACCEPTED" if label == "A" else "SKETCH_ACCEPTED")


def milestone(label):
    job = g.load(OUT / "jobs" / (label + "-problem.json"))
    assert job["status"] == "PUBLISHED"
    body = g.json_wire({"title": TITLES[label][1], "milestone_description": DESCRIPTIONS[label], "theorem_id": job["theorem_id"]})
    operation = label + "-milestone"
    path = f"/missions/{g.MISSION}/milestones"
    operation_pin(operation, "POST", path, body, "application/json")
    result = g.Client().business(operation, "POST", path, body, "application/json")
    assert result.get("id")
    g.save(OUT / "milestones" / (label + ".json"), result)
    print(label, "linked to NEW mission", result["id"])


def describe_leaf(label):
    assert label in PARENTS
    assert g.load(OUT / "proofs" / (label + "-current.json"))["status"] == "SKETCH_ACCEPTED"
    if label == "two":
        statement = r"There is a fixed $c>0$ such that, for every sufficiently large target scale $n$, there are integer pairs $(b_1,a_1),(b_2,a_2)$ with $b_1a_2\ne b_2a_1$ and both $|b_i+a_i\zeta(9)|<e^{-cn}$."
    else:
        statement = r"There is a fixed $c>0$ such that, for every sufficiently large target scale $n$, there are integers $b,a$ with $b+a\zeta(9)\ne0$ and $|b+a\zeta(9)|<e^{-cn}$."
    description = statement + r"""

Here $\zeta(9)=\operatorname{Re}(\texttt{riemannZeta}(9:\mathbb C))$. The statement places no coefficient-height or denominator-size bound on the integers. Its exponential tolerance should therefore not be interpreted as a stronger Diophantine approximation rate in denominator size.

Status: Open. The new verified decomposition uses the genuine selected inverse polynomials, their actual integer-output HasSum identity, and the coefficient-uniform analytic bound. The remaining geometric input is the named actual inverse-height margin on cofinal even construction scales; for the one-form route it also includes a positive Taylor-cone certificate. These construction obligations are Open, and the decomposition does not claim that the lattice margin J or irrationality has been proved.

The construction scale $k$ may exceed the target scale $n$: a fixed positive margin and the analytic error tending to zero give $e^{-\delta k/2}\le e^{-\delta n/2}$. This preserves the source's unbounded-even-scale quantifier without adding a density or eventual-every-scale condition.
"""
    path = "/theorems/" + PARENTS[label]
    body = g.json_wire({"natural_language_statement": description, "reason": "Document the newly verified actual inverse/analytic decomposition and remove the unsupported claim of a stronger denominator-size approximation rate."})
    operation = label + "-describe-leaf"
    operation_pin(operation, "PATCH", path, body, "application/json")
    value = g.Client().business(operation, "PATCH", path, body, "application/json")
    assert value["status"] == "Open" and value["mathlib_rev"] == g.ENV
    g.save(OUT / "canonical" / (label + "-parent-after-description.json"), value)
    print(label, "description matches the complete unchanged formal statement")


def readback():
    client = g.Client()
    root = "523f37b8-ae98-406c-a3f7-43aa8e002dd7"
    graph = client.call("GET", "/theorems/" + root + "/graph")
    milestones = client.call("GET", f"/missions/{g.MISSION}/milestones?limit=100&offset=0")
    stamp = datetime.now(timezone.utc).strftime("%H%M%S")
    g.save(OUT / "readback" / (stamp + "-graph.json"), graph)
    g.save(OUT / "readback" / (stamp + "-milestones.json"), milestones)
    report = {"checked_at_utc": datetime.now(timezone.utc).isoformat(), "new_public_mission_id": g.MISSION, "root_status": next(n["status"] for n in graph["nodes"] if n.get("theorem_id") == root), "theorem_nodes": sum(n["node_type"] == "theorem" for n in graph["nodes"]), "definition_nodes": sum(n["node_type"] == "definition" for n in graph["nodes"]), "sketch_nodes": sum(n["node_type"] == "sketch" for n in graph["nodes"]), "edges": len(graph["edges"]), "milestones": len(milestones["milestones"]), "completed_milestones": sum(bool(n.get("completed")) for n in milestones["milestones"]), "old_mission_operations": 0}
    assert report["root_status"] == "Open"
    g.save(OUT / "readback" / (stamp + "-audit.json"), report)
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["prepare", "register-definition", "register-problem", "poll-definition", "poll-problem", "verify", "poll-proof", "milestone", "describe-leaf", "readback"])
    parser.add_argument("label", nargs="?", choices=["A", "two", "one"])
    args = parser.parse_args()
    if args.mode == "prepare": prepare()
    elif args.mode.startswith("register-"): registration(args.label, args.mode.removeprefix("register-"))
    elif args.mode.startswith("poll-") and args.mode != "poll-proof": poll_job(args.label, args.mode.removeprefix("poll-"))
    elif args.mode == "verify": verify(args.label)
    elif args.mode == "poll-proof": poll_proof(args.label)
    elif args.mode == "milestone": milestone(args.label)
    elif args.mode == "describe-leaf": describe_leaf(args.label)
    elif args.mode == "readback": readback()

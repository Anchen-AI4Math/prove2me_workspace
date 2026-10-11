"""SOURCE-only gates/doc checks; no publisher import, network, Lean or secrets."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[3]
SCRIPTS = TASK / "scripts"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read(name):
    path = SCRIPTS / name
    b = path.read_bytes()
    snapshot = HERE / "source-snapshots" / name
    if not snapshot.exists():
        snapshot.write_bytes(b)
    return b.decode("utf-8"), {"task_relative": path.relative_to(TASK).as_posix(), "sha256": sha(b), "bytes": len(b)}


def function(tree, name):
    return next(n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name == name)


def exec_node(node, ns):
    exec(compile(ast.Module(body=[node], type_ignores=[]), "<pure SOURCE gate fixture>", "exec"), ns)


def main():
    target = HERE / "static-review-results.json"
    assert not target.exists()
    sources = {}
    bindings = []
    for name in ["publish_analytic_phase_new_mission_2026_10_07.py", "prepare_analytic_phase_publication_2026_10_07.py",
                 "publish_numerator_pf_new_mission_2026_10_07.py", "audit_new_mission_2026_10_07.py", "publish_mission_2026_10_02.py"]:
        sources[name], binding = read(name)
        bindings.append(binding)
    phase = ast.parse(sources["publish_analytic_phase_new_mission_2026_10_07.py"])
    transport = ast.parse(sources["publish_numerator_pf_new_mission_2026_10_07.py"])
    official = ast.parse(sources["publish_mission_2026_10_02.py"])
    docs_source = ast.parse(sources["audit_new_mission_2026_10_07.py"])
    node = function(phase, "prepare")
    ns = {"PIN": HERE / "fixtures/missing-pin/ABSENT-PIN.json"}
    assert not ns["PIN"].exists()
    exec_node(node, ns)
    try:
        ns["prepare"]()
    except RuntimeError as error:
        missing_pin_error = str(error)
    else:
        raise AssertionError("Missing-pin gate failed")
    assert "no API operation or credentials access" in missing_pin_error
    entrypoint_order = {}
    for tree, names in [(transport, ["registration", "poll_jobs", "verify", "proof_audit"]), (phase, ["audit"])]:
        for name in names:
            fn = function(tree, name)
            calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call)]
            prepare_line = min(n.lineno for n in calls if isinstance(n.func, ast.Name) and n.func.id == "prepare")
            client_line = min(n.lineno for n in calls if (isinstance(n.func, ast.Name) and n.func.id == "client") or
                              (isinstance(n.func, ast.Attribute) and n.func.attr == "client"))
            assert prepare_line < client_line
            entrypoint_order[name] = {"prepare_line": prepare_line, "client_line": client_line}
    docs_pin_node = next(n for n in docs_source.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "PINS" for t in n.targets))
    pins = ast.literal_eval(docs_pin_node.value)
    docs_dir = TASK / "formalization/platform/readback-2026-10-07/api-docs-v0.12.1"
    checked_docs = []
    for name, expected in pins.items():
        b = (docs_dir / name).read_bytes()
        assert sha(b) == expected
        checked_docs.append({"document": name, "sha256": sha(b), "bytes": len(b)})
    compatible = []
    previous = TASK / "formalization/platform/readback-2026-10-04/api-docs-v0.11.8"
    for name in ["mission_captain", "missions", "prove", "contribute"]:
        path = "references/" + name + ".md"
        assert (docs_dir / path).read_bytes() == (previous / path).read_bytes()
        compatible.append(path)
    base_calls = []

    class FakeBase:
        def call(self, method, path, data=None, authenticated=True):
            base_calls.append({"method": method, "path": path})
            return {"fake": True}

    fake_ns = {"official": SimpleNamespace(Client=FakeBase), "OLD": {"old-mission", "old-proposal"}, "NEW": "new-proposal"}
    exec_node(function(transport, "GlobalClient"), fake_ns)
    remote = fake_ns["GlobalClient"]()
    blocked = []
    for method, path, authenticated in [("GET", "/missions/old-mission", True), ("GET", "/mission-proposals/old-proposal", True),
                                       ("PATCH", "/mission-proposals/new-proposal", True), ("POST", "/mission-proposals/new-proposal/items", True),
                                       ("POST", "/missions/new-proposal/make-public", True), ("GET", "/missions", True)]:
        try:
            remote.call(method, path, authenticated=authenticated)
        except AssertionError:
            blocked.append({"method": method, "path": path})
        else:
            raise AssertionError("Unexpected fake delegation")
    assert not base_calls
    remote.call("GET", "/mission-proposals/new-proposal")
    remote.call("POST", "/agent/refresh", authenticated=False)
    official_client = function(official, "Client")
    init = next(n for n in official_client.body if isinstance(n, ast.FunctionDef) and n.name == "__init__")
    health_line = min(n.lineno for n in ast.walk(init) if isinstance(n, ast.Constant) and n.value == "/health")
    credentials_line = min(n.lineno for n in ast.walk(init) if isinstance(n, ast.Constant) and n.value == "credentials.json")
    assert health_line < credentials_line
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "reviewed_SOURCE_bindings": bindings,
              "missing_PIN_actual_expected_RuntimeError": missing_pin_error, "entrypoints_prepare_before_client": entrypoint_order,
              "official_docs_six_exact_pins": checked_docs, "official_endpoint_documents_byte_identical": compatible,
              "transport_client_docs_version": "0.12.1", "health_check_line": health_line, "credentials_read_SOURCE_line": credentials_line,
              "old_mission_and_frozen_proposal_calls_blocked": blocked, "allowed_fake_delegations": base_calls,
              "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0,
              "mathematical_independent_PASS_not_claimed": True}
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"report": str(target), "sha256": sha(target.read_bytes()), "six_docs_pins": len(checked_docs),
                      "blocked_endpoint_cases": len(blocked), "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0}, indent=2))


if __name__ == "__main__":
    main()

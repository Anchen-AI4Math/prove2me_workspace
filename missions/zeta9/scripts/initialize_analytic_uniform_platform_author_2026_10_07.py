"""Initialize a genuinely fresh Root-granted aupa1 author SOURCE project; no Lean."""
import hashlib
import json
from pathlib import Path
import subprocess

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform/analytic-uniform-weighted"
PROJECT = TASK / ".rt/aupa1"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
HANDOFF_SHA = "6b65b8dbb343f41eed4520b382716055cad7aa4fae6154be27028eb6a02c9640"


def binding(p):
    data = p.read_bytes()
    base = TASK if p.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": p.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))


def write_new(p, text):
    assert not p.exists(), p
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def main():
    grant_path = OUT / "Root-platform-author-lane1-grant.json"
    grant = load(grant_path)
    assert grant["Root_explicit_grant"] and grant["owner"] == "factorial_bound_author_1007"
    assert grant["lane"] == 1 and grant["fresh_private_project"] == PROJECT.relative_to(TASK).as_posix()
    handoff_path = OUT / "source-handoff-v1.json"
    assert binding(handoff_path)["sha256"] == HANDOFF_SHA == grant["frozen_SOURCE_handoff_sha256"]
    handoff = load(handoff_path)
    for b in handoff["files"]:
        assert binding(TASK / b["task_relative"]) == b
    assert not PROJECT.exists(), "A genuinely absent private project is required."
    PROJECT.mkdir(parents=True)
    plan = load(OUT / "target-plan.json")
    sources = []
    order = []
    for r in plan["canonical_dependencies"]:
        order.append(r["module"])
    order.append("Definitions.Def_ZetaNine_AnalyticUniformWeighted")
    for path in sorted((OUT / "staged/Definitions").glob("*.lean")):
        relative = path.relative_to(OUT / "staged")
        target = PROJECT / "src" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(path.read_bytes())
        sources.append({"module": relative.as_posix()[:-5].replace("/", "."),
                        "role": "mathematical_definition_SOURCE", "candidate": binding(path), "private_copy": binding(target)})
    for target_plan in plan["targets"]:
        relative = Path(target_plan["local_solution"])
        path = OUT / "staged" / relative
        target = PROJECT / "src" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(path.read_bytes())
        module = relative.as_posix()[:-5].replace("/", ".")
        sources.append({"module": module, "role": "complete_122_proofs_individual_solution_context",
                        "target_key": target_plan["key"], "candidate": binding(path), "private_copy": binding(target)})
    for path in sorted((OUT / "controls").rglob("*.lean")):
        target = PROJECT / "src" / path.name
        assert not target.exists()
        target.write_bytes(path.read_bytes())
        sources.append({"module": path.stem, "role": "complete_actual_audit_SOURCE",
                        "candidate": binding(path), "private_copy": binding(target)})
    manifest = load(WORKSPACE / "lake-manifest.json")
    assert next(p for p in manifest["packages"] if p["name"] == "mathlib")["rev"] == REV
    allowed = {"mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries", "Cli"}
    assert set(p["name"] for p in manifest["packages"]) <= allowed
    (PROJECT / "lake-manifest.json").write_bytes((WORKSPACE / "lake-manifest.json").read_bytes())
    (PROJECT / "lean-toolchain").write_bytes((WORKSPACE / "lean-toolchain").read_bytes())
    write_new(PROJECT / "lakefile.lean", f'''import Lake
open Lake DSL
package zeta9AnalyticUniformPlatformAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib AUPlatformAuthor where
  srcDir := "src"
  roots := #[`Definitions.Def_ZetaNine_AnalyticUniformWeighted]
''')
    write_new(PROJECT / "leaf.py", r'''from pathlib import Path
import json,os,subprocess,sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\users\self_projects\prove2me_workspace\.lake\packages").resolve()
env=dict(os.environ)
selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in env.get(key,'').split(os.pathsep) if raw]
    allowed=[]
    for raw in original:
        resolved=(PROJECT/Path(raw)).resolve()
        if resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(PACKAGES):
            allowed.append(str(resolved))
    own=str(PROJECT/'b/lib/lean') if key=='LEAN_PATH' else str(PROJECT/'src')
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed)
    selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={key:env.get(key) for key in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['AU_PLATFORM_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
sys.exit(subprocess.run(sys.argv[1:],env=env).returncode)
''')
    junction = PROJECT / ".lake/packages"
    junction.parent.mkdir(parents=True)
    result = subprocess.run(["powershell", "-NoProfile", "-Command", "New-Item -ItemType Junction -Path '" + str(junction) + "' -Target '" + str(WORKSPACE / ".lake/packages") + "' | Out-Null"], capture_output=True)
    (OUT / "aupa1-junction-stdout.log").write_bytes(result.stdout)
    (OUT / "aupa1-junction-stderr.log").write_bytes(result.stderr)
    assert result.returncode == 0 and junction.is_junction()
    assert junction.resolve() == (WORKSPACE / ".lake/packages").resolve()
    assert not list((PROJECT / "b").rglob("*.olean"))
    controls_order = ["AUPlatformExprDag", "AUPlatformExprDagValidation"]
    for target in plan["targets"]:
        controls_order.append(target["local_solution"][:-5].replace("/", "."))
        controls_order += ["AUP" + s + "_" + target["key"] for s in ("Types", "Kernel", "Boundary", "Resolver")]
    proof_context_policy = {"fresh_private_project": PROJECT.relative_to(TASK).as_posix(),
                            "Root_grant": binding(grant_path), "frozen_source_handoff": binding(handoff_path),
                            "sources": sources, "source_compile_order": order + controls_order,
                            "all_three_solutions_separate_compiler_environments": True,
                            "foreign_math_objects_copied": 0, "Root_proof_object_fallback": False,
                            "original_candidates_and_author_freeze_unchanged": True,
                            "pinned_package_names": sorted(allowed), "pinned_Mathlib_revision": REV,
                            "configs": [binding(PROJECT / p) for p in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "leaf.py")],
                            "package_junction_real_path": str(junction.resolve()), "actual_Lean_calls": 0,
                            "initializer_script": binding(Path(__file__))}
    write_new(OUT / "platform-native-inputs-v1.json", json.dumps(proof_context_policy, indent=2) + "\n")
    print(json.dumps({"status": "fresh_SOURCE_project_initialized_no_Lean_yet",
                      "private_project": PROJECT.relative_to(TASK).as_posix(), "source_modules": len(sources),
                      "policy": binding(OUT / "platform-native-inputs-v1.json")}))


if __name__ == "__main__":
    main()

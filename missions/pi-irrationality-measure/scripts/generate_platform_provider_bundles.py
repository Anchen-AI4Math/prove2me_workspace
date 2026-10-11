#!/usr/bin/env python3
"""Stage proved-provider Definition bundles from an isolated provider plan.

This script is preview-only and requires the authoritative complete 875-module
AST ownership snapshot.  It inherits the existing Definition generator's exact
AST subtraction/import/rename implementation, but injects only a freshly
reconstructed and checked provider variant and writes exclusively below
``verification/providers-complete-preview``.  The historical 799-provider
stages, including published validation evidence, are never overwritten.

No Lean process or network request is started.  Snapshot source files are
staged for later preflight.  Their exporter omits theorem proof values, retains
ordinary definition values, and resolves every private constant by the unique
``privateToUserName?`` plus owning-module pair rather than a fabricated private
kernel name.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
OUTPUT = VERIFICATION / "providers-complete-preview"
PROVIDER_PLAN_DIR = VERIFICATION / "provider-plans" / "all-shared-public"

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_platform_bundles as base_generator  # noqa: E402
from plan_platform_artifacts import build_artifacts  # noqa: E402
from plan_platform_units_providers import promote  # noqa: E402

MINIMUM_PROVIDER_NAMES = {
    "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff",
    "OAI.PiExponent.GeneralCartierDegreeLength.finite_zeroIdeal_of_mono",
    "OAI.PiExponent.primeRectangular_maps_maximal",
}
PUBLISHED = {
    "OAI.NumberTheory.PiExponent.Analysis.Collision": {
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_Collision",
        "definition_id": "e7e8f0df-8e23-43cf-aaac-4464d5084082",
        "validation": "verification/definition-validation/Def_OAI_NumberTheory_PiExponent_Analysis_Collision/validation.json",
    },
    "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision": {
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision",
        "definition_id": "82d606c5-f704-4255-8948-696d425a76a1",
        "validation": "verification/definition-validation/Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision/validation.json",
    },
    "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent": {
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent",
        "definition_id": "bdec8e94-fc3a-4f5a-9aef-c76bd32695d0",
        "validation": "verification/providers-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent/provider-validation.json",
    },
}


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # A short sibling temp name avoids Windows' legacy path-length ceiling for
    # long generated module stems while retaining atomic replacement.
    temporary = path.parent / f".__provider_{os.getpid()}.tmp"
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def workspace_relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK).as_posix()


def resolve_recorded_input(relative: str) -> Path:
    task_path = (TASK / relative).resolve()
    workspace_path = (ROOT / relative).resolve()
    if task_path.is_relative_to(TASK) and task_path.is_file():
        return task_path
    if workspace_path.is_relative_to(ROOT) and workspace_path.is_file():
        return workspace_path
    raise ValueError("Recorded provider input is missing: " + relative)


def comparable(record):
    return {key: value for key, value in record.items()
            if key not in {"provisional", "ready_for_generation"}}


def load_graph_rows(path: Path):
    raw = path.read_bytes()
    rows, hashes = {}, {}
    for line in raw.splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        rows[row["name"]] = row
        hashes[row["name"]] = sha_bytes(line)
    return rows, hashes, sha_bytes(raw)


def module_closure(roots, artifacts):
    todo = list(roots)
    seen = set()
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        bundle = artifacts["definition_bundles"].get(module)
        if bundle:
            todo.extend(bundle["imports"])
    return seen


def walk_syntax(node):
    yield node
    for child in node.get("children", []):
        yield from walk_syntax(child)


def build_live_import_inventory(state):
    """Build a provider-local import index from the append-only Stage 2 capture."""
    source_prefix = (TASK / "port/lean").relative_to(ROOT).as_posix() + "/"
    owned_modules = {path.removeprefix(source_prefix).removesuffix(".lean").replace("/", ".")
                     for path in state["inputs"] if path.startswith(source_prefix)}
    modules, facts_inputs = {}, {}
    for relative, entry in sorted(state["stage2"].items()):
        facts_path = ROOT / entry["facts"]
        if sha(facts_path) != entry["facts_sha256"]:
            raise ValueError("Live Stage 2 import facts changed: " + relative)
        source_path = TASK / "port/lean" / relative
        source_sha = sha(source_path)
        if source_sha != entry["preflight"]["source_sha256"]:
            raise ValueError("Live Stage 2 source changed: " + relative)
        facts_inputs[entry["facts"]] = entry["facts_sha256"]
        facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        headers = [fact["syntax"] for fact in facts if fact["kind"] == "header"]
        if len(headers) != 1:
            raise ValueError("Expected one parser header in live facts: " + relative)
        imports = []
        for node in walk_syntax(headers[0]):
            if node["syntaxKind"] != "Lean.Parser.Module.import":
                continue
            identifiers = [child for child in walk_syntax(node) if child.get("identifier") is not None]
            if len(identifiers) != 1:
                raise ValueError("Unsupported parser import syntax: " + relative)
            identifier = identifiers[0]
            name = identifier["identifier"]
            imports.append({"module": name, "project": name in owned_modules,
                            "command_range": node["range"], "name_range": identifier["range"]})
        name = relative.removesuffix(".lean").replace("/", ".")
        modules[name] = {
            "source": source_path.relative_to(ROOT).as_posix(),
            "source_sha256": source_sha,
            "facts": entry["facts"],
            "facts_sha256": entry["facts_sha256"],
            "imports": imports,
        }
    closures = {}
    for name in modules:
        todo, seen, external, pending = [name], set(), set(), set()
        while todo:
            current = todo.pop()
            if current in seen:
                continue
            seen.add(current)
            if current not in modules:
                pending.add(current)
                continue
            for dependency in modules[current]["imports"]:
                if dependency["project"]:
                    todo.append(dependency["module"])
                else:
                    external.add(dependency["module"])
        closures[name] = {"external_imports": sorted(external),
                          "unextracted_project_modules": sorted(pending)}
    return {"complete_extraction": state.get("complete", False), "modules": modules,
            "transitive_external_imports": closures,
            "stage2_entries_at_capture": len(state["stage2"]),
            "extraction_state_sha256": sha(VERIFICATION / "extraction-state.json"),
            "facts_input_hashes": facts_inputs}


def unit_closure(roots, units):
    todo = list(roots)
    seen = set()
    while todo:
        key = todo.pop()
        if key in seen:
            continue
        seen.add(key)
        todo.extend(units[key]["direct_unit_dependencies"])
    return seen


PROVIDER_EXPORTER = r'''
namespace PiExponentProviderSnapshot

open Lean Meta

structure ProviderRequest where
  sourceGraphName : String
  expectedUserName : String
  expectedPublicName : String
  expectedModule : String
  expectedKind : String
  sourceWasPrivate : Bool
  commandUnit : String
  declGraphSha256 : String
  declGraphRowSha256 : String

def moduleFor? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

def envKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def kindMetadata : ConstantInfo → Json
  | .thmInfo _ => Json.mkObj [("proofValueExported", toJson false)]
  | .defnInfo d => Json.mkObj [("valueExported", toJson true), ("safety", toJson (reprStr d.safety))]
  | .axiomInfo a => Json.mkObj [("isUnsafe", toJson a.isUnsafe)]
  | .opaqueInfo o => Json.mkObj [("valueExported", toJson false), ("isUnsafe", toJson o.isUnsafe)]
  | .inductInfo i => Json.mkObj [("numParams", toJson i.numParams), ("numIndices", toJson i.numIndices),
      ("all", toJson (i.all.map Name.toString)), ("constructors", toJson (i.ctors.map Name.toString)),
      ("numNested", toJson i.numNested), ("isRecursive", toJson i.isRec),
      ("isUnsafe", toJson i.isUnsafe), ("isReflexive", toJson i.isReflexive)]
  | .ctorInfo c => Json.mkObj [("inductive", toJson c.induct.toString),
      ("constructorIndex", toJson c.cidx), ("numParams", toJson c.numParams),
      ("numFields", toJson c.numFields), ("isUnsafe", toJson c.isUnsafe)]
  | .recInfo r => Json.mkObj [("all", toJson (r.all.map Name.toString)),
      ("numParams", toJson r.numParams), ("numIndices", toJson r.numIndices),
      ("numMotives", toJson r.numMotives), ("numMinors", toJson r.numMinors),
      ("ruleConstructors", toJson (r.rules.map (fun rule => rule.ctor.toString))),
      ("supportsK", toJson r.k), ("isUnsafe", toJson r.isUnsafe)]
  | .quotInfo _ => Json.mkObj []

def isClosed (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar && !e.hasLooseBVars

def ownedBy (env : Environment) (name : Name) (expected : String) : Bool :=
  match moduleFor? env name with
  | some moduleName => moduleName.toString == expected
  | none => false

def resolveRequest (env : Environment) (request : ProviderRequest) : MetaM Name := do
  let mut candidates : Array Name := #[]
  for (actualName, _) in env.constants.toList do
    if ownedBy env actualName request.expectedModule then
      if request.sourceWasPrivate then
        if (Lean.privateToUserName? actualName).map Name.toString == some request.expectedUserName then
          candidates := candidates.push actualName
      else if actualName.toString == request.expectedPublicName then
        candidates := candidates.push actualName
  unless candidates.size == 1 do
    throwError "Expected one declaration for source={request.sourceGraphName}, user={request.expectedUserName}, module={request.expectedModule}; found {candidates.size}"
  return candidates[0]!

def exportProviderSnapshotJsonl (requests : Array ProviderRequest) (output : String) : MetaM Unit := do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk output .write
  for request in requests do
    let name ← resolveRequest env request
    let some ci := env.find? name | throwError "Resolved declaration is absent: {name}"
    let actualKind := envKind ci
    unless actualKind == request.expectedKind do
      throwError "Declaration kind mismatch for {name}: expected={request.expectedKind}, actual={actualKind}"
    unless isClosed ci.type do
      throwError "Declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | _ => none
    if let some v := value then
      unless isClosed v do
        throwError "Definition value is not closed: {name}"
    let axioms ← Lean.collectAxioms name
    let axiomNames := axioms.toList.map Name.toString
      |>.mergeSort (fun a b => compare a b == .lt)
    let row := Json.mkObj [
      ("schemaVersion", toJson 1),
      ("sourceGraphName", toJson request.sourceGraphName),
      ("resolvedName", toJson name.toString),
      ("resolvedUserName", toJson ((Lean.privateToUserName? name).getD name).toString),
      ("sourceWasPrivate", toJson request.sourceWasPrivate),
      ("resolvedViaPrivateUserNameAndModuleOwner", toJson request.sourceWasPrivate),
      ("module", toJson request.expectedModule),
      ("commandUnit", toJson request.commandUnit),
      ("declGraphSha256", toJson request.declGraphSha256),
      ("declGraphRowSha256", toJson request.declGraphRowSha256),
      ("envKind", toJson actualKind),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true),
      ("closedValue", value.map (fun _ => toJson true) |>.getD Json.null),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
      ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
      ("axioms", toJson axiomNames),
      ("kindMetadata", kindMetadata ci)]
    handle.putStrLn row.compress
  handle.flush

end PiExponentProviderSnapshot
'''


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def render_request(row):
    fields = [
        ("sourceGraphName", row["source_graph_name"]),
        ("expectedUserName", row["expected_user_name"]),
        ("expectedPublicName", row["expected_public_name"]),
        ("expectedModule", row["expected_module"]),
        ("expectedKind", row["expected_kind"]),
        ("sourceWasPrivate", row["source_was_private"]),
        ("commandUnit", row["command_unit"]),
        ("declGraphSha256", row["decl_graph_sha256"]),
        ("declGraphRowSha256", row["decl_graph_row_sha256"]),
    ]
    values = []
    for key, value in fields:
        rendered = "true" if value is True else "false" if value is False else lean_string(value)
        values.append(f"{key} := {rendered}")
    return "    { " + ", ".join(values) + " }"


def render_snapshot(core: str, imported_module: str, requests, output: Path):
    body = "import Lean\nimport " + imported_module + "\n\n" + core.rstrip() + "\n\n" + PROVIDER_EXPORTER
    body += "\nopen PiExponentProviderSnapshot\n\ndef providerRequests : Array ProviderRequest := #[\n"
    body += ",\n".join(render_request(row) for row in requests)
    body += "\n  ]\n\nrun_meta do\n"
    body += "  exportProviderSnapshotJsonl providerRequests " + lean_string(workspace_relative(output)) + "\n"
    return body


class ProviderGenerator(base_generator.Generator):
    def __init__(self):
        super().__init__(preview=True)
        if (not self.state.get("complete") or len(self.state.get("stage2", {})) != 875
                or self.inventory.get("complete_extraction") is not True
                or self.inventory.get("extracted_modules") != 875):
            raise ValueError("Provider previews require the complete 875-module extraction")
        state_sha = self.input_hashes.pop("verification/extraction-state.json")
        live_imports = build_live_import_inventory(self.state)
        live_import_path = OUTPUT / "live-import-inventory.json"
        write_json(live_import_path, live_imports)
        self.imports = live_imports
        self.capture_observations = {
            "extraction_state": {
                "path": "verification/extraction-state.json",
                "sha256_at_capture": state_sha,
                "stage2_entries_at_capture": len(self.state["stage2"]),
                "complete_at_capture": bool(self.state.get("complete", False)),
                "dependency": False,
                "reason": "Append-only extraction progress outside a bundle's project import closure does not alter that bundle.",
            },
            "live_import_inventory": {
                "path": task_relative(live_import_path),
                "sha256_at_capture": sha(live_import_path),
                "dependency": False,
                "reason": "Per-bundle source/facts import provenance below is the exact dependency set.",
            },
        }
        self.base_unit_plan = self.unit_plan
        self.base_artifact_plan = self.artifact_plan
        pending = self.base_unit_plan.get("source_declarations_pending_ast")
        if (self.base_unit_plan.get("complete_extraction") is not True
                or self.base_artifact_plan.get("complete_extraction") is not True
                or pending is None or pending or self.inventory.get("unmatched")):
            raise ValueError("Provider previews require complete AST ownership; pending="
                             + str((pending or [])[:20]))
        self.provider_unit_path = PROVIDER_PLAN_DIR / "platform-unit-plan-provider-variant.json"
        self.provider_artifact_path = PROVIDER_PLAN_DIR / "platform-artifact-plan-provider-variant.json"
        self.provider_manifest_path = PROVIDER_PLAN_DIR / "provider-plan-manifest.json"
        provider_manifest = read_json(self.provider_manifest_path)
        if provider_manifest.get("basis") != "verified complete 875-module preview":
            raise ValueError("Provider plan is not based on the complete 875-module preview")
        for relative, expected in provider_manifest["input_hashes"].items():
            path = resolve_recorded_input(relative)
            if sha(path) != expected:
                raise ValueError("Provider plan input changed: " + relative)
        stored_plan = read_json(self.provider_unit_path)
        roots = set(stored_plan.get("provider_variant", {}).get("root_units", []))
        if not roots:
            raise ValueError("Stored all-shared provider plan has no explicit root units")
        fresh_plan, closure = promote(self.base_unit_plan, roots, "all-shared-public")
        if comparable(fresh_plan) != comparable(stored_plan):
            raise ValueError("Stored all-shared provider unit plan differs from fresh promotion")
        fresh_artifacts = build_artifacts(fresh_plan, self.scopes, self.reuse)
        fresh_artifacts["provider_variant"] = fresh_plan["provider_variant"]
        stored_artifacts = read_json(self.provider_artifact_path)
        if comparable(fresh_artifacts) != comparable(stored_artifacts):
            raise ValueError("Stored all-shared provider artifact plan differs from fresh rebuild")
        if (not stored_plan.get("provisional") or stored_plan.get("ready_for_generation")
                or not stored_artifacts.get("provisional") or stored_artifacts.get("ready_for_generation")):
            raise ValueError("Provider preview must remain provisional and non-final")
        self.unit_plan = stored_plan
        self.artifact_plan = stored_artifacts
        self.units = {unit["id"]: unit for unit in stored_plan["units"]}
        self.owner = {name: key for key, unit in self.units.items() for name in unit["graph_names"]}
        self.provider_roots = roots
        self.provider_closure = closure
        self._facts_by_module = {}
        for path in [self.provider_unit_path, self.provider_artifact_path,
                     self.provider_manifest_path,
                     Path(__file__).resolve(), TASK / "scripts/plan_platform_units_providers.py"]:
            self.input_hashes[task_relative(path)] = sha(path)
        self.graph_rows, self.graph_row_hashes, self.graph_sha = load_graph_rows(
            VERIFICATION / "decl_graph.jsonl")
        if self.graph_sha != self.input_hashes["verification/decl_graph.jsonl"]:
            raise ValueError("Provider graph hash differs from the base generator graph")
        self.new_private_units = {
            key for key in closure
            if self.units[key]["private"]
            and {u["id"]: u for u in self.base_unit_plan["units"]}[key]["category"] not in base_generator.DEFINITION_CATEGORIES
        }

    def bundle_import_provenance(self, module):
        """Exact source/facts inputs that determine one rewritten import closure."""
        todo, seen, rows = [module], set(), []
        while todo:
            current = todo.pop()
            if current in seen:
                continue
            seen.add(current)
            info = self.imports["modules"].get(current)
            if info is None:
                raise ValueError("Missing import provenance module: " + current)
            source = ROOT / info["source"]
            facts = ROOT / info["facts"]
            if sha(source) != info["source_sha256"] or sha(facts) != info["facts_sha256"]:
                raise ValueError("Import provenance input changed: " + current)
            rows.append({
                "module": current,
                "source": info["source"],
                "source_sha256": info["source_sha256"],
                "facts": info["facts"],
                "facts_sha256": info["facts_sha256"],
            })
            for dependency in info["imports"]:
                if dependency["project"]:
                    if dependency["module"] not in self.imports["modules"]:
                        raise ValueError("Unextracted project import in provider provenance: " + dependency["module"])
                    todo.append(dependency["module"])
        return sorted(rows, key=lambda row: row["module"])

    def source_platform_name(self, graph_name, unit):
        if unit["deprivate"]:
            if len(unit["graph_names"]) != 1 or unit["id"] not in self.names:
                raise ValueError("Deprivate snapshot needs one validated explicit generated name: " + unit["id"])
            return self.names[unit["id"]]
        return self.public_name_by_constant.get(graph_name, graph_name)

    @staticmethod
    def _range_key(value):
        return (value["start"]["offset"], value["end"]["offset"])

    def _module_facts(self, module):
        if module not in self._facts_by_module:
            info = self.imports["modules"].get(module)
            if info is None:
                raise ValueError("No authoritative parser facts for provider module: " + module)
            facts_path = ROOT / info["facts"]
            if sha(facts_path) != info["facts_sha256"]:
                raise ValueError("Provider parser facts changed: " + module)
            self._facts_by_module[module] = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        return self._facts_by_module[module]

    def _project_namespace_owners(self, identifier, namespace):
        """Resolve an open identifier only when the project owner is unambiguous."""
        candidates = set()
        if identifier.startswith(("OAI.", "PiExponent.")):
            candidates.add(identifier)
        if identifier.startswith("PiExponent."):
            candidates.add("OAI." + identifier)
        parts = namespace.split(".") if namespace else []
        for size in range(len(parts), 0, -1):
            candidates.add(".".join(parts[:size] + [identifier]))
        matches = defaultdict(set)
        for name, row in self.graph_rows.items():
            displayed = {name, row["userName"]}
            for prefix in candidates:
                if any(item == prefix or item.startswith(prefix + ".") for item in displayed):
                    matches[prefix].add(row["module"])
        exact = [(prefix, owners) for prefix, owners in matches.items() if len(owners) == 1]
        if not exact:
            if not matches:
                return None
            return {"owner_module": None,
                    "ambiguous_owner_modules": sorted(set().union(*matches.values())),
                    "resolved_prefixes": sorted(matches)}
        # Prefer the most-qualified successful interpretation.  If equally
        # qualified interpretations disagree, the syntax is ambiguous and must
        # not be silently assigned to one module.
        width = max(prefix.count(".") for prefix, _ in exact)
        owners = {next(iter(value)) for prefix, value in exact if prefix.count(".") == width}
        if len(owners) != 1:
            return {"owner_module": None,
                    "ambiguous_owner_modules": sorted(owners),
                    "resolved_prefixes": sorted(prefix for prefix, _ in exact
                                                if prefix.count(".") == width)}
        owner = next(iter(owners))
        prefixes = sorted(prefix for prefix, value in exact
                          if prefix.count(".") == width and owner in value)
        return {"owner_module": owner, "resolved_prefixes": prefixes}

    def module_boundary_risks(self, module):
        """Reject graph and retained-syntax dependencies outside the bundle plan."""
        bundle = self.artifact_plan["definition_bundles"][module]
        selected = set(bundle["units"])
        risks = []
        pending = set(self.base_unit_plan.get("source_declarations_pending_ast", []))
        for key in sorted(selected):
            todo = list(self.units[key]["graph_names"])
            seen = set()
            while todo:
                name = todo.pop()
                if name in seen:
                    continue
                seen.add(name)
                if name in pending:
                    risks.append({"unit": key, "reason": "kernel graph dependency has no AST command owner",
                                  "source_graph_name": name})
                row = self.graph_rows.get(name)
                if row:
                    todo.extend(row["typeDeps"] + row["valueDeps"] + row["constructors"])

        facts = self._module_facts(module)
        commands = {self._range_key(fact["syntax"]["range"]): fact["syntax"]
                    for fact in facts if fact.get("kind") == "command"
                    and fact.get("syntax", {}).get("range")}
        retained = {}
        for key in sorted(selected):
            scope = self.scope_for(self.units[key])
            for context in scope["context_commands"]:
                retained[self._range_key(context["range"])] = (context, scope["namespace"])
        certified = set(self.reuse_by_module) | set(PUBLISHED)
        planned_imports = set(bundle["imports"]) | certified
        todo = [module]
        original_project_closure = set()
        while todo:
            current = todo.pop()
            if current in original_project_closure:
                continue
            original_project_closure.add(current)
            for dependency in self.imports["modules"].get(current, {}).get("imports", []):
                if dependency["project"]:
                    todo.append(dependency["module"])
        for key, (context, namespace) in sorted(retained.items()):
            if context["syntaxKind"] != "Lean.Parser.Command.open":
                continue
            syntax = commands.get(key)
            if syntax is None:
                risks.append({"reason": "retained open command has no exact authoritative syntax fact",
                              "command_range": context["range"]})
                continue
            identifiers = sorted({node["identifier"] for node in walk_syntax(syntax)
                                  if node.get("identifier")})
            for identifier in identifiers:
                ownership = self._project_namespace_owners(identifier, namespace)
                if ownership is None:
                    continue
                owner = ownership["owner_module"]
                if owner is None:
                    owners = set(ownership["ambiguous_owner_modules"])
                    if module in owners or owners & planned_imports:
                        continue
                    original_candidates = sorted(owners & original_project_closure)
                    risks.append({
                        "reason": ("retained open namespace has project owner imports removed"
                                   if original_candidates else
                                   "retained open namespace has ambiguous project owner modules"),
                        "identifier": identifier,
                        "resolved_prefixes": ownership["resolved_prefixes"],
                        "owner_modules": sorted(owners),
                        "original_import_owner_candidates": original_candidates,
                        "command_range": context["range"],
                    })
                    continue
                if owner != module and owner not in planned_imports:
                    risks.append({
                        "reason": "retained open namespace has a unique project owner module not imported",
                        "identifier": identifier,
                        "resolved_prefixes": ownership["resolved_prefixes"],
                        "owner_module": owner,
                        "command_range": context["range"],
                    })
        return risks

    def module_name_risk(self, module):
        reasons = self.module_boundary_risks(module)
        bundle = self.artifact_plan["definition_bundles"][module]
        for key in bundle["units"]:
            unit = self.units[key]
            if key in self.name_errors:
                reasons.append({"unit": key, "reason": self.name_errors[key]})
            if unit["deprivate"]:
                override = self.overrides_by_unit.get(key)
                if (override is None
                        or not override.get("binding_and_reference_rewrite_validated")
                        or not override.get("kernel_type_comparison_validated")):
                    reasons.append({"unit": key, "reason": "deprivate override is not fully validated"})
            if unit["private"] and not unit["deprivate"]:
                reasons.append({"unit": key, "reason": (
                    "private provider dependency awaits actual privateToUserName plus module-owner CI"
                    if key in self.new_private_units else
                    "existing private Definition dependency has no actual privateToUserName plus module-owner CI")})
            if unit["is_instance_command"] or unit["is_local_instance"]:
                reasons.append({"unit": key, "reason": "instance command is outside the ordinary public theorem/def provider interface"})
            for name in unit["graph_names"]:
                if name in self.public_name_by_constant:
                    override = next(item for item in self.source_overrides["planned_overrides"]
                                    if item["source_name"] == name)
                    if not override["lean_or_type_validated"]:
                        reasons.append({"unit": key, "reason": "source theorem rename is not Lean/type validated"})
        return reasons

    def stage_bundle(self, module: str, batch: str):
        boundary_risks = self.module_boundary_risks(module)
        if boundary_risks:
            raise ValueError("Provider source boundary is incomplete: "
                             + json.dumps(boundary_risks, ensure_ascii=False))
        # Reuse the exact accepted generator implementation, redirecting only
        # its process-local output root to a private engine directory.
        # A PID-scoped engine directory prevents two read-only preview runs from
        # deleting or replacing one another's temporary accepted-generator output.
        # Keep this close to the task root: Windows' legacy path limit can be
        # exceeded by long generated module names once ``.manifest.json`` is
        # appended inside the accepted generator.
        engine_dest = TASK / ".pe" / str(os.getpid()) / ("m" if batch.startswith("minimum") else "s")
        original_dest = base_generator.DEST
        base_generator.DEST = engine_dest
        try:
            report = super().generate(module)
        finally:
            base_generator.DEST = original_dest
        if report.get("reused"):
            return report
        engine_output = ROOT / report["output"]
        engine_manifest = engine_output.with_suffix(".manifest.json")
        result = engine_output.read_bytes()
        target = OUTPUT / batch / Path(*report["platform_module"].split(".")).with_suffix(".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(result)
        engine_output.unlink()
        if engine_manifest.exists():
            engine_manifest.unlink()
        # The accepted generator creates only this temporary file and its
        # manifest below our PID-scoped root.  Prune empty parents without a
        # recursive delete, stopping before another process' PID directory.
        directory = engine_output.parent
        stop = engine_dest.parent.parent
        while directory != stop:
            try:
                directory.rmdir()
            except OSError:
                break
            directory = directory.parent
        report["engine_output_removed"] = True
        report["output"] = workspace_relative(target)
        report["output_sha256"] = sha(target)
        report["provider_plan"] = task_relative(self.provider_unit_path)
        report["provider_plan_sha256"] = sha(self.provider_unit_path)
        report["provider_artifact_plan"] = task_relative(self.provider_artifact_path)
        report["provider_artifact_plan_sha256"] = sha(self.provider_artifact_path)
        report["provider_variant"] = "all-shared-public"
        report["accepted_generator_logic_reused"] = True
        report["accepted_outputs_untouched"] = True
        report["preview_only"] = True
        report["lean_started"] = False
        report["api_used"] = False
        report["input_hashes"] = dict(sorted(self.input_hashes.items()))
        report["capture_observations"] = self.capture_observations
        report["import_provenance"] = self.bundle_import_provenance(module)
        manifest_path = target.with_suffix(".manifest.json")
        write_json(manifest_path, report)
        self.write_ledgers(module, batch, report, target)
        self.write_snapshots(module, batch, report, target)
        return report

    def write_ledgers(self, module, batch, report, target):
        stage = target.parent.parent / "ledgers" / target.stem
        bundle = self.artifact_plan["definition_bundles"][module]
        selected = set(bundle["units"])
        closure = unit_closure(selected, self.units)
        command_rows = []
        for key in sorted(closure):
            unit = self.units[key]
            command_rows.append({
                "unit": key, "source_module": unit["module"], "category": unit["category"],
                "in_this_bundle": key in selected, "graph_names": unit["graph_names"],
                "range": {"start": unit["start"], "end": unit["end"]},
                "source_sha256": unit["source_sha256"],
                "direct_unit_dependencies": unit["direct_unit_dependencies"],
            })
        write_json(stage / "command-closure.json", {
            "source_module": module, "root_units": sorted(selected),
            "closure_units": command_rows, "closed": True,
            "definitions_only": all(self.units[key]["category"] in base_generator.DEFINITION_CATEGORIES
                                    for key in closure),
        })
        inventory = self.modules[module]
        source = ROOT / report["source"]
        data = source.read_bytes()
        selected_offsets = {self.units[key]["start"]["offset"] for key in selected}
        helper_units = {item["unit"] for item in report["elaboration_only_helpers"]}
        selected_offsets |= {int(key.rpartition(":")[2]) for key in helper_units}
        ast_rows = []
        for item in inventory["units"]:
            a, b = item["start"]["offset"], item["end"]["offset"]
            ast_rows.append({
                "start": item["start"], "end": item["end"], "graph_names": item["graph_names"],
                "selected": a in selected_offsets, "command_bytes": b - a,
                "command_sha256": sha_bytes(data[a:b]),
            })
        write_json(stage / "ast-byte-ledger.json", {
            "source": report["source"], "source_sha256": report["source_sha256"],
            "facts": report["facts"], "facts_sha256": report["facts_sha256"],
            "whole_command_units": ast_rows,
        })
        subtraction = [edit for edit in report["edits"]
                       if edit["reason"] == "subtract unselected declaration command"]
        write_json(stage / "subtraction-ledger.json", {
            "source_module": module, "edits": subtraction,
            "removed_commands": len(subtraction), "theorem_stubs_inserted": 0,
            "proof_commands_retained_whole": True,
        })
        original_imports = self.imports["modules"][module]["imports"]
        write_json(stage / "import-ledger.json", {
            "source_module": module,
            "parser_reported_original_imports": original_imports,
            "definition_bundle_dependencies": bundle["imports"],
            "rewritten_imports": report["imports"],
            "project_import_closure_provenance": report["import_provenance"],
            "rewrite_edits": [edit for edit in report["edits"]
                              if edit["reason"] in {"rewrite parser import command", "insert generated imports"}],
        })

    def snapshot_requests(self, module, generated):
        bundle = self.artifact_plan["definition_bundles"][module]
        requests = []
        expected_module = self.platform_module(module) if generated else module
        for key in bundle["units"]:
            unit = self.units[key]
            for name in unit["graph_names"]:
                row = self.graph_rows[name]
                source_private = bool(row["isPrivate"])
                generated_private = bool(source_private and not unit["deprivate"])
                is_private = generated_private if generated else source_private
                public_name = self.source_platform_name(name, unit) if generated else name
                requests.append({
                    "source_graph_name": name,
                    "expected_user_name": row["userName"] if not generated or generated_private else public_name,
                    "expected_public_name": "" if is_private else public_name,
                    "expected_module": expected_module,
                    "expected_kind": row["kind"],
                    "source_was_private": is_private,
                    "command_unit": key,
                    "decl_graph_sha256": self.graph_sha,
                    "decl_graph_row_sha256": self.graph_row_hashes[name],
                })
        return requests

    def write_snapshots(self, module, batch, report, target):
        snapshot_core = VERIFICATION / "TypeOnlyTheoremSnapshotCore.inc"
        snapshot_lineage = VERIFICATION / "TypeOnlyTheoremSnapshotCore.lineage.json"
        core = snapshot_core.read_text(encoding="utf-8")
        stage = target.parent.parent / "snapshots" / target.stem
        stage.mkdir(parents=True, exist_ok=True)
        original_jsonl = stage / "original.jsonl"
        generated_jsonl = stage / "generated.jsonl"
        original_requests = self.snapshot_requests(module, generated=False)
        generated_requests = self.snapshot_requests(module, generated=True)
        if [row["source_graph_name"] for row in original_requests] != [row["source_graph_name"] for row in generated_requests]:
            raise ValueError("Original/generated snapshot request domains differ: " + module)
        original_lean = stage / "SnapshotOriginal.lean"
        generated_lean = stage / "SnapshotGenerated.lean"
        original_lean.write_text(render_snapshot(core, module, original_requests, original_jsonl), encoding="utf-8")
        generated_lean.write_text(render_snapshot(core, report["platform_module"], generated_requests, generated_jsonl), encoding="utf-8")
        request_path = stage / "snapshot-requests.json"
        write_json(request_path, {"original": original_requests, "generated": generated_requests})
        graph_kinds = CounterLike(row["expected_kind"] for row in original_requests)
        comparison = {
            "source_module": module,
            "generated_module": report["platform_module"],
            "source_graph_names": [row["source_graph_name"] for row in original_requests],
            "kind_counts": graph_kinds,
            "comparison_policy": {
                "theorem": ["levelParams", "type", "axioms", "envKind"],
                "def": ["levelParams", "type", "value", "axioms", "envKind"],
                "inductive_ctor_rec": ["levelParams", "type", "axioms", "envKind", "kindMetadata"],
                "theorem_value_must_be_null": True,
                "ordinary_definition_value_must_be_present": True,
                "private_name_matching": "unique privateToUserName? plus exact module owner",
            },
            "snapshot_core": task_relative(snapshot_core),
            "snapshot_core_sha256": sha(snapshot_core),
            "snapshot_core_lineage": task_relative(snapshot_lineage),
            "snapshot_core_lineage_sha256": sha(snapshot_lineage),
            "provider_exporter_sha256": sha_bytes(PROVIDER_EXPORTER.encode("utf-8")),
            "original_exporter": workspace_relative(original_lean),
            "original_exporter_sha256": sha(original_lean),
            "generated_exporter": workspace_relative(generated_lean),
            "generated_exporter_sha256": sha(generated_lean),
            "generated_bundle": workspace_relative(target),
            "generated_bundle_sha256": sha(target),
            "expected_original_jsonl": workspace_relative(original_jsonl),
            "expected_generated_jsonl": workspace_relative(generated_jsonl),
            "lean_started": False,
            "validated": False,
        }
        write_json(stage / "snapshot-comparison-plan.json", comparison)


def CounterLike(values):
    result = defaultdict(int)
    for value in values:
        result[value] += 1
    return dict(sorted(result.items()))


def certified_dependencies(generator: ProviderGenerator):
    reuse = []
    for item in generator.reuse:
        reuse.append({
            "source_module": item["source_module"],
            "platform_module": item["existing_module"],
            "provided_constants": item["provided_constants"],
            "provided_constant_count": len(item["provided_constants"]),
            "validated": item["validated"],
            "kernel_validated": item["kernel_validated"],
            "source_sha256": item["source_sha256"],
            "existing_sha256": item["existing_sha256"],
            "ast_validation_sha256": item["ast_validation_sha256"],
        })
    published = []
    for source_module, item in PUBLISHED.items():
        validation = TASK / item["validation"]
        publication = validation.parent / "publication.json"
        publication_doc = read_json(publication)
        if publication_doc["definition_id"] != item["definition_id"]:
            raise ValueError("Published provider identity changed: " + source_module)
        published.append({
            "source_module": source_module,
            "platform_module": item["platform_module"],
            "definition_id": publication_doc["definition_id"],
            "validation": item["validation"],
            "validation_sha256": sha(validation),
            "publication": workspace_relative(publication),
            "publication_sha256": sha(publication),
            "validated": read_json(validation).get("validated") is True,
            "published": bool(publication_doc.get("definition_id") and publication_doc.get("target_readback")),
        })
    return {"canonical_reuse": reuse, "published_provider_bundles": published}


def private_risk_report(generator: ProviderGenerator):
    base_units = {unit["id"]: unit for unit in generator.base_unit_plan["units"]}
    incoming = defaultdict(list)
    for key, unit in generator.units.items():
        for dep in unit["direct_unit_dependencies"]:
            incoming[dep].append(key)
    rows = []
    for key in sorted(generator.new_private_units):
        unit = generator.units[key]
        names = unit["graph_names"]
        stage_key = module_path(unit["module"])
        entry = generator.state["stage2"][stage_key]
        facts_path = ROOT / entry["facts"]
        facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        binding_ids = []
        if unit["nameRange"]:
            binding_ids = sorted({fact["const"] for fact in facts if fact["kind"] == "ref"
                                  and fact["start"] == unit["nameRange"]["start"]
                                  and fact["end"] == unit["nameRange"]["end"]})
        consumers = sorted(incoming[key])
        cross = [consumer for consumer in consumers
                 if generator.units[consumer]["module"] != unit["module"]]
        override = generator.overrides_by_unit.get(key)
        rows.append({
            "unit": key, "source_module": unit["module"], "graph_names": names,
            "user_names": [generator.graph_rows[name]["userName"] for name in names],
            "category_before": base_units[key]["category"], "category_after": unit["category"],
            "deprivate": unit["deprivate"],
            "deprivate_override": override,
            "incoming_definition_units": consumers,
            "cross_module_incoming_units": cross,
            "same_source_module_only": not cross,
            "direct_public_type_consumers": sorted(row["name"] for row in generator.graph_rows.values()
                                                   if not row["isPrivate"]
                                                   and any(name in row["typeDeps"] for name in names)),
            "source_binding_oracle_identities": binding_ids,
            "binding_identity_unique": len(binding_ids) == 1,
            "source_sha256": unit["source_sha256"],
            "facts": entry["facts"], "facts_sha256": entry["facts_sha256"],
            "actual_generated_private_ci": {
                "resolver": "Lean.privateToUserName? plus exact generated module owner",
                "kernel_numeric_name_guessed": False,
                "validated": False,
            },
        })
    return rows


def module_path(module):
    return module.replace(".", "/") + ".lean"


def choose_batches(generator: ProviderGenerator):
    units = generator.units
    minimum_units = {generator.owner[name] for name in MINIMUM_PROVIDER_NAMES}
    minimum_modules = sorted({units[key]["module"] for key in minimum_units})
    shared_root_modules = {units[key]["module"] for key in generator.provider_roots}
    certified = {item["source_module"] for item in generator.reuse} | set(PUBLISHED)
    safe_leaves, rejected = [], []
    for module in sorted(shared_root_modules):
        if module in certified:
            continue
        imports = generator.artifact_plan["definition_bundles"][module]["imports"]
        uncertified = sorted(set(imports) - certified)
        risks = generator.module_name_risk(module)
        import_facts_pending = generator.imports["transitive_external_imports"][module]["unextracted_project_modules"]
        if not uncertified and not risks and not import_facts_pending:
            safe_leaves.append(module)
        else:
            rejected.append({"source_module": module, "uncertified_definition_imports": uncertified,
                             "name_or_private_risks": risks,
                             "unextracted_project_import_facts": import_facts_pending})
    return minimum_modules, safe_leaves, rejected


def dependency_plan(generator: ProviderGenerator, minimum_modules, certificates):
    closure = module_closure(minimum_modules, generator.artifact_plan)
    certified = ({item["source_module"] for item in certificates["canonical_reuse"]}
                 | {item["source_module"] for item in certificates["published_provider_bundles"]})
    order = [module for module in generator.artifact_plan["definition_order"] if module in closure]
    pending = [module for module in order if module not in certified]
    return {
        "minimum_provider_modules": minimum_modules,
        "definition_module_closure_count": len(closure),
        "definition_module_closure": sorted(closure),
        "leaves_first_order": order,
        "certified_modules": sorted(closure & certified),
        "pending_generated_modules": pending,
        "pending_generated_module_count": len(pending),
        "certification_strategy": {
            "reused_statement_constants": sum(item["provided_constant_count"]
                                               for item in certificates["canonical_reuse"]),
            "published_definition_bundles": len(certificates["published_provider_bundles"]),
            "remaining_rule": "generate leaves-first, compile each bundle <=300s, compare theorem types and ordinary-def values, then audit Std3",
        },
        "preview_only": True,
        "lean_started": False,
    }


def generic_validator_ordinary_public(generator: ProviderGenerator, module: str):
    """Static interface subset accepted by the generic provider validator."""
    reasons = []
    for key in generator.artifact_plan["definition_bundles"][module]["units"]:
        unit = generator.units[key]
        if unit["private"] or unit["deprivate"] or unit["is_instance_command"] or unit["is_local_instance"]:
            reasons.append({"unit": key, "reason": "private/deprivate/instance command"})
        if len(unit["graph_names"]) != 1:
            reasons.append({"unit": key, "reason": "multi-declaration command"})
        if unit["graph_kinds"] not in (["theorem"], ["def"]):
            reasons.append({"unit": key, "reason": "non theorem/def environment kind"})
    return reasons


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true")
    parser.add_argument("--batch", choices=("minimum", "safe-leaves", "both"), default="both")
    parser.add_argument("--limit", type=int, help="positive preview-only cap within each selected batch")
    parser.add_argument("--selection-only", action="store_true",
                        help="write dependency/risk/selection ledgers without staging bundle source")
    args = parser.parse_args()
    if not args.preview:
        raise SystemExit("Only isolated --preview generation is implemented; final guards are not bypassed")
    if args.limit is not None and args.limit <= 0:
        parser.error("--limit must be positive")
    generator = ProviderGenerator()
    certificates = certified_dependencies(generator)
    write_json(OUTPUT / "dependency-certificates.json", certificates)
    private_rows = private_risk_report(generator)
    write_json(OUTPUT / "new-private-helper-risk.json", {
        "count": len(private_rows), "helpers": private_rows,
        "all_actual_private_names_require_runtime_unique_resolution": True,
        "numeric_private_names_may_be_guessed": False,
        "lean_started": False,
    })
    minimum, safe_leaves, safe_rejected = choose_batches(generator)
    write_json(OUTPUT / "minimum-dependency-plan.json",
               dependency_plan(generator, minimum, certificates))
    write_json(OUTPUT / "safe-leaf-selection.json", {
        "selected": safe_leaves, "selected_count": len(safe_leaves),
        "rejected": safe_rejected,
        "selection_rule": "shared-provider root module whose Definition imports are already certified and whose selected commands have no unresolved AST owner, retained project-open boundary, deprivate/name, or private-CI requirement",
        "capture_observations": generator.capture_observations,
        "preview_only": True,
    })
    if args.selection_only:
        summary = {
            "provider_variant": "all-shared-public",
            "output_root": task_relative(OUTPUT),
            "minimum_modules": minimum,
            "safe_leaf_modules": safe_leaves,
            "safe_leaf_count": len(safe_leaves),
            "rejected_count": len(safe_rejected),
            "bundles_staged": 0,
            "complete_ast_owner_guard": True,
            "retained_open_namespace_guard": True,
            "preview_only": True,
            "lean_started": False,
            "api_used": False,
        }
        write_json(OUTPUT / "selection-summary.json", summary)
        print(json.dumps(summary, ensure_ascii=False))
        return
    batches = []
    if args.batch in {"minimum", "both"}:
        batches.append(("minimum-statement", minimum))
    if args.batch in {"safe-leaves", "both"}:
        batches.append(("all-shared-safe-leaves", safe_leaves))
    all_reports, all_rejected = {}, {}
    for label, modules in batches:
        if args.limit:
            modules = modules[:args.limit]
        reports, rejected = [], []
        for module in modules:
            try:
                reports.append(generator.stage_bundle(module, label))
            except (ValueError, KeyError, StopIteration) as error:
                rejected.append({"source_module": module, "reason": str(error) or type(error).__name__})
        all_reports[label] = reports
        all_rejected[label] = rejected
        write_json(OUTPUT / label / "generation-report.json", {
            "batch": label, "generated": reports, "rejected": rejected,
            "preview_only": True, "lean_started": False, "api_used": False,
            "input_hashes": dict(sorted(generator.input_hashes.items())),
            "capture_observations": generator.capture_observations,
        })
    safe_reports = all_reports.get("all-shared-safe-leaves", [])
    interface_rejected = []
    compatible_reports = []
    for item in safe_reports:
        reasons = generic_validator_ordinary_public(generator, item["source_module"])
        if reasons:
            interface_rejected.append({"source_module": item["source_module"], "reasons": reasons})
        else:
            compatible_reports.append(item)
    ranked = sorted(compatible_reports, key=lambda item: ((ROOT / item["output"]).stat().st_size,
                                                           len(item["imports"]), item["source_module"]))
    next_batch = []
    for item in ranked[:10]:
        source = (ROOT / item["output"]).relative_to(VERIFICATION).as_posix()
        next_batch.append({
            "source_module": item["source_module"],
            "platform_module": item["platform_module"],
            "source": source,
            "source_sha256": item["output_sha256"],
            "source_bytes": (ROOT / item["output"]).stat().st_size,
            "selected_units": len(item["selected_units"]),
            "definition_bundle_dependencies": generator.artifact_plan["definition_bundles"][item["source_module"]]["imports"],
            "preflight_command": (
                "python scripts/preflight_staged_module.py " + source
                + " --root " + (OUTPUT / "all-shared-safe-leaves").relative_to(VERIFICATION).as_posix()
                + " --timeout-seconds 300 --emit-olean"
            ),
            "snapshot_plan": (
                task_relative(OUTPUT / "all-shared-safe-leaves" / "snapshots") + "/"
                + Path(item["output"]).stem + "/snapshot-comparison-plan.json"
            ),
        })
    write_json(OUTPUT / "next-preflight-batch.json", {
        "selection": "ten smallest generated all-shared provider leaves with zero Definition-bundle dependencies and only ordinary public one-name theorem/def commands",
        "candidates": next_batch,
        "generic_validator_interface_rejected": interface_rejected,
        "all_candidates_have_zero_definition_bundle_dependencies": all(not item["definition_bundle_dependencies"]
                                                                        for item in next_batch),
        "timeout_seconds_each": 300,
        "lean_started": False,
    })
    summary = {
        "provider_variant": "all-shared-public",
        "minimum_provider_names": sorted(MINIMUM_PROVIDER_NAMES),
        "minimum_modules": minimum,
        "safe_leaf_modules": safe_leaves,
        "generated_by_batch": {key: len(value) for key, value in all_reports.items()},
        "rejected_by_batch": {key: value for key, value in all_rejected.items()},
        "new_private_helpers": len(private_rows),
        "fresh_base_and_provider_plan_equality": True,
        "accepted_outputs_untouched": True,
        "capture_observations": generator.capture_observations,
        "preview_only": True,
        "lean_started": False,
        "api_used": False,
    }
    write_json(OUTPUT / "generation-summary.json", summary)
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()

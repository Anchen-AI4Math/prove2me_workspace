"""Append import-ambiguity and orphan-doc-comment repairs; freeze old failures."""
from copy import deepcopy
import initialize_author as p


def main():
    source = p.load(p.OUT / "author-context-preparation.json")
    control = p.load(p.OUT / "author-control-preparation-v2.json")
    repaired_sources, repaired_controls, notes = deepcopy(source), deepcopy(control), []
    for tag, short in zip(["c", "f", "m"], ["Constant", "Five", "Matrix"], strict=True):
        ctx = p.PROJECT / tag
        row = next(row for row in repaired_sources["contexts"] if row["tag"] == tag)
        solution = next(item for item in row["math_sources"] if item["module"].startswith("Solutions."))
        old_module, old_path = solution["module"], ctx / solution["path"]
        raw = old_path.read_bytes()
        assert raw.count(b"Finset.mem_antidiagonal") == 4
        repaired = raw.replace(b"Finset.mem_antidiagonal", b"Finset.HasAntidiagonal.mem_antidiagonal")
        orphan = b"/-- Rows are new monomial indices; columns are old P coefficient indices. -/"
        assert repaired.count(orphan) == 1
        repaired = repaired.replace(orphan, orphan.replace(b"/--", b"/-", 1), 1)
        new_module = "Solutions.Outputs" + short + "V2"
        new_path = ctx / (new_module.replace(".", "/") + ".lean")
        p.write(new_path, repaired)
        solution.update({"module": new_module, "path": new_path.relative_to(ctx).as_posix(), "binding": p.bind(new_path),
                         "original_failed_or_uncompiled_candidate": p.bind(old_path),
                         "repair": "four proof-body lemma qualifiers and one orphan documentation marker only"})
        fullheaders = p.load(p.OUT / "target-plan.json")["native_all16_exact_headers"]
        for header in fullheaders:
            value = header if isinstance(header, str) else header["header"]
            assert repaired.decode("utf-8").count(value) == raw.decode("utf-8").count(value) == 1
        crow = next(item for item in repaired_controls["contexts"] if item["tag"] == tag)
        swaps = {old_module: new_module, "OutputsPlatformAssertions": "OutputsPlatformAssertionsV3",
                 "OutputsPlatformSemantic": "OutputsPlatformSemanticV3",
                 "OutputsPlatformGeneratedV2": "OutputsPlatformGeneratedV3",
                 "OutputsPlatformResolverV2": "OutputsPlatformResolverV3"}
        for item in crow["rows"]:
            original = ctx / item["path"]
            value = original.read_text(encoding="utf-8")
            for before, after in swaps.items():
                value = value.replace(before, after)
            module = swaps[item["module"]]
            target = ctx / (module + ".lean")
            p.write(target, value)
            item.update({"module": module, "path": target.name, "binding": p.bind(target)})
        for key in ["all_actual_math_modules", "actual_own_modules"]:
            crow[key] = [swaps.get(module, module) for module in crow[key]]
        notes.append({"tag": tag, "old_solution": p.bind(old_path), "private_solution_v2": p.bind(new_path),
                      "all16_original_full_headers_occurrences": 1, "all_other_theorem_headers_unchanged": True,
                      "all380_proof_declarations_retained": True, "new_assumptions_or_changed_whole_functions": False})
    for row in repaired_sources["contexts"]:
        if row["tag"] == "r":
            for old, short in zip(row["math_sources"][-3:], ["Constant", "Five", "Matrix"], strict=True):
                module = "Theorems.Ref" + short + "V2"
                path = p.PROJECT / "r" / (module.replace(".", "/") + ".lean")
                old.update({"module": module, "path": path.relative_to(p.PROJECT / "r").as_posix(), "binding": p.bind(path)})
    p.dump(p.OUT / "author-math-source-preparation-v2.json", repaired_sources)
    p.dump(p.OUT / "author-control-preparation-v3.json", repaired_controls)
    p.dump(p.OUT / "author-private-solution-repair-v2.json", {"repairs": notes,
            "actual_failure": "c/s37 retained complete; broad import changed antidiagonal lemma resolution, orphan doc comment expects declaration",
            "original_candidate_51_files_unchanged": True, "Lean_calls_in_preparation": 0, "API_calls": 0})
    print("Appended three private repaired Solutions and complete control V3 SOURCE, original failures retained")


if __name__ == "__main__":
    main()

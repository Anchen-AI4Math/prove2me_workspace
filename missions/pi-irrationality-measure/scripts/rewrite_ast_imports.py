"""Plan import replacements at parser-reported ranges in immutable source bytes."""
from span_edits import Edit


def import_edits(imports, replacement_modules):
    """Replace all original import commands by a deterministic supplied union.

    The caller computes transitive external imports from the AST import graph,
    plus the generated Definitions/Theorems modules needed by its selection.
    Returning edits instead of already-mutated text lets declaration subtraction,
    binding renames and import changes share one checked right-to-left pass.
    """
    names = sorted(set(replacement_modules))
    for name in names:
        if not name or any(not part.isidentifier() for part in name.split(".")):
            raise ValueError(f"Import module is not a dotted identifier: {name!r}")
    block = "\n".join("import " + name for name in names).encode("utf-8")
    original = sorted(imports, key=lambda item: item["command_range"]["start"]["offset"])
    if not original:
        return [Edit(0, 0, block + b"\n", "insert generated imports")] if block else []
    edits = []
    for index, item in enumerate(original):
        span = item["command_range"]
        edits.append(Edit(span["start"]["offset"], span["end"]["offset"],
                          block if index == 0 else b"", "rewrite parser import command"))
    return edits


def external_import_union(module, import_inventory):
    """Refuse incomplete transitive closure rather than lose Mathlib imports."""
    closure = import_inventory["transitive_external_imports"][module]
    if closure["unextracted_project_modules"]:
        raise ValueError(f"Transitive project import facts are pending for {module}")
    return closure["external_imports"]

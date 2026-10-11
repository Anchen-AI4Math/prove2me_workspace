"""Plan a same-namespace constant rename using its binding reference as identity."""
from span_edits import from_range


def rename_bound_constant(unit, facts, verified_source_name, public_name):
    """Return edits; callers filter retained spans and apply them together.

    Private IDs printed by the sketch oracle may omit the original module.
    Never join them across files by spelling. An exact binding range within
    this source selects its oracle constant, which then selects its references.
    This covers emitted facts; recursive and macro-produced references still
    require the mandatory re-elaboration/type validation.
    """
    if not unit["nameRange"]:
        raise ValueError("A binding rename requires an authoritative name range")
    before_namespace, _, _ = verified_source_name.rpartition(".")
    after_namespace, _, leaf = public_name.rpartition(".")
    if before_namespace != after_namespace:
        raise ValueError("Namespace-changing renames need a separate scope transformation")
    if not public_name.isascii() or any(not part.isidentifier() for part in public_name.split(".")):
        raise ValueError("Proposed public name must be a conservative dotted ASCII identifier")
    binding = unit["nameRange"]
    binding_refs = [fact for fact in facts if fact["kind"] == "ref"
                    and fact["start"]["offset"] == binding["start"]["offset"]
                    and fact["end"]["offset"] == binding["end"]["offset"]]
    constants = {fact["const"] for fact in binding_refs}
    if len(constants) != 1:
        raise ValueError("The binding must resolve to exactly one emitted constant identity")
    constant = next(iter(constants))
    edits = [from_range(binding, leaf, "rename original declaration binding")]
    seen = {(binding["start"]["offset"], binding["end"]["offset"])}
    for fact in facts:
        if fact["kind"] != "ref" or fact["const"] != constant:
            continue
        key = (fact["start"]["offset"], fact["end"]["offset"])
        if key in seen:
            continue
        seen.add(key)
        edits.append(from_range({"start": fact["start"], "end": fact["end"]}, public_name,
                                "rename emitted constant reference"))
    if unit["privateTok"]:
        edits.append(from_range(unit["privateTok"], "", "make required definition public"))
    return edits, constant

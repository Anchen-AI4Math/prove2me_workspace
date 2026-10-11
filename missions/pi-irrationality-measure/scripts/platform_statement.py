"""Build one platform statement fragment at authoritative source byte ranges.

The caller assembles its preamble and validates the exact concatenation in Lean.
This function does not infer scopes, rename dependencies, or certify type equality.
"""
import hashlib
from span_edits import Edit, apply_edits, from_range


def declaration_fragment(data, unit, wrapper_info, theorem_name, source_sha256, *, stub):
    if hashlib.sha256(data).hexdigest() != source_sha256:
        raise ValueError("Statement source differs from the validated oracle input")
    if (not theorem_name.isascii() or
            any(not part.isidentifier() for part in theorem_name.split("."))):
        raise ValueError("Platform theorem name must be a conservative dotted ASCII identifier")
    if unit["graph_kinds"] != ["theorem"] or unit["is_instance_command"]:
        raise ValueError("A platform theorem fragment must come from a theorem command")
    if not unit["nameRange"] or unit["valueStart"] is None:
        raise ValueError("A theorem requires authoritative binding and value ranges")
    if (unit["start"] != wrapper_info["range"]["start"] or
            unit["end"] != wrapper_info["range"]["end"] or
            unit["nameRange"] != wrapper_info["nameRange"]):
        raise ValueError("Wrapper and declaration facts belong to different commands")

    edits = []
    hoisted = []
    removed_ranges = []
    for wrapper in wrapper_info["wrappers"]:
        kind = wrapper["syntaxKind"]
        if kind not in ("Lean.Parser.Command.include", "Lean.Parser.Command.omit", "Lean.Parser.Command.open"):
            raise ValueError(f"Scoped wrapper needs an explicit transformation: {kind}")
        command = wrapper["command_range"]
        text = data[command["start"]["offset"]:command["end"]["offset"]].decode("utf-8")
        hoisted.append({"syntaxKind": kind, "text": text, "source_range": command})
        span = wrapper["prefix_range"]
        removed_ranges.append((span["start"]["offset"], span["end"]["offset"]))
        edits.append(from_range(span, "", "hoist scoped include/omit to preamble"))

    # A docstring can belong to an outer wrapper's deleted prefix. Do not create
    # a second overlapping edit; every other modifier is removed at its own span.
    for field in ("docstring", "privateTok"):
        span = unit[field]
        if span is None:
            continue
        start, end = span["start"]["offset"], span["end"]["offset"]
        if any(left <= start <= end <= right for left, right in removed_ranges):
            continue
        edits.append(from_range(span, "", "strip platform " + field))
    keywords = wrapper_info["theorem_keyword_tokens"]
    if len(keywords) != 1:
        raise ValueError("Expected one AST theorem/lemma keyword")
    if keywords[0]["keyword"] == "lemma":
        edits.append(from_range(keywords[0]["range"], "theorem", "platform theorem keyword"))
    edits.append(from_range(unit["nameRange"], theorem_name, "fully qualified platform binding"))
    if stub:
        edits.append(Edit(unit["valueStart"]["offset"], unit["end"]["offset"],
                          b":= by sorry", "platform statement placeholder"))

    start, end = unit["start"]["offset"], unit["end"]["offset"]
    if any(not start <= edit.start <= edit.end <= end for edit in edits):
        raise ValueError("A statement edit escapes its source command")
    fragment = data[start:end]
    local_edits = [Edit(edit.start - start, edit.end - start, edit.replacement, edit.reason)
                   for edit in edits]
    result = apply_edits(fragment, local_edits, hashlib.sha256(fragment).hexdigest())
    ledger = [{"start": edit.start, "end": edit.end, "reason": edit.reason,
               "replacement_bytes": len(edit.replacement)} for edit in edits]
    return result, hoisted, ledger


def statement_fragment(data, unit, wrapper_info, theorem_name, source_sha256):
    return declaration_fragment(data, unit, wrapper_info, theorem_name, source_sha256, stub=True)


def solution_fragment(data, unit, wrapper_info, source_sha256):
    return declaration_fragment(data, unit, wrapper_info, "solution", source_sha256, stub=False)

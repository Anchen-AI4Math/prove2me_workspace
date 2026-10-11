"""Rename an anonymous private local instance from same-file oracle facts.

The oracle's source range for an anonymous instance binding is the `instance`
keyword itself. This module inserts an explicit leaf name at that range's end,
removes only the parser-recorded `private` token, and rewrites references only
within the facts supplied for the same source module. It never joins private
names across modules by their printed spelling.
"""
from __future__ import annotations

from span_edits import Edit


def _offset_range(item: dict) -> tuple[int, int]:
    try:
        start = item["start"]["offset"]
        end = item["end"]["offset"]
    except (KeyError, TypeError) as exc:
        raise ValueError("An oracle reference lacks an authoritative byte range") from exc
    if not isinstance(start, int) or not isinstance(end, int) or start >= end:
        raise ValueError("An oracle reference has an invalid or empty byte range")
    return start, end


def _inside(unit: dict, fact: dict) -> bool:
    try:
        start, end = _offset_range(fact)
        return unit["start"]["offset"] <= start and end <= unit["end"]["offset"]
    except (KeyError, TypeError, ValueError):
        return False


def _safe_name(name: str) -> tuple[str, str]:
    if not isinstance(name, str) or not name.isascii():
        raise ValueError("The stable public name must be an ASCII dotted identifier")
    parts = name.split(".")
    if len(parts) < 2 or any(not part.isidentifier() for part in parts):
        raise ValueError("The stable public name must be a fully qualified dotted identifier")
    return ".".join(parts[:-1]), parts[-1]


def rename_anonymous_instance(
    unit: dict,
    facts: list[dict],
    graph_row: dict,
    source_module: str,
    source_bytes: bytes,
    public_name: str,
    wrapper: dict,
) -> tuple[list[Edit], str, dict]:
    """Return byte edits, the oracle identity, and an auditable rename record.

    `facts` must contain only Stage2 facts for `source_module`. `graph_row` is
    the unique declaration-graph row owning this AST unit. `wrapper` is its
    Parser wrapper-inventory declaration; unsupported wrappers/macros are
    rejected because this edit cannot prove their generated names are visible.
    """
    if not source_module or graph_row.get("module") != source_module:
        raise ValueError("The graph row and same-file Stage2 facts must name one module")
    if not isinstance(source_bytes, bytes):
        raise ValueError("The exact source bytes are required to validate Parser ranges")
    source_bytes.decode("utf-8")
    if not unit.get("is_instance_command") or not unit.get("is_local_instance"):
        raise ValueError("Only a Parser-recognized local instance command is supported")
    if unit.get("nameRange") is not None or unit.get("nameText") is not None:
        raise ValueError("This path is only for an anonymous instance with no name range")
    names = unit.get("graph_names")
    if not isinstance(names, list) or len(names) != 1 or names[0] != graph_row.get("name"):
        raise ValueError("The AST unit must own exactly the matching graph declaration")
    if graph_row.get("kind") != "theorem" or not graph_row.get("isPrivate"):
        raise ValueError("The graph declaration must be the private generated instance theorem")
    if not unit.get("privateTok"):
        raise ValueError("The parser did not provide a private-token range to remove")
    local_ranges = unit.get("local_modifier_ranges")
    if not isinstance(local_ranges, list) or len(local_ranges) != 1:
        raise ValueError("Only the recognized single-local-modifier form is supported")
    if not isinstance(wrapper, dict) or wrapper.get("wrappers") != []:
        raise ValueError("Wrapped or macro-generated declarations require a separate binding audit")
    if wrapper.get("inner_syntaxKind") != "Lean.Parser.Command.declaration":
        raise ValueError("The declaration is not the recognized Parser declaration syntax")
    if wrapper.get("nameRange") is not None:
        raise ValueError("The wrapper inventory disagrees that this binding is anonymous")

    source_name = graph_row.get("userName")
    if not isinstance(source_name, str) or not source_name.isascii():
        raise ValueError("The graph row lacks a safe verified source name")
    source_namespace, source_leaf = source_name.rpartition(".")[::2]
    public_namespace, public_leaf = _safe_name(public_name)
    if not source_namespace or source_namespace != public_namespace:
        raise ValueError("Anonymous-instance renames must keep the verified namespace")
    if not source_leaf or not source_leaf.isidentifier():
        raise ValueError("The verified source leaf is not a conservative identifier")

    start_line = unit.get("start", {}).get("line")
    value_start = unit.get("valueStart")
    if not isinstance(start_line, int) or not isinstance(value_start, dict):
        raise ValueError("The parser did not provide the declaration header boundary")
    header_end = value_start.get("offset")
    if not isinstance(header_end, int):
        raise ValueError("The parser did not provide a valid declaration value boundary")

    # Resolve the binding solely from the oracle's same-file constant identity
    # and its source range in this command header. For this syntax, that exact
    # range is the `instance` keyword; no source-text search chooses the offset.
    binding_facts = []
    for fact in facts:
        if fact.get("kind") != "ref" or not _inside(unit, fact):
            continue
        constant = fact.get("const")
        if not isinstance(constant, str) or not constant.startswith("_private."):
            continue
        if not constant.endswith("." + source_name):
            continue
        try:
            start, end = _offset_range(fact)
        except ValueError:
            continue
        if (fact.get("start", {}).get("line") == start_line
                and fact.get("end", {}).get("line") == start_line
                and end <= header_end):
            binding_facts.append(fact)
    if len(binding_facts) != 1:
        raise ValueError("Expected exactly one visible oracle binding reference in the command header")
    binding = binding_facts[0]
    identity = binding["const"]
    binding_start, binding_end = _offset_range(binding)
    if source_bytes[binding_start:binding_end] != b"instance":
        raise ValueError("The oracle binding range does not cover the instance keyword")
    private_start = unit["privateTok"]["start"]["offset"]
    private_end = unit["privateTok"]["end"]["offset"]
    if source_bytes[private_start:private_end] != b"private":
        raise ValueError("The parser private-token range does not cover the private modifier")
    for modifier in local_ranges:
        start, end = _offset_range(modifier)
        if source_bytes[start:end] != b"local":
            raise ValueError("The recognized local-instance modifier range is not local")

    identity_facts = [fact for fact in facts
                      if fact.get("kind") == "ref" and fact.get("const") == identity]
    if not identity_facts:
        raise ValueError("No same-file oracle references were found for the binding identity")
    for fact in identity_facts:
        _offset_range(fact)  # Reject macro/synthetic references without source positions.

    binding_key = (binding_start, binding_end)
    refs = []
    edits = [
        Edit(binding_end, binding_end, (" " + public_leaf).encode("ascii"),
             "insert an explicit name after the Parser-located instance keyword"),
        Edit(unit["privateTok"]["start"]["offset"], unit["privateTok"]["end"]["offset"], b"",
             "remove only the Parser-located private modifier"),
    ]
    seen_spans = {binding_key}
    for fact in identity_facts:
        start, end = _offset_range(fact)
        if (start, end) == binding_key:
            refs.append({"start": start, "end": end, "role": "anonymous_binding"})
            continue
        if (start, end) in seen_spans:
            raise ValueError("Multiple oracle references share an ambiguous source range")
        seen_spans.add((start, end))
        refs.append({"start": start, "end": end, "role": "reference"})
        edits.append(Edit(start, end, public_name.encode("ascii"),
                          "rewrite same-file reference by exact oracle constant identity"))

    record = {
        "source_module": source_module,
        "graph_name": graph_row["name"],
        "source_name": source_name,
        "public_name": public_name,
        "oracle_identity": identity,
        "binding_reference_range": {"start": binding_start, "end": binding_end},
        "insertion_offset": binding_end,
        "reference_ranges": refs,
        "edits": [
            {"start": edit.start, "end": edit.end,
             "replacement": edit.replacement.decode("utf-8"), "reason": edit.reason}
            for edit in sorted(edits, key=lambda item: (item.start, item.end))
        ],
        "preserved_modifiers": ["local"],
        "removed_modifiers": ["private"],
        "cross_file_private_name_matching": False,
        "lean_or_type_validated": False,
    }
    return edits, identity, record

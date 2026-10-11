"""Subtract complete declaration commands, preserving every surrounding byte.

Callers supply validated AST units. This module does not discover declarations,
expand ranges, or infer source scopes. Import/rename transformations are separate
AST edits and may be composed after the selection has been planned.
"""
from span_edits import Edit, apply_edits


def declaration_edits(declaration_units, selected_offsets, *, stub_offsets=()):
    """Plan edits against the original bytes, for one combined application.

    Units are the Stage 2 whole commands, including mutual blocks and wrappers.
    ``stub_offsets`` applies only to selected theorem commands and replaces the
    oracle's value suffix; Definitions callers must always leave it empty.
    """
    by_start = {}
    for unit in declaration_units:
        start = unit["start"]["offset"]
        if start in by_start:
            raise ValueError("Duplicate source command in subtraction inventory")
        by_start[start] = unit
    selected = set(selected_offsets)
    stubs = set(stub_offsets)
    if not selected <= by_start.keys():
        raise ValueError("Selection contains a command absent from the AST inventory")
    if not stubs <= selected:
        raise ValueError("Only retained commands can become theorem stubs")
    edits = []
    for start, unit in by_start.items():
        end = unit["end"]["offset"]
        if start not in selected:
            edits.append(Edit(start, end, b"", "subtract unselected declaration command"))
        elif start in stubs:
            if (unit["graph_kinds"] != ["theorem"] or unit["is_instance_command"]
                    or unit["valueStart"] is None):
                raise ValueError("Only theorem commands with oracle value ranges can be stubbed")
            value_start = unit["valueStart"]["offset"]
            if not start <= value_start < end:
                raise ValueError("The oracle proof range escapes its declaration command")
            edits.append(Edit(value_start, end, b":= by sorry", "replace theorem value by platform stub"))
    return edits


def subtract_declarations(data, declaration_units, selected_offsets, source_sha256,
                          *, stub_offsets=()):
    """Apply declaration edits alone; imports/renames can use declaration_edits."""
    edits = declaration_edits(declaration_units, selected_offsets, stub_offsets=stub_offsets)
    result = apply_edits(data, edits, source_sha256)
    ledger = [{"start": edit.start, "end": edit.end, "reason": edit.reason,
               "replacement_bytes": len(edit.replacement)} for edit in edits]
    return result, ledger

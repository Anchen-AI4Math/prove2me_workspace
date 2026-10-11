"""Restore source scope at namespace root using parser-owned byte spans.

The result retains a literal `theorem solution` binding at module root. Sections
and noncomputable mode are restored; all active source commands remain ordered.
This is source construction only. The caller must certify generated types and
axioms with the actual Lean environment, including attribute dependencies.
"""
import hashlib

from span_edits import Edit, apply_edits

COMMAND_KINDS = {"Lean.Parser.Command." + name for name in (
    "open", "variable", "universe", "include", "omit", "set_option",
    "attribute", "notation", "infix", "infixl", "infixr", "prefix",
    "postfix", "localNotation",
)}


def namespace_prefixes(namespace):
    if not namespace:
        return []
    parts = namespace.split(".")
    if any(not part.isascii() or not part.isidentifier() for part in parts):
        raise ValueError("Source namespace needs an explicit reviewed identifier mapping")
    return [".".join(parts[:index]) for index in range(1, len(parts) + 1)]


def restore_context(data, facts, scope, source_sha256, reference_edits=(), extra_commands=()):
    """Return independent preamble/closing and a byte edit provenance ledger.

    `reference_edits` must already map authoritative constant references to the
    caller's certified providers. An extra command has its original offset and
    explicit generated text, for restoring moved local instances.
    """
    if hashlib.sha256(data).hexdigest() != source_sha256:
        raise ValueError("Source bytes changed before context restoration")
    commands = {}
    for fact in facts:
        if fact["kind"] == "command":
            start = fact["syntax"]["range"]["start"]["offset"]
            if start in commands:
                raise ValueError("An original command has ambiguous parser ownership")
            commands[start] = fact
    frames = scope["scope_stack"]
    if any(frame["kind"] not in {"namespace", "section"} for frame in frames):
        raise ValueError("Unsupported source scope frame")
    noncomputable = False
    opening_records = []
    for frame in frames:
        span = frame["opening"]
        start, end = span["start"]["offset"], span["end"]["offset"]
        fact = commands.get(start)
        expected = "Lean.Parser.Command." + frame["kind"]
        if not fact or fact["isDeclaration"] or fact["syntax"]["syntaxKind"] != expected:
            raise ValueError("Scope opening does not identify its actual source command")
        if fact["syntax"]["range"] != span:
            raise ValueError("Scope opening range differs from the parser")
        text = data[start:end].decode("utf-8")
        if frame["kind"] == "section":
            # Read the parser token, never infer mode from comments or substrings.
            stack = [fact["syntax"]]
            while stack:
                node = stack.pop()
                if node.get("atom") == "noncomputable":
                    noncomputable = True
                stack.extend(node.get("children", []))
        opening_records.append({"kind": frame["kind"], "name": frame["name"],
                                "source_range": span, "source_text": text})
    replay, ledger = {}, []
    for item in scope["context_commands"]:
        kind, span = item["syntaxKind"], item["range"]
        if kind not in COMMAND_KINDS:
            raise ValueError("Unsupported active source context: " + kind)
        a, b = span["start"]["offset"], span["end"]["offset"]
        command = commands.get(a)
        if (not command or command["isDeclaration"] or command["syntax"]["syntaxKind"] != kind
                or command["syntax"]["range"] != span):
            raise ValueError("Active context is not its parser-owned source command")
        if a in replay:
            raise ValueError("A source context command is replayed twice")
        applicable = [edit for edit in reference_edits if a <= edit.start <= edit.end <= b]
        local = [Edit(edit.start-a, edit.end-a, edit.replacement, edit.reason) for edit in applicable]
        fragment = data[a:b]
        text = apply_edits(fragment, local, hashlib.sha256(fragment).hexdigest()).decode("utf-8")
        replay[a] = text
        ledger.append({"syntaxKind": kind, "source_range": span,
                       "source_sha256": hashlib.sha256(fragment).hexdigest(),
                       "generated_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
                       "edits": [{"start": edit.start, "end": edit.end,
                                  "replacement": edit.replacement.decode("utf-8"),
                                  "reason": edit.reason} for edit in applicable]})
    for offset, text in extra_commands:
        if offset in replay or not isinstance(offset, int) or not isinstance(text, str):
            raise ValueError("Moved local instance restoration overlaps a context command")
        replay[offset] = text
    prefixes = namespace_prefixes(scope["namespace"])
    # All project references are qualified by the caller's AST edits. Namespace
    # opens also preserve source resolution for local notation and short names
    # in proof syntax. The actual elaborator validates each opened namespace.
    lines = ["noncomputable section" if noncomputable else "section"]
    if prefixes:
        lines.append("open " + " ".join(prefixes))
    lines.extend(text for _, text in sorted(replay.items()))
    return {"preamble": "\n".join(lines) + "\n", "closing": "\nend\n",
            "namespace_opens": prefixes, "source_scope_frames": opening_records,
            "context_commands": ledger,
            "literal_root_binding": True, "validated": False,
            "pending": ["actual namespace elaboration", "original/generated kernel type equality",
                        "actual attribute/provider dependencies", "solution axiom audit"]}

"""Validate authoritative AST positions against the exact hashed UTF-8 source bytes."""
from bisect import bisect_right
import hashlib
from pathlib import Path

ALLOWED_KINDS = {"header", "command", "decl", "ref"}

def validate_facts(source: Path, facts: list[dict], source_sha256: str) -> dict:
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != source_sha256:
        raise ValueError(f"Source changed since extraction: {source}")
    data.decode("utf-8")
    starts = [0] + [i + 1 for i, byte in enumerate(data) if byte == 10]
    position_count = 0
    named_declarations = 0

    def walk(value):
        nonlocal position_count
        if isinstance(value, dict):
            if {"offset", "line", "col"} <= value.keys():
                offset = value["offset"]
                if not 0 <= offset <= len(data):
                    raise ValueError(f"Position outside source bytes: {value}")
                if offset < len(data) and data[offset] & 0xC0 == 0x80:
                    raise ValueError(f"Position splits a UTF-8 codepoint: {value}")
                if bisect_right(starts, offset) != value["line"]:
                    raise ValueError(f"Position has an inconsistent source line: {value}")
                position_count += 1
            if isinstance(value.get("start"), dict) and isinstance(value.get("end"), dict):
                if value["start"]["offset"] > value["end"]["offset"]:
                    raise ValueError(f"Reversed source range: {value}")
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    if sum(fact.get("kind") == "header" for fact in facts) != 1:
        raise ValueError("Expected exactly one parsed module header")
    for fact in facts:
        if fact.get("kind") not in ALLOWED_KINDS:
            raise ValueError(f"Unexpected oracle fact: {fact.get('kind')}")
        walk(fact)
        if fact["kind"] == "decl" and fact.get("nameRange"):
            a = fact["nameRange"]["start"]["offset"]
            b = fact["nameRange"]["end"]["offset"]
            text = data[a:b].decode("utf-8")
            # Lean's semantic name may omit identifier-quoting delimiters.
            if text.replace("«", "").replace("»", "") != fact["nameText"].replace("«", "").replace("»", ""):
                raise ValueError(f"Declaration-name bytes disagree: {text!r}, {fact['nameText']!r}")
            named_declarations += 1
    return {"positions_checked": position_count, "named_declarations_checked": named_declarations,
            "source_bytes": len(data), "crlf_count": data.count(b"\r\n")}

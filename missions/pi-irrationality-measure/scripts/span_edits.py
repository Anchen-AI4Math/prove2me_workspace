"""Apply source edits only at authoritative UTF-8 byte ranges, from right to left."""
from dataclasses import dataclass
import hashlib

@dataclass(frozen=True)
class Edit:
    start: int
    end: int
    replacement: bytes
    reason: str

def boundary(data: bytes, offset: int) -> bool:
    return 0 <= offset <= len(data) and (offset == len(data) or data[offset] & 0xC0 != 0x80)

def from_range(position_range: dict, replacement: str, reason: str) -> Edit:
    return Edit(position_range["start"]["offset"], position_range["end"]["offset"],
                replacement.encode("utf-8"), reason)

def apply_edits(data: bytes, edits: list[Edit], source_sha256: str) -> bytes:
    if hashlib.sha256(data).hexdigest() != source_sha256:
        raise ValueError("The source bytes differ from those used to extract AST positions")
    data.decode("utf-8")
    ordered = sorted(edits, key=lambda edit: (edit.start, edit.end))
    for edit in ordered:
        if edit.start > edit.end or not boundary(data, edit.start) or not boundary(data, edit.end):
            raise ValueError(f"Invalid UTF-8 byte range: {edit}")
        edit.replacement.decode("utf-8")
    for before, after in zip(ordered, ordered[1:]):
        if before.end > after.start or before.start == after.start:
            raise ValueError(f"Ambiguous overlapping edits: {before.reason}, {after.reason}")
    result = data
    for edit in reversed(ordered):
        result = result[:edit.start] + edit.replacement + result[edit.end:]
    result.decode("utf-8")
    return result

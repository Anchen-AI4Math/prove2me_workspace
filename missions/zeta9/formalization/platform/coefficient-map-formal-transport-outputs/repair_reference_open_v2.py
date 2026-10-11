"""Append private catalog import repair; preserve frozen original payloads."""
import initialize_author as p
import run_author_sources as runner


def main():
    runner.gate()
    rows = []
    for index, (suffix, short) in enumerate([("constant", "Constant"), ("five", "Five"), ("matrix", "Matrix")]):
        original = p.PROJECT / "r" / "Theorems" / ("Thm_ZetaNine_CoefficientMapFormalTransportOutputs_" + suffix + ".lean")
        raw = original.read_bytes()
        line = b"open ZetaNine.CoefficientMapFormalTransportOutputs\n"
        crlf = line.replace(b"\n", b"\r\n")
        selected = crlf if crlf in raw else line
        assert raw.count(selected) == 1
        repaired = raw.replace(selected, b"", 1)
        assert repaired.split(b"theorem ", 1)[1] == raw.split(b"theorem ", 1)[1]
        target = p.PROJECT / "r" / "Theorems" / ("Ref" + short + "V2.lean")
        if not target.exists():
            p.write(target, repaired)
        assert target.read_bytes() == repaired
        rows.append({"suffix": suffix, "original": p.bind(original), "private_repair": p.bind(target),
                     "whole_formal_header_and_body_bytes_unchanged": True,
                     "repair": "remove one unnecessary open of namespace first created by theorem declaration"})
    report = p.OUT / "author-reference-import-repair-v2.json"
    if not report.exists():
        p.dump(report, {"kind": "private import/open repair only", "rows": rows,
                        "original_frozen_payloads_unchanged": True, "catalogs_are_type_only_not_proofs": True})
    for index, (suffix, short) in enumerate([("constant", "Constant"), ("five", "Five"), ("matrix", "Matrix")]):
        runner.run("r", "rv2" + str(index), "Theorems.Ref" + short + "V2", "Theorems/Ref" + short + "V2.lean")


if __name__ == "__main__":
    main()

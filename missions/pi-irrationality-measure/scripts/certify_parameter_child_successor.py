"""Reuse the frozen legacy-value consumer for the two independent child leaves."""
import argparse
import inspect
import json
from pathlib import Path
from unittest.mock import patch
import validate_parameter_proved_child_existing as legacy

SELF = Path(__file__).resolve()
PRODUCER_SHA = "03713c04b700921ec7b01dfad6467f3d639790b33d55ea7d26a6687cfa45fc3a"
LEGACY_SHA = "197d6d9c0d93936a8a0e1f56cee1ffb8c4cb9e5639f714f32fa63379d77f76c2"
SPECS = {"c2": ("c2", "exists_rational_parameters", "independent"),
         "c3": ("c3", "exists_small_rational_sigma", "independent")}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=sorted(SPECS))
    args = parser.parse_args()
    producer = legacy.producer
    if legacy.sha(Path(producer.__file__)) != PRODUCER_SHA or legacy.sha(Path(legacy.__file__)) != LEGACY_SHA:
        raise ValueError("Frozen producer or legacy Expr consumer changed")
    c = producer.configure(SPECS[args.stage])
    base_path = producer.V / "ap4" / args.stage / "actual-child-validation.base.json"
    path = base_path.with_name("actual-child-validation.json")
    if path.exists() or base_path.exists():
        raise ValueError("Existing successor certificate retained; no overwrite")
    producer.check_only(c)
    with patch.object(legacy, "THEOREM", c["theorem"]):
        value = legacy.full_expr_pin(c)
    source = inspect.getsource(producer.validate_existing)
    anchor = ' or original_t["value"] is not None'
    if source.count(anchor) != 1:
        raise ValueError("Exact legacy-value predicate changed")
    ns = dict(producer.__dict__)
    seconds = producer.read(c["parent_validation"])["preflights"]["SnapshotGenerated.lean"]["seconds"]
    ns["generated_pf"] = {"data": {"seconds": seconds}}
    captured = []
    def capture(target, certificate):
        if target.resolve() != path.resolve() or captured:
            raise ValueError("Unexpected certificate output from frozen consumer")
        captured.append(certificate)
    ns["dump"] = capture
    exec(compile(source.replace(anchor, "", 1), str(SELF), "exec"), ns)
    base = ns["validate_existing"](c)
    if captured != [base] or not base["validated"]:
        raise ValueError("Frozen successor consumer did not yield one validated certificate")
    producer.dump(base_path, base)
    certificate = dict(base)
    certificate["historical_full_expr_source_certificate"] = value
    certificate["consumer_adapter"] = {
        "path": producer.task_rel(SELF), "sha256": legacy.sha(SELF),
        "frozen_producer_sha256": PRODUCER_SHA, "frozen_legacy_expr_consumer_sha256": LEGACY_SHA,
        "bounded_change": "legacy source proof value permitted; fresh source and child type-only guards retained",
        "legacy_generated_preflight_seconds_binding": seconds,
        "Lean_started": False, "API_used": False}
    producer.dump(path, certificate)
    print(json.dumps({"validated": True, "certificate": producer.task_rel(path),
                      "certificate_sha256": legacy.sha(path), "Std3_only": certificate["Std3_only"],
                      "max_file_seconds": certificate["max_file_seconds"]}))

if __name__ == "__main__":
    main()

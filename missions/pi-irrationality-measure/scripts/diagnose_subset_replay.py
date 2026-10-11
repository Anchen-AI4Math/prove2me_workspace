"""Read-only field diagnostics for the frozen source-subset certificate."""
import json
from pathlib import Path
import validate_provider_source_subset_snapshot as validator

prior = json.loads(validator.CERTIFICATE.read_bytes())
current, _ = validator.validate_subset(require_actual=True)
differences = []

def compare(left, right, path=""):
    if left == right:
        return
    if isinstance(left, dict) and isinstance(right, dict):
        for key in sorted(set(left) | set(right)):
            compare(left.get(key), right.get(key), path + "/" + key)
    elif isinstance(left, list) and isinstance(right, list) and len(left) == len(right):
        for index, (l, r) in enumerate(zip(left, right)):
            compare(l, r, path + "/" + str(index))
    else:
        differences.append({"field": path, "recorded": str(left)[:180], "current": str(right)[:180]})

compare(prior, current)
print(json.dumps({"equal": prior == current, "differences": differences[:20],
                  "difference_count": len(differences)}, ensure_ascii=False))

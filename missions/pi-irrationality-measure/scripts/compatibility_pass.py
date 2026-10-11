"""Apply checked one-to-one library compatibility substitutions to the port only."""
import json
from pathlib import Path
import re

TASK = Path(__file__).resolve().parents[1]
changes = []
mapping = {
    "ite_eq_right": "if_neg",
    "ite_eq_left": "if_pos",
    "Finset.prod_le_prod₀": "Finset.prod_le_prod",
    "Finset.prod_le_prod_of_subset_of_one_le₀": "Finset.prod_le_prod_of_subset_of_one_le",
    "Finset.prod_le_one₀": "Finset.prod_le_one",
    "dite_eq_left": "dif_pos",
    "dite_eq_right": "dif_neg",
    "PresheafOfModulesOfCommRing": "PresheafOfModules",
}
for path in (TASK / "port/lean").rglob("*.lean"):
    text = path.read_text(encoding="utf-8")
    for before, after in mapping.items():
        pattern = r"(?<![\w.])" + re.escape(before) + r"(?![\w'])"
        text, count = re.subn(pattern, after, text)
        if count:
            changes.append({"file": str(path.relative_to(TASK)), "from": before,
                            "to": after, "count": count})
    path.write_text(text, encoding="utf-8")
(TASK / "port/compatibility-pass.json").write_text(json.dumps(changes, ensure_ascii=False, indent=2), encoding="utf-8")
print("Compatibility substitutions:", sum(c["count"] for c in changes))

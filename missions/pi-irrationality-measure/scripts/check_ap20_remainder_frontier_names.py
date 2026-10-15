"""GET-only exact lookup of the two original analytic remainder frontiers."""
import json
import check_ap20_exact_platform_names as lookup

lookup.NAMES = [
    "OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized",
    "OAI.PiExponent.tendsto_log_translationTermCount_div",
]
lookup.OUTPUT = lookup.TASK / "verification/ap20/exact-analytic-remainder-two-frontier-lookup.json"

if __name__ == "__main__":
    print(json.dumps(lookup.run(), ensure_ascii=False, indent=2))

"""Capture bounded differences after a failed read-only ap2 replay."""
import json
from pathlib import Path
import admissible_provider_manifest_bridge as bridge
import complete_admissible_provider as complete
import generate_shared_source_snapshot as base


def differences(left, right, prefix=''):
    if type(left) is not type(right):
        return [(prefix, left, right)]
    if isinstance(left, dict):
        result = []
        for key in sorted(set(left) | set(right)):
            if key not in left or key not in right:
                result.append((prefix + '/' + key, left.get(key), right.get(key)))
            else:
                result.extend(differences(left[key], right[key], prefix + '/' + key))
        return result
    if isinstance(left, list):
        if len(left) != len(right):
            return [(prefix + '/length', len(left), len(right))]
        result = []
        for index, (a, b) in enumerate(zip(left, right, strict=True)):
            result.extend(differences(a, b, prefix + '/' + str(index)))
        return result
    return [] if left == right else [(prefix, left, right)]


try:
    with bridge.installed():
        value = complete.certify(replay=True)
    print(json.dumps(value))
except ValueError as error:
    tb = error.__traceback__
    while tb and not (tb.tb_frame.f_code.co_name == 'certify'
                     and Path(tb.tb_frame.f_code.co_filename).resolve() == Path(complete.__file__).resolve()):
        tb = tb.tb_next
    if not tb or 'report' not in tb.tb_frame.f_locals:
        raise
    report = tb.tb_frame.f_locals['report']
    stored = json.loads((bridge.DEST / 'complete-validation.json').read_bytes())
    rows = differences(stored, report)
    diagnostic = dict(error=str(error), difference_count=len(rows), differences=rows,
                      source='fresh-read-only-complete-replay', lean_started=False, api_used=False)
    base.write_json(bridge.DEST / 'replay-differences.json', diagnostic)
    print(json.dumps(diagnostic, ensure_ascii=True, indent=2))

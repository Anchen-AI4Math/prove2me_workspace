"""Isolate the new quartic proof's elaboration, without changing its source."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
code=(HERE/'machine/lean/Submission/ThreeSum/QuarticSwitch.lean').read_text(encoding='utf-8')
code=code.split('theorem meets ',1)[0]
code=code.replace('set_option maxHeartbeats 5000000','set_option maxHeartbeats 300000\nset_option profiler true')
code+='\nend ThreeSum1960614.LightQuarticSwitch\n'
(HERE/'verification/QuarticDiagnostic.lean').write_text(code,encoding='utf-8')

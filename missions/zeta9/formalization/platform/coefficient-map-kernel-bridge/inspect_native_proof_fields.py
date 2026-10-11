from pathlib import Path
import json,sys
sys.stdout.reconfigure(encoding='utf-8')
p=Path(__file__).resolve().parent;task=p.parents[2]
rs=json.loads((task/'verification/formalization-coefficient-map-kernel-2026-10-04/type-report.json').read_text(encoding='utf-8-sig'))
for r in rs:
 if r['declaration'].endswith(('.actualAggregateEquiv','.inverseMultiplier')):print(r['declaration'],r['definitionValue'][:1400])

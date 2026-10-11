"""Exact read-only diagnostic -c input retained after its actual tool exit1; not rerun."""
import sys,json
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
o=Path('verification/formalization-coefficient-map-numerator-pf-platform-independent-2026-10-07')
sys.path.insert(0,str(o))
import inspect_author as p
from analyze_oracles import records,match_decl
rec=p.load(o/'execution-receipt.json')
latest={r['label']:r for r in rec['rows'] if r['exit_code']==0}
prep=p.load(o/'source-preparation.json');sel=p.load(o/'own-native-graph-selection.json')
graph={r['name']:r for x in (p.PROJECT/'native-decl-graph.jsonl').read_text(encoding='utf-8').splitlines() for r in [json.loads(x)]}
facts={r['module']:records(latest['official-parser-'+r['module'].rsplit('.',1)[-1]]) for r in prep['native_sources']}
diffs=[(n,graph[n],match_decl(facts[graph[n]['module']],n)) for n in sel['definitions']+sel['proofs'] if not match_decl(facts[graph[n]['module']],n)['declStart']['line']<=graph[n]['startLine']<=graph[n]['endLine']<=match_decl(facts[graph[n]['module']],n)['declEnd']['line']]
print(json.dumps(diffs,ensure_ascii=False,indent=2)[:8000])

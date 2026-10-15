"""Prune proof-only imports from unpublished declarations using the Lean oracle.

Formal statements and every proof byte remain identical. No local Lean build is
run. Published and in-flight declarations are immutable. The platform compiles
the resulting declarations and checks each unchanged proof as a real reduction.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
digest = lambda b: hashlib.sha256(b).hexdigest()
manifest_path = VER / 'machine-platform-manifest.json'
manifest = read(manifest_path)
state = read(VER / 'machine-platform-publish.json')
classification = read(VER / 'machine-node-classification.json')
oracle_path = VER / 'machine-decl-graph.jsonl'
assert digest(oracle_path.read_bytes()) == classification['declaration_graph_sha256']
graph = {r['name']: r for line in oracle_path.read_text(encoding='utf-8').splitlines()
         if (r := json.loads(line)).get('name')}
records = {r['name']: r for r in manifest['theorems']}
originals = {r['original_decl']: r['name'] for r in manifest['theorems']}
modules = {r['theorem_module']: r for r in manifest['theorems']}
conversion_path = VER / 'server-macro-apply-state.json'
conversion = read(conversion_path)
changes = []
prepared = []
assert not any(graph[name].get('isInstance') for name in originals)


def required_theorems(original):
    pending = list(graph[original]['typeDeps'])
    seen = set()
    required = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name in originals:
            required.add(originals[name])
            continue
        row = graph.get(name)
        if row:
            # Follow the actual definitions/companions used by the type,
            # including their bodies and all implicit-instance material.
            pending.extend(row['typeDeps'])
            pending.extend(row['valueDeps'])
    return required, len(seen)


for record in manifest['theorems']:
    item = state['items'].get(record['name'], {})
    if record.get('existing_theorem_id') or item.get('theorem_id'):
        continue
    if item.get('job_id') and item.get('publish_status') not in ('FAILED','ERROR'):
        continue
    assert not item.get('publish_intent') or item.get('job_id'), record['name']
    required, visited_count = required_theorems(record['original_decl'])
    lines = record['preamble'].splitlines(keepends=True)
    non_imports = ''.join(line for line in lines if not line.startswith('import '))
    removed = []
    retained = []
    for line in lines:
        module = line.strip().removeprefix('import ') if line.startswith('import ') else None
        child = modules.get(module)
        if child and child['name'] not in required and child['name'] not in non_imports:
            removed.append(child['name'])
        else:
            retained.append(line)
    if not removed:
        continue
    # Import removal must not make an `open` namespace cease to exist. Empty
    # namespaces introduce no mathematical declaration or assumption.
    preamble = ''.join(retained)
    namespaces = sorted({name.rsplit('.',1)[0] for name in removed})
    imports = list(re.finditer(r'(?m)^import [\w.]+\r?$', preamble))
    assert imports
    position = imports[-1].end()
    markers = '\n\n' + '\n'.join('namespace '+name+'\nend '+name for name in namespaces) + '\n'
    preamble = preamble[:position] + markers + preamble[position:]
    path = ROOT / record['theorem_path']
    original = path.read_bytes()
    assert original.decode('utf-8') == record['preamble']+'\n'+record['formal_statement']+'\n'
    assert digest(original) == record['theorem_sha256']
    revised = (preamble+'\n'+record['formal_statement']+'\n').encode('utf-8')
    entry = conversion['items'][record['theorem_path']]
    assert entry['result_sha256'] == digest(original)
    change = {'name':record['name'],'path':record['theorem_path'],
              'previous_sha256':digest(original),'current_sha256':digest(revised),
              'removed_proof_only_imports':removed,'required_by_type_closure':sorted(required),
              'native_type_closure_declarations_checked':visited_count,
              'formal_statement_sha256':digest(record['formal_statement'].encode()),
              'proof_sha256_unchanged':record['solution_sha256']}
    changes.append(change)
    prepared.append((record,path,original,revised,preamble,entry,change))

receipt = {'planned_at_utc':datetime.now(timezone.utc).isoformat(),
           'native_declaration_oracle_sha256':digest(oracle_path.read_bytes()),
           'source_commit':manifest['source_commit'],
           'unpublished_declarations_to_adjust':len(changes),
           'proof_only_imports_removed':sum(len(c['removed_proof_only_imports']) for c in changes),
           'formal_statements_and_proof_bytes_unchanged':True,'changes':changes}
if '--apply' in sys.argv:
    assert (VER / 'machine-server-first.pause').exists()
    for record,path,original,revised,preamble,entry,change in prepared:
        backup=VER/'server-proof-originals'/(path.stem+'-'+digest(original)[:12]+'.lean.txt')
        if backup.exists():assert backup.read_bytes()==original
        else:backup.write_bytes(original)
        path.write_bytes(revised)
        record.update(preamble=preamble,theorem_sha256=digest(revised))
        entry.setdefault('post_conversion_changes',[]).append({**change,'reason':'remove proof-only imports from an unpublished declaration using native type reachability'})
        entry['result_sha256']=digest(revised)
    manifest['open_sketch_pipeline']={'enabled':True,'native_declaration_oracle_sha256':digest(oracle_path.read_bytes()),
                                      'proof_only_import_count':receipt['proof_only_imports_removed'],
                                      'formal_statements_and_proofs_unchanged':True}
    manifest_path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    conversion_path.write_text(json.dumps(conversion,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    receipt['applied_at_utc']=datetime.now(timezone.utc).isoformat()
    receipt['manifest_sha256']=digest(manifest_path.read_bytes())
(VER/'open-sketch-pipeline-plan.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in receipt.items() if k!='changes'}))

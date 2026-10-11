"""Lightweight source/DAG/resource audit; no Lean compilation."""
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def main():
    manifest = json.loads((HERE / 'platform/milestone35-manifest.json').read_text(encoding='utf-8'))
    all_slugs = [manifest['lookup']]
    for parent in manifest['parts']:
        all_slugs.extend(manifest['subparts'][parent] + [parent])
    assert len(all_slugs) == len(set(all_slugs))
    specs = {slug: json.loads((HERE / 'platform' / (slug + '.json')).read_text(encoding='utf-8')) for slug in all_slugs}
    modules = {'Theorems.Thm_' + spec['theorem_name'].replace('.', '_'): slug for slug, spec in specs.items()}
    deps = {}
    for slug, spec in specs.items():
        code = (ROOT / spec['proof_file']).read_text(encoding='utf-8')
        assert 'attribute [local irreducible] rowAt' not in code
        assert not re.search(r'\b(sorry|native_decide|axiom)\b', code)
        deps[slug] = {modules[m] for m in re.findall(r'^import (\S+)', code, re.M) if m in modules}
    remaining = set(all_slugs)
    resolved = set()
    while remaining:
        ready = {s for s in remaining if deps[s] <= resolved}
        assert ready, sorted(remaining)
        remaining -= ready
        resolved |= ready
    original = (ROOT / 'Definitions/Def_SnakyCertificate.lean').read_text(encoding='utf-8')
    entries = {int(i): [tuple(map(int, t)) for t in re.findall(r'⟨(\d+), (\d+), (\d+), (\d+)⟩', body)]
               for i, body in re.findall(r'def entry_(\d+) : Entry := ⟨\d+, \[(.*?)\]⟩', original)}
    ancestors = set()
    def visit(i):
        if i in ancestors:
            return
        ancestors.add(i)
        for child, *_ in entries.get(i, []):
            visit(child)
    for i in (557, 595, 603, 615):
        visit(i)
    result = {'support_tasks': len(all_slugs), 'acyclic_dependencies': True,
              'proof_sources_have_no_sorry_axiom_native_decide': True,
              'endpoint_ancestor_rows': len(ancestors), 'local_lean_started': False}
    (HERE / 'verification/remote-source-audit.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result), flush=True)

if __name__ == '__main__':
    main()

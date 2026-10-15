"""Seal dependency-closed, atomic public reuse after all compiler gates pass."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from audit_extended_machine_reuse import main as audit

HERE = Path(__file__).resolve().parent
VER = HERE / 'verification'
ROOT = HERE.parents[1]


def read(name):
    return json.loads((VER / name).read_text(encoding='utf-8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expr_hash(value):
    return hashlib.sha256(value.encode()).hexdigest() if value is not None else None


def main():
    audit()
    report = read('extended-reuse-atomic-audit.json')
    assert report['all_participating_units_available'], 'All exact-source Stage 2 units must be available'
    assert read('public-theorem-probe-errors.json') == [], 'Public statement elaboration must be error-free'
    catalog = read('machine-public-1962-catalog.json')
    assert catalog['snapshot_complete']
    assert (datetime.now(timezone.utc) - datetime.fromisoformat(catalog['checked_at_utc'])).total_seconds() < 3600
    current = {r['theorem_name']: r for r in catalog['records']}
    for item in read('public-theorem-probe-inputs.json'):
        for key in ('preamble', 'formal_statement', 'theorem_id'):
            assert item[key] == current[item['theorem_name']][key], (item['theorem_name'], key)

    index = read('extended-reuse-compact-index.json')
    # Recompute every compact hash from the full compiler readback. These large
    # JSONL files are streamed so publication does not need gigabytes of RAM.
    for side in ('native', 'public'):
        seen = set()
        with (VER / ('extended-reuse-' + side + '.jsonl')).open(encoding='utf-8') as handle:
            for line in handle:
                ci = json.loads(line)
                row = index[side][ci['name']]
                seen.add(ci['name'])
                for key in ('name', 'module', 'kind', 'isProof', 'universeCount', 'axioms', 'shape'):
                    assert row[key] == ci[key], (side, ci['name'], key)
                for key, field in (('type_sha256', 'type'), ('value_sha256', 'value'),
                                   ('raw_type_sha256', 'rawType'), ('raw_value_sha256', 'rawValue')):
                    assert row[key] == expr_hash(ci[field]), (side, ci['name'], key)
        assert seen == set(index[side])

    seed_path = VER / 'machine-definition-reuse-seed-v1.json'
    if not seed_path.exists():
        active = read('machine-definition-reuse.json')
        assert active['source_definition_count'] == 229 and active.get('schema_version', 1) == 1
        seed_path.write_text(json.dumps(active, indent=2) + '\n', encoding='utf-8')
    seed = read(seed_path.name)
    names = set(report['compatible_source_names']) & set(index['public'])
    frozen_modules = {'Submission.EndStatement', 'Submission.ThreeSum.AnalysisDefinitions'}
    frozen_names = {n for n, r in seed['definitions'].items() if r['native_module'] in frozen_modules}
    assert frozen_names <= set(report['compatible_names']), 'Frozen goal/specification interfaces must remain canonical'
    seed_by_module = {}
    for name, record in seed['definitions'].items():
        seed_by_module.setdefault(record['native_module'], set()).add(name)
    full_seed_modules = {module for module, members in seed_by_module.items()
                         if members <= set(report['compatible_names'])}
    # A partial Syntax/Logic relocation also needs freshly scoped macros. Keep
    # the old structural notation CIs only for wholly canonical seed modules.
    names.update(n for n, r in seed['definitions'].items() if r['native_module'] in full_seed_modules)
    providers = read('machine-public-definition-providers.json')
    for record in seed['modules'].values():
        providers.setdefault(record['definition_module'], {
            'module': record['definition_module'], 'theorem_id': record['theorem_id'],
            'sha256': record['public_sha256'], 'source': 'sealed original four-provider audit'})
    definitions, modules = {}, {}
    for name in sorted(names):
        native, public = index['native'][name], index['public'][name]
        provider = providers[public['module']]
        path = ROOT / Path(*public['module'].split('.')).with_suffix('.lean')
        assert sha(path) == provider['sha256'], public['module']
        definitions[name] = {
            'native_module': native['module'], 'definition_module': public['module'],
            'theorem_id': provider['theorem_id'],
            'check': ('kernel-definitional-equality' if name in report['kernel_checked_overrides']
                      else 'exact-alpha-type-and-matcher-normal-value-with-ABI-and-atomic-dependency-closure')}
        module = modules.setdefault(native['module'], {
            'native_sha256': sha(HERE / 'machine/lean' / Path(*native['module'].split('.')).with_suffix('.lean')),
            'providers': {}, 'skip_macro_bundle': native['module'] in full_seed_modules})
        module['providers'][public['module']] = {
            'definition_module': public['module'], 'theorem_id': provider['theorem_id'],
            'public_sha256': provider['sha256']}
    for record in modules.values():
        record['providers'] = [value for _, value in sorted(record['providers'].items())]

    evidence = [
        'machine-definition-reuse-seed-v1.json', 'extended-reuse-atomic-audit.json',
        'extended-reuse-compact-index.json', 'extended-reuse-native.jsonl', 'extended-reuse-public.jsonl',
        'dump_extended_reuse_native.lean', 'dump_extended_reuse_public.lean',
        'reuse-generated-equalities-check.txt', 'check_reuse_generated_equalities.lean',
        'machine-native-matchers.json', 'machine-public-definition-providers.json',
        'machine-public-1962-catalog.json', 'public-theorem-probe-inputs.json',
        'probe_public_theorem_types.lean', 'public-theorem-probe-types.json', 'public-theorem-probe-errors.json']
    manifest = {
        'approved': True, 'schema_version': 2, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_definition_count': len(definitions), 'definitions': definitions, 'modules': modules,
        'evidence': {name: sha(VER / name) for name in evidence},
        'normalization': report['method'], 'atomic_source_commands': True}
    (VER / 'machine-definition-reuse.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')

    # Preserve the previously accepted analytic/model mappings. Compatible
    # public nodes are linked by their original canonical names, never copied.
    plan = read('machine-upload-plan.json')
    for name, record in list(plan['accepted_library_nodes'].items()):
        if (record.get('check') == 'exact elaborated public type with atomic-compatible data dependencies'
                and name not in report['compatible_public_theorems']):
            del plan['accepted_library_nodes'][name]
    for name, record in report['compatible_public_theorems'].items():
        assert record['status'] == 'Proved'
        existing = plan['accepted_library_nodes'].get(name)
        assert existing is None or existing['theorem_id'] == record['theorem_id'], name
        plan['accepted_library_nodes'][name] = {
            'theorem_id': record['theorem_id'], 'platform_name': name,
            'check': 'exact elaborated public type with atomic-compatible data dependencies',
            'catalog_checked_at_utc': catalog['checked_at_utc']}
    plan['extended_reuse_audit_sha256'] = sha(VER / 'extended-reuse-atomic-audit.json')
    (VER / 'machine-upload-plan.json').write_text(json.dumps(plan, indent=2) + '\n', encoding='utf-8')
    print('Approved', len(definitions), 'sourced CIs in', len(modules), 'native modules, and',
          len(report['compatible_public_theorems']), 'proved public theorem interfaces.')


if __name__ == '__main__':
    main()

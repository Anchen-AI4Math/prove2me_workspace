"""Strict offline certificate for the genuine original-name Collision child mirror."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path

import stage_collision_remainder_child_mirror as stage
import certify_collision_remainder_limit_node_v3 as prior
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
SOURCE_OWNERS = {'OAI.NumberTheory.PiExponent.Polynomials.SimplexLog',
                 'OAI.NumberTheory.PiExponent.Analysis.Collision'}
BOUNDARY = sorted(['OAI.PiExponent.Collision.collisionRatio',
                   'OAI.PiExponent.Collision.collisionRemainder',
                   'OAI.PiExponent.tendsto_log_div_of_normalized_pow'])


def need(cond: bool, message: str) -> None:
    if not cond:
        raise ValueError(message)


def read(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def written(path: Path, record: dict):
    data = record['data']
    end = datetime.fromisoformat(data['at_utc']).timestamp()
    need(path.is_file() and end - data['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Kernel JSON was not written in its actual bounded compiler window: ' + str(path))
    return read(path)


def types(rows: list[dict], names: list[str]) -> dict[str, dict]:
    need(isinstance(rows, list) and [r.get('name') for r in rows] == names,
         'Actual theorem TypeOnly root domain differs')
    result = {}
    for row in rows:
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['value'] is None and isinstance(row['prettyType'], str)
             and bool(row['prettyType']), 'Theorem TypeOnly value/shape differs')
        kernel.checked_expr(row['type'], set(row['levelParams']))
        result[row['name']] = row
    return result


def proof_rows(doc: dict, side: str, roots: list[str], modules: set[str], module_name: str):
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
                      'rootNames', 'boundaryNames', 'rows'}
         and doc['schemaVersion'] == 1 and doc['side'] == side
         and doc['probeMainModule'] == module_name
         and doc['rootNames'] == roots and doc['boundaryNames'] == BOUNDARY,
         'Actual proof-reference envelope differs')
    rows = doc['rows']
    names = [r['name'] for r in rows]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual closed proof reference root/CI domain differs')
    for row in rows:
        owner = row['owner']['module']
        need(owner in modules and row['closedType'] is True
             and row['closedValue'] is True and set(row['axioms']) <= STD3,
             'Closed theorem owner/value/Std3 differs: ' + row['name'])
        kernel.evidence_row(row, name=row['name'], module=owner, helper=True)
    return {r['name']: r for r in rows}


def validate() -> dict:
    stage.check_only()
    # One complete prior source/proof certificate replay; all later comparisons
    # use its already genuine source c3 output without re-running Lean.
    old = prior.validate()
    need(old['validated'] is True and old['Std3_only'] is True and
         old['references_bitwise_equal_under_actual_mapping'] is True,
         'Historical full source proof certificate differs')
    prep = read(stage.STAGE / 'preparation.json')
    need(prep['source_commit'] == 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
         and prep['original_proof_suffixes_unchanged'] is True
         and prep['only_private_visibility_prefix_added'] is True
         and prep['public_platform_boundary_names'] == [stage.TARGET]
         and prep['private_helper_names'] == [stage.HELPER]
         and prep['accepted_theorem_id'] == '3d02d61e-2783-4a0c-82ca-a411ca66c0fc'
         and prep['accepted_proof_id'] == 'f31fb318-a908-4905-beef-f1f9d8d716d3'
         and prep['reused_actual_source_type_json_sha256'] == stage.SHA(stage.SOURCE_TYPES)
         and prep['reused_actual_source_proof_references_json_sha256'] == stage.SHA(stage.SOURCE_REFS),
         'Frozen original AST/Accepted binding/source-reuse preparation differs')
    specs = [(stage.OUTPUT, 'emit-olean', stage.MODULE),
             (stage.SNAPSHOT, 'modecheck', 'GeneratedSnapshot')]
    records = {}
    for i, (filename, mode, module) in enumerate(specs, 1):
        record = context.record(stage.STAGE / filename, stage.STAGE / f'c{i}.json',
                                mode, module, stage.STAGE)
        data = record['data']
        need(data['success'] is True and data['exit_code'] == 0 and
             data['timed_out'] is False and 0 < data['seconds'] <= 300 and
             data['timeout_seconds'] == 300 and data['mode'] == mode and
             'emit_olean' not in data and data['runner'] == stage.rel(stage.RUNNER)
             and data['runner_sha256'] == stage.SHA(stage.RUNNER)
             and data['legacy_runner_sha256'] == stage.SHA(stage.LEGACY)
             and data['cleanup_completed'] is True,
             'Actual bounded mirror compiler record differs: ' + filename)
        if mode == 'modecheck':
            need(data['output_olean'] is None and data['output_olean_sha256'] is None,
                 'Metadata-only probe emitted OLean')
        records[filename] = record
    olean = stage.V / 'staged-build/lib/lean' / Path(stage.OUTPUT).with_suffix('.olean')
    need(records[stage.OUTPUT]['data']['output_olean_sha256'] == stage.SHA(olean),
         'Actual original-name mirror OLean differs')
    imported = kernel.imported_dep(records[stage.SNAPSHOT], stage.MODULE)
    need(Path(imported['path']).resolve() == olean.resolve()
         and imported['sha256_before'] == stage.SHA(olean),
         'Generated proof probe imported different mirror OLean')
    inventory = written(stage.STAGE / stage.INVENTORY, records[stage.SNAPSHOT])
    need(set(inventory) == {'schemaVersion', 'probeMainModule', 'mirrorModule',
                            'sourceHelper', 'actualPrivateHelper', 'publicTarget',
                            'rawOwnedNames', 'rawOwnedCIs'}
         and inventory['schemaVersion'] == 1
         and inventory['probeMainModule'] == 'GeneratedSnapshot'
         and inventory['mirrorModule'] == stage.MODULE
         and inventory['sourceHelper'] == stage.HELPER
         and inventory['publicTarget'] == stage.TARGET,
         'Actual full owned-CI inventory envelope differs')
    private = inventory['actualPrivateHelper']
    names = inventory['rawOwnedNames']
    rows = inventory['rawOwnedCIs']
    need(names == sorted(set(names)) and [r['actualName'] for r in rows] == names
         and set(names) == {private, stage.TARGET}
         and private != stage.HELPER and private.startswith('_private.'),
         'An owned proof helper or public theorem is not certified')
    by_name = {r['actualName']: r for r in rows}
    need(by_name[private]['privateUserName'] == stage.HELPER
         and by_name[stage.TARGET]['privateUserName'] is None
         and all(r['kind'] == 'theorem' and r['isProp'] is True
                 and r['closedValue'] is True for r in rows),
         'Private/public actual CI kind, user name, Prop, or closedness differs')
    for row in rows:
        kernel.evidence_row(row['CI'], name=row['actualName'],
                            module=stage.MODULE, helper=True)
    source_type = types(read(stage.SOURCE_TYPES), [stage.HELPER, stage.TARGET])
    generated_type = types(written(stage.STAGE / stage.TYPES, records[stage.SNAPSHOT]),
                           [private, stage.TARGET])
    source_refs = proof_rows(read(stage.SOURCE_REFS), 'source',
                             [stage.HELPER, stage.TARGET], SOURCE_OWNERS, 'SourceSnapshot')
    generated_refs = proof_rows(written(stage.STAGE / stage.REFS, records[stage.SNAPSHOT]),
                                'generated', [private, stage.TARGET],
                                {stage.MODULE}, 'GeneratedSnapshot')
    mapping = {stage.HELPER: private, stage.TARGET: stage.TARGET}
    need(set(source_refs) == set(mapping) and set(generated_refs) == set(mapping.values()),
         'Actual owned CI proof closure exceeds precisely the original two theorem commands')
    for name, mapped in mapping.items():
        a, b = source_type[name], generated_type[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1],
             'Actual original/private full kernel theorem type differs: ' + name)
        a, b = source_refs[name], generated_refs[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Actual original/private full proof type or Std3 differs: ' + name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need({mapping.get(x, x) for x in a[field]} == set(b[field]),
                 'Actual original/private proof references differ: ' + name + ':' + field)
        for used in b['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in generated_refs or used in BOUNDARY or
                     used in prior.EXPECTED_ACTUAL_AUTO,
                     'Generated project proof reference lacks exact certified boundary: ' + used)
    need(generated_refs[stage.TARGET] == by_name[stage.TARGET]['CI'],
         'Actual public target CI differs from complete owned inventory')
    return {'schema_version': 1,
        'artifact_kind': 'ap20-original-name-closed-collision-remainder-private-mirror-validation',
        'validated': True, 'Std3_only': True,
        'source_commit': prep['source_commit'], 'platform_module': stage.MODULE,
        'accepted_theorem_id': prep['accepted_theorem_id'],
        'accepted_proof_id': prep['accepted_proof_id'],
        'accepted_evidence_sha256': stage.SHA(stage.PUB),
        'public_platform_boundary_names': [stage.TARGET],
        'actual_private_helper_mappings': [{'sourceName': stage.HELPER,
                                            'actualName': private,
                                            'privateUserName': stage.HELPER,
                                            'owner': generated_refs[private]['owner']}],
        'raw_owned_inventory_exact': True,
        'source_and_generated_full_types_equal': True,
        'source_and_generated_actual_proof_references_paired': True,
        'references_bitwise_equal_under_actual_mapping': True,
        'original_proof_suffixes_unchanged': True,
        'reused_source_certificate_sha256': stage.SHA(stage.SOURCE_CERT),
        'reused_source_type_json_sha256': stage.SHA(stage.SOURCE_TYPES),
        'reused_source_proof_references_json_sha256': stage.SHA(stage.SOURCE_REFS),
        'preparation_sha256': stage.SHA(stage.STAGE / 'preparation.json'),
        'generated_type_json_sha256': stage.SHA(stage.STAGE / stage.TYPES),
        'generated_refs_json_sha256': stage.SHA(stage.STAGE / stage.REFS),
        'owned_inventory_sha256': stage.SHA(stage.STAGE / stage.INVENTORY),
        'provider_olean': stage.rel(olean),
        'provider_olean_sha256': stage.SHA(olean),
        'preflights': {name: record['data'] for name, record in records.items()},
        'implementation_hashes': {stage.rel(SELF): stage.SHA(SELF),
                                  stage.rel(stage.SELF): stage.SHA(stage.SELF)}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    x = parser.add_mutually_exclusive_group(required=True)
    x.add_argument('--certify-existing', action='store_true')
    x.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    result = validate()
    path = stage.STAGE / stage.CERTIFICATE
    if args.certify_existing:
        path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    else:
        need(path.is_file() and read(path) == result,
             'Saved genuine mirror certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(path),
                      'sha256': stage.SHA(path)}))


if __name__ == '__main__':
    main()

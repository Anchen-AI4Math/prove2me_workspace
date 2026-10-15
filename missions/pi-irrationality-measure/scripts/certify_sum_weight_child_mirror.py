"""Strict offline certificate for the original-name Collision child mirror."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path

import stage_sum_weight_child_mirror as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
read, sha, need, rel = stage.read, stage.sha, stage.need, stage.rel


def written(path, preflight):
    data = preflight['data']
    end = datetime.fromisoformat(data['at_utc']).timestamp()
    need(path.is_file() and end - data['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Snapshot JSON was not written during its actual bounded compiler invocation: ' + rel(path))
    return read(path)


def type_rows(path, preflight, names):
    rows = written(path, preflight)
    need(isinstance(rows, list) and [r.get('name') for r in rows] == names,
         'Actual source/generated TypeOnly root domain differs')
    result = {}
    for row in rows:
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['value'] is None and isinstance(row['prettyType'], str)
             and bool(row['prettyType']), 'Theorem TypeOnly value/shape differs')
        kernel.checked_expr(row['type'], set(row['levelParams']))
        kernel.normalized_type(row)
        result[row['name']] = row
    return result


def proof_rows(path, preflight, side, roots, module):
    doc = written(path, preflight)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
                      'rootNames', 'boundaryNames', 'rows'}
         and doc['schemaVersion'] == 1 and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == [],
         'Actual proof-reference probe envelope differs')
    rows = doc['rows']
    need([r['name'] for r in rows] == sorted(set(r['name'] for r in rows))
         and set(roots) <= {r['name'] for r in rows},
         'Actual closed proof reference root or unique CI domain differs')
    for row in rows:
        kernel.evidence_row(row, name=row['name'], module=module, helper=True)
    return {r['name']: r for r in rows}


def validate():
    stage.check_only()
    prep = read(stage.STAGE / 'preparation.json')
    need(prep['original_AST_units'] == 2 and prep['original_source_lines'] == 35
         and prep['private_helper_names'] == [stage.HELPER]
         and prep['public_platform_boundary_names'] == [stage.TARGET]
         and prep['only_private_visibility_prefix_added'] is True
         and prep['all_original_proof_suffixes_unchanged'] is True,
         'Frozen original source/private theorem boundary differs')
    records = {}
    specs = [(stage.OUTPUT, 'emit-olean', stage.MODULE),
             (stage.SOURCE_SNAPSHOT, 'modecheck', 'SourceSnapshot'),
             (stage.GENERATED_SNAPSHOT, 'modecheck', 'GeneratedSnapshot')]
    for i, (filename, mode, module) in enumerate(specs, 1):
        record = context.record(stage.STAGE / filename, stage.STAGE / f'c{i}.json',
                                mode, module, stage.STAGE)
        data = record['data']
        need(data['success'] is True and data['exit_code'] == 0
             and data['timed_out'] is False and 0 < data['seconds'] <= 300
             and data['timeout_seconds'] == 300 and data['mode'] == mode
             and 'emit_olean' not in data,
             'Actual bounded child compiler record differs: ' + filename)
        need(data['runner'] == rel(stage.RUNNER)
             and data['runner_sha256'] == sha(stage.RUNNER)
             and data['legacy_runner_sha256'] == sha(stage.LEGACY_RUNNER)
             and data['cleanup_completed'] is True,
             'Actual bounded compiler/runtime provenance differs')
        if mode == 'modecheck':
            need(data['output_olean'] is None and data['output_olean_sha256'] is None,
                 'Metadata-only snapshot emitted OLean')
        records[filename] = record
    olean = stage.V / 'staged-build/lib/lean' / Path(stage.OUTPUT).with_suffix('.olean')
    need(records[stage.OUTPUT]['data']['output_olean_sha256'] == sha(olean),
         'Actual original-name mirror OLean differs')
    imported = kernel.imported_dep(records[stage.GENERATED_SNAPSHOT], stage.MODULE)
    need(Path(imported['path']).resolve() == olean.resolve()
         and imported['sha256_before'] == sha(olean),
         'Generated proof snapshot imported a different mirror OLean')
    mapping_doc = written(stage.STAGE / stage.MAPPING_JSON, records[stage.GENERATED_SNAPSHOT])
    need(set(mapping_doc) == {'schemaVersion', 'probeMainModule', 'mirrorModule',
                              'sourceHelper', 'actualPrivateHelper', 'actualPrivateUserName',
                              'actualOwnedPrivateNames',
                              'privateOwner', 'publicTarget', 'actualOwnedPublicNames',
                              'actualOwnedPublicCIs'}
         and mapping_doc['schemaVersion'] == 1
         and mapping_doc['probeMainModule'] == 'GeneratedSnapshot'
         and mapping_doc['mirrorModule'] == stage.MODULE
         and mapping_doc['sourceHelper'] == stage.HELPER
         and mapping_doc['actualPrivateUserName'] == stage.HELPER
         and mapping_doc['publicTarget'] == stage.TARGET,
         'Actual private helper resolver envelope differs')
    private = mapping_doc['actualPrivateHelper']
    kernel.imported_owner({'owner': mapping_doc['privateOwner']}, stage.MODULE)
    need(private != stage.HELPER and private.startswith('_private.')
         and mapping_doc['actualOwnedPrivateNames'] == [private]
         and mapping_doc['actualOwnedPublicNames'] == [stage.TARGET]
         and [r['actualName'] for r in mapping_doc['actualOwnedPublicCIs']] == [stage.TARGET],
         'Private helper leaked or additional owned public CI needs explicit audit')
    public_ci = mapping_doc['actualOwnedPublicCIs'][0]
    need(public_ci['actualIsProp'] is True,
         'Public target is not an actual kernel proposition')
    kernel.evidence_row(public_ci['CI'], name=stage.TARGET, module=stage.MODULE, helper=True)
    mapping = {stage.HELPER: private, stage.TARGET: stage.TARGET}
    source_names = [stage.HELPER, stage.TARGET]
    generated_names = [private, stage.TARGET]
    source = type_rows(stage.STAGE / stage.SOURCE_TYPE_JSON,
                       records[stage.SOURCE_SNAPSHOT], source_names)
    generated = type_rows(stage.STAGE / stage.GENERATED_TYPE_JSON,
                          records[stage.GENERATED_SNAPSHOT], generated_names)
    source_refs = proof_rows(stage.STAGE / stage.SOURCE_REFS_JSON,
                             records[stage.SOURCE_SNAPSHOT], 'source', source_names,
                             stage.SOURCE_MODULE)
    generated_refs = proof_rows(stage.STAGE / stage.GENERATED_REFS_JSON,
                                records[stage.GENERATED_SNAPSHOT], 'generated',
                                generated_names, stage.MODULE)
    extras = pairing.pair_extra({n: r for n, r in source_refs.items() if n not in mapping},
                                {n: r for n, r in generated_refs.items()
                                 if n not in mapping.values()}, mapping)
    mapping.update(extras)
    need(generated_refs[stage.TARGET] == public_ci['CI'],
         'Actual public inventory target CI differs from closed proof export')
    old_type = read(stage.OLD / 'original-type.json')[0]
    need(kernel.normalized_type(old_type) == kernel.normalized_type(source[stage.TARGET]),
         'Historical Accepted source kernel type differs from new original-source probe')
    for name, mapped in mapping.items():
        if name in source:
            need(kernel.normalized_type(source[name])[0] == kernel.normalized_type(generated[mapped])[0]
                 and kernel.rename_expr(kernel.normalized_type(source[name])[1], mapping)
                     == kernel.normalized_type(generated[mapped])[1],
                 'Actual original/private root full kernel type differs: ' + name)
        a, b = source_refs[name], generated_refs[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Actual original/private proof CI full type/Std3 differs: ' + name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need({mapping.get(x, x) for x in a[field]} == set(b[field]),
                 'Actual original/private closed proof references differ: '
                 + name + ':' + field)
        for used in b['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in generated_refs,
                     'Generated project proof reference lacks closed mirror provenance: ' + used)
    return {'schema_version': 1,
            'artifact_kind': 'ap18-original-name-closed-sum-weight-private-mirror-validation',
            'source_commit': prep['source_commit'],
            'source_name': stage.TARGET, 'platform_module': stage.MODULE,
            'historical_accepted_theorem_id': prep['historical_Accepted_theorem_id'],
            'historical_accepted_proof_id': prep['historical_Accepted_proof_id'],
            'accepted_theorem_id': prep['historical_Accepted_theorem_id'],
            'accepted_proof_id': prep['historical_Accepted_proof_id'],
            'accepted_evidence_sha256': sha(stage.OLD / 'publication.json'),
            'public_platform_boundary_names': [stage.TARGET],
            'actual_private_helper_mapping': {stage.HELPER: private},
            'actual_private_helper_mappings': [{'sourceName': stage.HELPER,
                                                'actualName': private,
                                                'privateUserName': stage.HELPER,
                                                'owner': mapping_doc['privateOwner']}],
            'actual_private_helper_owner': mapping_doc['privateOwner'],
            'actual_owned_public_names': mapping_doc['actualOwnedPublicNames'],
            'all_original_proof_suffixes_unchanged': True,
            'historical_Accepted_wire_and_type_verified': True,
            'source_and_generated_types_equal': True,
            'source_and_generated_actual_proof_references_paired': True,
            'references_bitwise_equal_under_private_mapping': True,
            'Std3_only': True, 'provider_olean': rel(olean),
            'provider_olean_sha256': sha(olean),
            'preparation_sha256': sha(stage.STAGE / 'preparation.json'),
            'generated_json_sha256': {filename: sha(stage.STAGE / filename) for filename in
                                      [stage.SOURCE_TYPE_JSON, stage.GENERATED_TYPE_JSON,
                                       stage.SOURCE_REFS_JSON, stage.GENERATED_REFS_JSON,
                                       stage.MAPPING_JSON]},
            'preflights': records,
            'actual_source_and_generated_CI_count': len(mapping),
            'implementation_hashes': {rel(p): sha(p) for p in
                                      [SELF, stage.SELF, Path(kernel.__file__),
                                       Path(pairing.__file__), Path(context.__file__)]},
            'max_file_seconds': max(r['data']['seconds'] for r in records.values()),
            'validated': True, 'submission_ready': False,
            'Lean_started_by_consumer': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--certify-existing', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    report = validate()
    path = stage.STAGE / stage.CERTIFICATE
    raw = stage.encode(report)
    if path.exists():
        need(path.read_bytes() == raw, 'Existing immutable sum-weight mirror certificate differs')
    elif args.certify_existing:
        path.write_bytes(raw)
    else:
        need(False, 'No actual certified sum-weight mirror result yet')
    print(json.dumps({'certificate': rel(path), 'certificate_sha256': sha(path),
                      'validated': True, 'max_file_seconds': report['max_file_seconds'],
                      'Lean_started': False, 'API_used': False}, indent=2))


if __name__ == '__main__':
    main()

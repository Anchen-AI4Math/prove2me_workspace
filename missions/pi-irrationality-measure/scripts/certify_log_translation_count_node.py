"""Strict offline certificate for the four-original-AST translation-count node."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path

import stage_log_translation_count_node as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
BOUNDARY = sorted(['OAI.PiExponent.translationTermCount',
                   'OAI.PiExponent.tendsto_log_div_of_normalized_pow'])
SOURCES = set(stage.SOURCE_MODULES)


def need(cond: bool, reason: str) -> None:
    if not cond:
        raise ValueError(reason)


def read(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def written(path: Path, record: dict):
    data = record['data']
    end = datetime.fromisoformat(data['at_utc']).timestamp()
    need(path.is_file() and end - data['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Actual kernel JSON was not written in compiler invocation window: ' + stage.rel(path))
    return read(path)


def types(path: Path, record: dict, expected: list[str]):
    rows = written(path, record)
    need(isinstance(rows, list) and [row.get('name') for row in rows] == expected,
         'Actual theorem TypeOnly roots differ')
    result = {}
    for row in rows:
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['value'] is None and isinstance(row['prettyType'], str)
             and bool(row['prettyType']), 'Theorem TypeOnly value/shape differs')
        kernel.checked_expr(row['type'], set(row['levelParams']))
        result[row['name']] = row
    return result


def proofs(path: Path, record: dict, side: str, roots: list[str], modules: set[str]):
    doc = written(path, record)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
                      'rootNames', 'boundaryNames', 'rows'}
         and doc['schemaVersion'] == 1 and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == BOUNDARY,
         'Actual source/generated full proof-reference envelope differs')
    rows = doc['rows']
    names = [row['name'] for row in rows]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual proof reference root/domain differs')
    for row in rows:
        owner = row['owner']['module']
        need(owner in modules and row['closedType'] is True
             and row['closedValue'] is True and set(row['axioms']) <= STD3,
             'Actual proof CI owner/closedness/Std3 differs: ' + row['name'])
        kernel.evidence_row(row, name=row['name'], module=owner, helper=True)
    return {r['name']: r for r in rows}


def validate():
    stage.check_only()
    prep = read(stage.STAGE / 'preparation.json')
    need(prep['source_commit'] == stage.route.COMMIT
         and prep['original_source_lines'] == 42
         and prep['three_helper_proof_suffixes_unchanged'] is True
         and prep['target_proof_suffix_unchanged'] is True
         and prep['global_solution_name_only_rewritten'] is True
         and prep['source_type_only_names'] == stage.HELPERS + [stage.TARGET]
         and prep['published_data_definition_id'] == '04008248-130e-40ba-b6a3-df3e9b9df91b'
         and prep['accepted_logdiv_theorem_id'] == '8b1c0341-2978-4a9d-8acc-8a5e3538cbda'
         and prep['actual_exact_name_lookup_sha256'] == stage.file_sha(stage.LOOKUP),
         'Frozen source AST/proof/boundary/lookup preparation differs')
    data_cert = read(stage.route.CERT)
    pub = read(stage.route.PUBLISHED)
    logdiv = read(stage.route.LOGDIV_CERT)
    body = pub['target_readback']['body']
    need(data_cert['validated'] is True and data_cert['Std3_only'] is True
         and data_cert['actual_owned_CI_names'] == sorted(data_cert['actual_owned_CI_names'])
         and 'OAI.PiExponent.translationTermCount' in data_cert['provided_names']
         and not any(name.startswith('OAI.PiExponent.translationTermCount.')
                     for name in data_cert['actual_owned_CI_names'])
         and pub['definition_id'] == '04008248-130e-40ba-b6a3-df3e9b9df91b'
         and pub['last_publish_verdict']['body']['status'] == 'PUBLISHED'
         and body['status'] == 'Definition' and body['visibility'] == 'public'
         and body['definition'] == pub['publish_intent']['payload']['definition']
         and body['deprecated_at'] is None
         and logdiv['validated'] is True and logdiv['Std3_only'] is True
         and logdiv['accepted_theorem_id'] == '8b1c0341-2978-4a9d-8acc-8a5e3538cbda',
         'Published exact Def / no-extra-equation / Accepted LogDiv certificate differs')
    records = {}
    for i, (output, mode) in enumerate(zip(stage.FILES, stage.MODES, strict=True), 1):
        module = Path(output).with_suffix('').as_posix().replace('/', '.')
        record = context.record(stage.STAGE / output, stage.STAGE / f'c{i}.json',
                                mode, module, stage.STAGE)
        data = record['data']
        need(data['success'] is True and data['exit_code'] == 0 and
             data['timed_out'] is False and 0 < data['seconds'] <= 300
             and data['timeout_seconds'] == 300 and data['mode'] == mode
             and 'emit_olean' not in data
             and data['runner'] == stage.rel(stage.RUNNER)
             and data['runner_sha256'] == stage.file_sha(stage.RUNNER)
             and data['legacy_runner_sha256'] == stage.file_sha(stage.LEGACY)
             and data['cleanup_completed'] is True,
             'Actual bounded compiler context differs: ' + output)
        if mode == 'modecheck':
            need(data['output_olean'] is None and data['output_olean_sha256'] is None,
                 'Comparator or metadata probe emitted OLean')
        records[output] = record
    olean = stage.V / 'staged-build/lib/lean' / Path(stage.SOLUTION_OUTPUT).with_suffix('.olean')
    need(records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'] == stage.file_sha(olean),
         'Actual global closed solution OLean differs')
    imported = kernel.imported_dep(records[stage.GENERATED_SNAPSHOT], stage.SOLUTION_MODULE)
    need(Path(imported['path']).resolve() == olean.resolve()
         and imported['sha256_before'] == stage.file_sha(olean),
         'Generated actual proof snapshot imported a different solution OLean')
    source_roots = stage.HELPERS + [stage.TARGET]
    inventory = written(stage.STAGE / stage.INVENTORY,
                        records[stage.GENERATED_SNAPSHOT])
    need(set(inventory) == {'schemaVersion', 'probeMainModule', 'solutionModule',
                            'sourceHelpers', 'actualPrivateHelpers',
                            'publicPlatformTarget', 'rawOwnedNames', 'rawOwnedCIs'}
         and inventory['schemaVersion'] == 1
         and inventory['probeMainModule'] == 'GeneratedSnapshot'
         and inventory['solutionModule'] == stage.SOLUTION_MODULE
         and inventory['sourceHelpers'] == stage.HELPERS
         and inventory['publicPlatformTarget'] == 'solution',
         'Actual raw solution-owned CI inventory envelope differs')
    private = inventory['actualPrivateHelpers']
    generated_roots = private + ['solution']
    need(len(private) == 3 and len(set(private)) == 3
         and all(name.startswith('_private.') for name in private),
         'Three original helpers were not uniquely compiled as private CIs')
    mapping = dict(zip(stage.HELPERS, private, strict=True))
    mapping[stage.TARGET] = 'solution'
    raw_names = inventory['rawOwnedNames']
    raw_rows = inventory['rawOwnedCIs']
    need(raw_names == sorted(set(raw_names))
         and [r['actualName'] for r in raw_rows] == raw_names
         and set(generated_roots) <= set(raw_names),
         'Actual raw owned CI names/domain differs')
    for row in raw_rows:
        need(row['kind'] == 'theorem' and row['isProp'] is True,
             'Unexpected owned non-Prop or non-theorem CI: ' + row['actualName'])
        kernel.evidence_row(row['CI'], name=row['actualName'],
                            module=stage.SOLUTION_MODULE, helper=True)
    for source_name, actual in zip(stage.HELPERS, private, strict=True):
        row = next(r for r in raw_rows if r['actualName'] == actual)
        need(row['privateUserName'] == source_name,
             'Actual private helper user-name mapping differs: ' + source_name)
    need(next(r for r in raw_rows if r['actualName'] == 'solution')['privateUserName'] is None,
         'Global solution is private')
    a_types = types(stage.STAGE / stage.SOURCE_TYPES, records[stage.SOURCE_SNAPSHOT], source_roots)
    b_types = types(stage.STAGE / stage.GENERATED_TYPES, records[stage.GENERATED_SNAPSHOT], generated_roots)
    a_refs = proofs(stage.STAGE / stage.SOURCE_REFS, records[stage.SOURCE_SNAPSHOT],
                    'source', source_roots, SOURCES)
    b_refs = proofs(stage.STAGE / stage.GENERATED_REFS, records[stage.GENERATED_SNAPSHOT],
                    'generated', generated_roots, {stage.SOLUTION_MODULE})
    extra = pairing.pair_extra({n: r for n, r in a_refs.items() if n not in mapping},
                               {n: r for n, r in b_refs.items() if n not in mapping.values()},
                               mapping)
    mapping.update(extra)
    need(set(raw_names) == set(b_refs),
         'An actual owned CI was not included in generated closed proof-reference export')
    inventory_ci = {r['actualName']: r['CI'] for r in raw_rows}
    for generated_name, row in b_refs.items():
        need(row == inventory_ci[generated_name],
             'Raw owned CI differs from actual proof closure: ' + generated_name)
    for source_name, actual_name in mapping.items():
        if source_name in a_types:
            a, b = a_types[source_name], b_types[actual_name]
            need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
                 and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                     == kernel.normalized_type(b)[1],
                 'Source/generated original full theorem type differs: ' + source_name)
        a, b = a_refs[source_name], b_refs[actual_name]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Source/generated closed proof CI type/Std3 differs: ' + source_name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need({mapping.get(x, x) for x in a[field]} == set(b[field]),
                 'Actual source/generated proof references differ: '
                 + source_name + ':' + field)
        for used in b['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in b_refs or used in BOUNDARY,
                     'Generated project proof dependency has no certified actual boundary: ' + used)
    return {'schema_version': 1,
            'artifact_kind': 'ap20-log-translation-count-four-original-AST-validation',
            'validated': True, 'Std3_only': True,
            'source_commit': prep['source_commit'],
            'original_AST_units': 4, 'original_source_lines': 42,
            'original_proof_suffixes_unchanged': True,
            'source_and_generated_full_types_equal': True,
            'source_and_generated_actual_proof_references_paired': True,
            'references_bitwise_equal_under_actual_mapping': True,
            'actual_private_helper_mappings': [
                {'sourceName': source_name, 'actualName': actual_name,
                 'owner': b_refs[actual_name]['owner']}
                for source_name, actual_name in zip(stage.HELPERS, private, strict=True)],
            'actual_automatic_CI_pairs': extra,
            'raw_owned_inventory_exact': True,
            'public_platform_boundary_names': [stage.TARGET],
            'published_data_definition_id': prep['published_data_definition_id'],
            'accepted_logdiv_theorem_id': prep['accepted_logdiv_theorem_id'],
            'solution_olean': stage.rel(olean),
            'solution_olean_sha256': stage.file_sha(olean),
            'preparation_sha256': stage.file_sha(stage.STAGE / 'preparation.json'),
            'source_types_sha256': stage.file_sha(stage.STAGE / stage.SOURCE_TYPES),
            'generated_types_sha256': stage.file_sha(stage.STAGE / stage.GENERATED_TYPES),
            'source_refs_sha256': stage.file_sha(stage.STAGE / stage.SOURCE_REFS),
            'generated_refs_sha256': stage.file_sha(stage.STAGE / stage.GENERATED_REFS),
            'owned_inventory_sha256': stage.file_sha(stage.STAGE / stage.INVENTORY),
            'preflights': {name: record['data'] for name, record in records.items()},
            'max_file_seconds': max(r['data']['seconds'] for r in records.values()),
            'compiler_manifest_hashes': {f'c{i}.json': stage.file_sha(stage.STAGE / f'c{i}.json')
                                         for i in range(1, 5)},
            'implementation_hashes': {stage.rel(SELF): stage.file_sha(SELF),
                                      stage.rel(stage.SELF): stage.file_sha(stage.SELF)},
            'submission_ready': False, 'proposal_status': 'Draft',
            'Lean_started_by_consumer': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    x = parser.add_mutually_exclusive_group(required=True)
    x.add_argument('--certify-existing', action='store_true')
    x.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    report = validate()
    path = stage.STAGE / stage.CERTIFICATE
    if args.certify_existing:
        path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    else:
        need(path.is_file() and read(path) == report,
             'Saved real four-context certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(path),
                      'sha256': stage.file_sha(path)}))


if __name__ == '__main__':
    main()

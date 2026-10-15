"""Derived strict certificate for the actual AP20 translation proof and CI inventory."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path

import stage_log_translation_count_node as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context
import certify_log_translation_count_node as preimage
import certify_log_translation_count_node_v3 as imported_boundary

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
BOUNDARY = ['OAI.PiExponent.translationTermCount',
            'OAI.PiExponent.tendsto_log_div_of_normalized_pow']
SOURCES = set(stage.SOURCE_MODULES)
CERTIFICATE = 'node-validation-v5.json'
AUDIT_SHA256 = '0b36aa2f337f1123db81399fe067ae638fe42cfb580e1fdfed5dc7a94471bd20'
EXTERNAL_INSTANCE_DELTAS = {
    'OAI.PiExponent.tendsto_translationTermCount_normalized': {
        'sourceOnly': ['NeZero.one', 'Real.instNontrivial'],
        'generatedOnly': ['NeZero.charZero_one'],
    },
    stage.TARGET: {
        'sourceOnly': ['NeZero.one', 'Real.instNontrivial',
                       'instMulZeroOneClassOfSemiring'],
        'generatedOnly': ['AddGroupWithOne.toAddMonoidWithOne',
                          'FloorRing.toFloorSemiring', 'FloorSemiring.instCharZero',
                          'NeZero.charZero_one', 'Real.instFloorRing', 'Real.instRing',
                          'Ring.toAddGroupWithOne', 'Ring.toSemiring'],
    },
}


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


def app_head_args(expr):
    args = []
    while isinstance(expr, list) and len(expr) == 3 and expr[0] == 'app':
        args.insert(0, expr[2])
        expr = expr[1]
    return expr, args


def certified_data_equation(row: dict, data_cert: dict):
    """Match the genuine lazy equation's complete RHS to the published full Def."""
    need(data_cert['primary_Def_full_types_values_equal'] is True,
         'Published RemainderData full Def equality is uncertified')
    provider = stage.TASK / 'verification/ap19/analytic-remainder-data/generated-full-ci.jsonl'
    need(provider.is_file(), 'Published full Def metadata is missing')
    provenance_key = 'verification/ap19/analytic-remainder-data/generated-full-ci.jsonl'
    witness = data_cert['source_automatic_preflight']['data']
    before = witness['manifest_input_hashes_before'][provenance_key]
    after = witness['manifest_input_hashes_after'][provenance_key]
    actual_hash = stage.file_sha(provider)
    need(before == after == {'expected_sha256': actual_hash,
                             'actual_sha256': actual_hash, 'matches': True},
         'Actual full Def metadata does not match certified historical hash')
    rows = [json.loads(line) for line in provider.read_text(encoding='utf-8').splitlines()]
    definitions = [r for r in rows if r.get('resolvedName') ==
                   'OAI.PiExponent.translationTermCount']
    need(len(definitions) == 1 and definitions[0]['envKind'] == 'def'
         and definitions[0]['closedType'] is True
         and definitions[0]['closedValue'] is True,
         'Exact published translationTermCount full Def is missing')
    definition = definitions[0]
    definition_type = definition['type']
    value = definition['value']
    equation_type = row['CI']['type']
    binders = [('forall', 'explicit', ['const', 'Nat', []]),
               ('forall', 'explicit', ['const', 'Real', []]),
               ('forall', 'explicit', ['const', 'Real', []])]
    for tag, style, domain in binders:
        need(equation_type[:3] == [tag, style, domain]
             and definition_type[:3] == [tag, style, domain]
             and value[:3] == ['lambda', style, domain],
             'Actual lazy equation binder scope differs from full source Def')
        equation_type, definition_type, value = (equation_type[3],
                                                  definition_type[3], value[3])
    head, args = app_head_args(equation_type)
    lhs_head, lhs_args = app_head_args(args[1]) if len(args) == 3 else (None, [])
    need(head == ['const', 'Eq', [['succ', ['zero']]]]
         and args[0] == ['const', 'Nat', []]
         and definition_type == ['const', 'Nat', []]
         and lhs_head == ['const', 'OAI.PiExponent.translationTermCount', []]
         and lhs_args == [['bvar', 2], ['bvar', 1], ['bvar', 0]]
         and args[2] == value,
         'Actual lazy equation is not exactly the published Def body at original arguments')
    return {'name': row['actualName'], 'full_def_metadata_sha256': stage.file_sha(provider),
            'published_definition_id': '04008248-130e-40ba-b6a3-df3e9b9df91b',
            'exact_binders_lhs_and_rhs_equal': True}


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
    audit_path = stage.STAGE / 'actual-ci-audit.json'
    need(stage.file_sha(audit_path) == AUDIT_SHA256,
         'One-pass actual all-CI audit preimage changed')
    audit = read(audit_path)
    need(audit['allFullTypesEqual'] is True and audit['allAxiomsEqual'] is True
         and audit['allProjectRefsEqual'] is True
         and audit['actualExtraPairingError'] is None
         and audit['sourceCINames'] == sorted(a_refs)
         and audit['generatedCINames'] == sorted(b_refs)
         and audit['rawOwnedNames'] == raw_names
         and audit['proofClosureOutsideRawOwned'] == [],
         'Actual complete all-CI audit differs')
    unused = sorted(set(raw_names) - set(b_refs))
    need(unused == audit['rawOwnedOutsideProofClosure'] and len(unused) == 8
         and unused[0] == 'OAI.PiExponent.translationTermCount.eq_1',
         'Actual unused owned closed-CI inventory differs')
    inventory_ci = {r['actualName']: r['CI'] for r in raw_rows}
    for generated_name, row in b_refs.items():
        need(row == inventory_ci[generated_name],
             'Raw owned CI differs from actual proof closure: ' + generated_name)
    unused_rows = {r['actualName']: r for r in raw_rows if r['actualName'] in unused}
    equation = certified_data_equation(unused_rows[unused[0]], data_cert)
    unused_proof_caches = []
    for name in unused[1:]:
        row = unused_rows[name]
        refs = row['CI']['allUsedConstants']
        need(row['privateUserName'] is not None
             and not any(x.startswith('OAI.') or
                         x.startswith('_private.') and '.OAI.' in x for x in refs)
             and row['CI']['closedType'] is True
             and row['CI']['closedValue'] is True
             and set(row['CI']['axioms']) <= STD3,
             'Unused actual proof cache is not a closed external-only Prop CI: ' + name)
        unused_proof_caches.append({'actualName': name,
                                    'full_CI': row['CI'],
                                    'unreferenced_by_four_proof_roots': True})
    finite_deltas = {}
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
            source_set = {mapping.get(x, x) for x in a[field]}
            generated_set = set(b[field])
            observed = {'sourceOnly': sorted(source_set - generated_set),
                        'generatedOnly': sorted(generated_set - source_set)}
            expected = (EXTERNAL_INSTANCE_DELTAS.get(source_name, {})
                        if field != 'typeRefs' else {})
            expected = {'sourceOnly': expected.get('sourceOnly', []),
                        'generatedOnly': expected.get('generatedOnly', [])}
            need(observed == expected and all(
                     not (x.startswith('OAI.') or
                          x.startswith('_private.') and '.OAI.' in x)
                     for x in observed['sourceOnly'] + observed['generatedOnly']),
                 'Actual proof refs exceed exact finite Mathlib instance delta: '
                 + source_name + ':' + field)
            if observed['sourceOnly'] or observed['generatedOnly']:
                finite_deltas.setdefault(source_name, {})[field] = observed
        for used in b['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in b_refs or used in BOUNDARY,
                     'Generated project proof dependency has no certified actual boundary: ' + used)
    data_path = stage.TASK / data_cert['original_emitted_provider_olean']
    logdiv_path = stage.TASK / logdiv['provider_olean']
    c1 = records[stage.TARGET_OUTPUT]
    c2 = records[stage.SOLUTION_OUTPUT]
    imported_refs = {
        'c1_published_data': imported_boundary.imported(
            c1, imported_boundary.DATA_MODULE, data_path,
            data_cert['original_emitted_provider_olean_sha256']),
        'c2_published_data': imported_boundary.imported(
            c2, imported_boundary.DATA_MODULE, data_path,
            data_cert['original_emitted_provider_olean_sha256']),
        'c2_accepted_logdiv': imported_boundary.imported(
            c2, imported_boundary.LOGDIV_MODULE, logdiv_path,
            logdiv['provider_olean_sha256']),
    }
    return {'schema_version': 1,
            'artifact_kind': 'ap20-log-translation-count-four-original-AST-validation-v5',
            'validated': True, 'Std3_only': True,
            'source_commit': prep['source_commit'],
            'original_AST_units': 4, 'original_source_lines': 42,
            'original_proof_suffixes_unchanged': True,
            'source_and_generated_full_types_equal': True,
            'source_and_generated_actual_proof_references_paired': True,
            'references_bitwise_equal_under_actual_mapping': False,
            'actual_external_instance_deltas': finite_deltas,
            'actual_unused_raw_closed_CIs': {
                'data_equation': equation, 'unreferenced_proof_caches': unused_proof_caches,
                'complete_raw_owner_inventory_sha256': stage.file_sha(stage.STAGE / stage.INVENTORY),
                'actual_all_CI_audit_sha256': AUDIT_SHA256},
            'actual_imported_certified_provider_oleans': imported_refs,
            'published_data_cert_sha256': stage.file_sha(stage.route.CERT),
            'accepted_logdiv_mirror_cert_sha256': stage.file_sha(stage.route.LOGDIV_CERT),
            'frozen_original_consumer_preimage_sha256': stage.file_sha(Path(preimage.__file__)),
            'frozen_v3_consumer_preimage_sha256': stage.file_sha(Path(imported_boundary.__file__)),
            'frozen_v4_consumer_preimage_sha256': stage.file_sha(stage.TASK / 'scripts/certify_log_translation_count_node_v4.py'),
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
                                      stage.rel(Path(preimage.__file__)): stage.file_sha(Path(preimage.__file__)),
                                      stage.rel(Path(imported_boundary.__file__)): stage.file_sha(Path(imported_boundary.__file__)),
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
    path = stage.STAGE / CERTIFICATE
    if args.certify_existing:
        path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    else:
        need(path.is_file() and read(path) == report,
             'Saved real four-context certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(path),
                      'sha256': stage.file_sha(path)}))


if __name__ == '__main__':
    main()

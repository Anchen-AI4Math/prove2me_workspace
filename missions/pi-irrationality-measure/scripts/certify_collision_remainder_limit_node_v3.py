"""Strict offline certificate for the actual AP20 collision-remainder proof contexts."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path

import stage_collision_remainder_limit_node_v2 as stage
import certify_full_row_minor_node as kernel
import certify_grouped_actual_mean_bounds_node as grouped
import validate_namespace_context_providers as context
import preflight_staged_module_windows_bounded as bounded_runner

SELF = Path(__file__).resolve()
read, sha, need, rel = stage.read, stage.sha, stage.need, stage.rel
CERTIFICATE = 'node-validation-v3.json'
SOURCE_AUTO = stage.V / 'ap19/analytic-remainder-auto-ci-source-v4/source-automatic-ci.json'
GENERATED_AUTO = stage.DATA_STAGE / 'actual-owned-CI-inventory.json'
EXPECTED_ACTUAL_AUTO = {
    'OAI.PiExponent.Collision.collisionRatio._proof_1',
    'OAI.PiExponent.Collision.collisionRemainder._proof_1',
}


def certified_data_automatic_CIs():
    certificate = read(stage.DATA_CERT)
    original = read(SOURCE_AUTO)
    generated = read(GENERATED_AUTO)
    pairs = certificate['actual_source_generated_closed_Prop_autoCI_pairs']
    names = {row['name'] for row in pairs}
    need(certificate['validated'] is True and certificate['Std3_only'] is True
         and sha(SOURCE_AUTO) == certificate['source_automatic_json_sha256']
         and sha(GENERATED_AUTO) == certificate['generated_owned_inventory_sha256']
         and names == EXPECTED_ACTUAL_AUTO and len(pairs) == len(names) == 2,
         'Actual previously certified RemainderData auto CI domain differs')
    source_rows = {row['name']: row for row in original['rawSourceAutomaticCIs']}
    generated_rows = {row['name']: row for row in generated['rawOwnedCIs']}
    need(set(source_rows) == names and names <= set(generated_rows),
         'Original/generated automatic CI evidence rows differ')
    for pair in pairs:
        name = pair['name']
        a, b = source_rows[name], generated_rows[name]
        need(a['actualOwner'] == pair['source_owner']
             and b['owner'] == pair['generated_owner']
             and a['levelParams'] == b['levelParams'] == pair['levelParams']
             and a['type'] == b['type']
             and a['typeRefs'] == b['typeRefs'] == pair['typeRefs']
             and a['valueRefs'] == b['valueRefs'] == pair['valueRefs']
             and a['axioms'] == b['axioms'] == pair['axioms'] == ['propext']
             and a['kind'] == b['kind'] == 'theorem'
             and a['closedType'] is b['closedType'] is True
             and a['closedValue'] is b['closedValue'] is True
             and a['isProp'] is b['isProp'] is pair['closed_Prop'] is True
             and a['value'] is None and b['value'] is not None
             and a['privateUserName'] is b['privateUserName'] is None
             and not any(ref.startswith('OAI.') or ref.startswith('_private.OAI.')
                         for ref in pair['typeRefs'] + pair['valueRefs']),
             'Exact original/generated closed Prop CI type/refs/owner/Std3 differs: ' + name)
        kernel.checked_expr(a['type'], set(a['levelParams']))
    return names, pairs


def written(path, record):
    ended = datetime.fromisoformat(record['data']['at_utc']).timestamp()
    need(path.is_file() and ended - record['data']['seconds'] - 2 <= path.stat().st_mtime <= ended + 2,
         'Kernel JSON was not written during its compiler invocation: ' + rel(path))
    return read(path)


def preflight(filename, spec):
    module = filename[:-5].replace('/', '.')
    result = context.record(stage.STAGE / filename, stage.STAGE / spec['manifest'],
                            spec['mode'], module, stage.STAGE)
    data = result['data']
    need(data['success'] is True and data['exit_code'] == 0 and data['timed_out'] is False
         and 0 < data['seconds'] <= 300 and data['timeout_seconds'] == 300
         and data['mode'] == spec['mode'] and 'emit_olean' not in data
         and data['runner'] == rel(Path(bounded_runner.__file__))
         and data['runner_sha256'] == sha(Path(bounded_runner.__file__))
         and data['cleanup_completed'] is True,
         'Actual bounded compiler result differs: ' + filename)
    if spec['mode'] == 'emit-olean':
        path = stage.V / 'staged-build/lib/lean' / Path(filename).with_suffix('.olean')
        need(data['output_olean'] == rel(path) and data['output_olean_sha256'] == sha(path),
             'Actual generated solution OLean differs')
    else:
        need(data['output_olean'] is None and data['output_olean_sha256'] is None,
             'Modecheck unexpectedly emitted OLean')
    return result


def types(filename, record, names):
    rows = written(stage.STAGE / filename, record)
    need(isinstance(rows, list) and len(rows) == len(names), 'TypeOnly domain differs')
    result = {}
    for row, name in zip(rows, names, strict=True):
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['name'] == name and row['value'] is None,
             'Theorem TypeOnly row differs: ' + name)
        kernel.checked_expr(row['type'], set(row['levelParams']))
        result[name] = row
    return result


def proofs(filename, record, side, roots, modules, boundary):
    doc = written(stage.STAGE / filename, record)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule', 'rootNames',
                     'boundaryNames', 'rows'}
         and doc['schemaVersion'] == 1 and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == sorted(boundary),
         'Actual proof-reference snapshot header differs')
    names = [row['name'] for row in doc['rows']]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual source or generated CI closure differs')
    result = {}
    for row in doc['rows']:
        module = row['owner']['module']
        need(module in modules, 'Proof CI owner outside exact source/generated module domain')
        result[row['name']] = kernel.evidence_row(row, name=row['name'], module=module, helper=True)
    return result


def validate():
    stage.check_only()
    certified_auto, certified_pairs = certified_data_automatic_CIs()
    prep = read(stage.STAGE / 'preparation.json')
    need(prep['proposal_status'] == 'Draft' and prep['validated'] is False
         and prep['source_line_count'] == 15 and len(prep['exact_source_units']) == 2
         and prep['original_proof_suffixes_unchanged'] is True,
         'Exact original source/proof preparation differs')
    records = {f: preflight(f, prep['files'][f]) for f in stage.FILES}
    solution_olean = stage.V / 'staged-build/lib/lean' / Path(stage.SOLUTION_OUTPUT).with_suffix('.olean')
    imported = kernel.imported_dep(records[stage.GENERATED_SNAPSHOT], stage.SOLUTION_MODULE)
    need(Path(imported['path']).resolve() == solution_olean.resolve()
         and imported['sha256_before'] == sha(solution_olean),
         'Generated snapshot did not import the actual closed solution OLean')
    child_olean = stage.TASK / read(stage.CHILD_CERT)['provider_olean']
    child_import = kernel.imported_dep(records[stage.SOLUTION_OUTPUT], stage.route.PARENT_MODULE)
    need(Path(child_import['path']).resolve() == child_olean.resolve()
         and child_import['sha256_before'] == sha(child_olean),
         'Closed solution did not import the actual accepted LogDiv mirror OLean')
    data_cert = read(stage.DATA_CERT)
    data_olean = stage.TASK / data_cert['original_emitted_provider_olean']
    need(sha(data_olean) == data_cert['original_emitted_provider_olean_sha256'],
         'Certified RemainderData provider OLean changed')
    for filename in [stage.TARGET_OUTPUT, stage.SOLUTION_OUTPUT]:
        imported_data = kernel.imported_dep(records[filename], stage.route.data.PLATFORM_MODULE)
        need(Path(imported_data['path']).resolve() == data_olean.resolve()
             and imported_data['sha256_before'] == sha(data_olean),
             'Actual comparator/solution did not import certified RemainderData OLean')
    boundary = set(prep['provider_boundary_names'])
    sroots = [stage.HELPER, stage.TARGET]
    groots = [stage.HELPER, 'solution']
    st = types(stage.SOURCE_TYPE_JSON, records[stage.SOURCE_SNAPSHOT], sroots)
    gt = types(stage.GENERATED_TYPE_JSON, records[stage.GENERATED_SNAPSHOT], groots)
    sr = proofs(stage.SOURCE_REFS_JSON, records[stage.SOURCE_SNAPSHOT], 'source', sroots,
                {stage.TARGET_MODULE, 'OAI.NumberTheory.PiExponent.Polynomials.SimplexLog'}, boundary)
    gr = proofs(stage.GENERATED_REFS_JSON, records[stage.GENERATED_SNAPSHOT], 'generated', groots,
                {stage.SOLUTION_MODULE}, boundary)
    mapping = {stage.HELPER: stage.HELPER, stage.TARGET: 'solution'}
    extra_s = {n: r for n, r in sr.items() if n not in mapping}
    extra_g = {n: r for n, r in gr.items() if n not in mapping.values()}
    mapping.update(grouped.pair_extra(extra_s, extra_g, mapping))
    for source_name, generated_name in mapping.items():
        a, b = sr[source_name], gr[generated_name]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping) == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Exact closed CI type/Std3 pair differs: ' + source_name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need({mapping.get(n, n) for n in a[field]} == set(b[field]),
                 'Actual proof references differ: ' + source_name + ':' + field)
    for source_name, generated_name in [(stage.HELPER, stage.HELPER), (stage.TARGET, 'solution')]:
        a, b = st[source_name], gt[generated_name]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping) == kernel.normalized_type(b)[1],
             'Original/generated TypeOnly theorem type differs: ' + source_name)
    inventory = written(stage.STAGE / stage.OWNED_JSON, records[stage.GENERATED_SNAPSHOT])
    need(set(inventory) == {'schemaVersion', 'probeMainModule', 'mirrorModule', 'rawOwnedNames', 'rawOwnedCIs'}
         and inventory['schemaVersion'] == 1 and inventory['probeMainModule'] == 'GeneratedSnapshot'
         and inventory['mirrorModule'] == stage.SOLUTION_MODULE
         and inventory['rawOwnedNames'] == sorted(gr)
         and [row['name'] for row in inventory['rawOwnedCIs']] == sorted(gr),
         'Actual full owned CI inventory includes an unpaired cache or unknown declaration')
    public_owned = []
    for row in inventory['rawOwnedCIs']:
        actual = gr[row['name']]
        need(row['kind'] == 'theorem' and row['closedType'] is True
             and row['closedValue'] is True and row['isProp'] is True
             and all(row[k] == actual[k] for k in ['owner', 'levelParams', 'type',
                 'typeRefs', 'valueRefs', 'allUsedConstants', 'axioms']),
             'Actual owned CI is not the certified closed proof row')
        if row['privateUserName'] is None:
            public_owned.append(row['name'])
    need(public_owned == sorted([stage.HELPER, 'solution']),
         'Generated module has an unexpected public proof interface')
    actual_unknown = {}
    for side, rows in [('source', sr), ('generated', gr)]:
        unknown = set()
        for row in rows.values():
            unknown.update(n for n in row['allUsedConstants']
                           if (n.startswith('OAI.') or n.startswith('_private.OAI.'))
                           and n not in rows and n not in boundary)
        need(unknown == certified_auto,
             'Actual project proof refs differ from the exact certified data auto CIs: ' + side)
        actual_unknown[side] = sorted(unknown)
    return {'schema_version': 1, 'artifact_kind': 'ap20-collision-remainder-limit-proof-validation',
            'validated': True, 'Std3_only': True, 'closed_global_solution': True,
            'original_AST_units': 2, 'original_source_lines': 15,
            'literal_original_proof_suffixes': True, 'source_and_generated_full_types_equal': True,
            'source_and_generated_actual_proof_references_paired': True,
            'references_bitwise_equal_under_actual_mapping': True,
            'actual_automatic_CI_pairs': mapping, 'raw_owned_inventory_exact': True,
            'actual_external_data_closed_Prop_CI_refs': actual_unknown,
            'actual_external_data_closed_Prop_CI_pairs': certified_pairs,
            'external_data_auto_source_json_sha256': sha(SOURCE_AUTO),
            'external_data_auto_generated_json_sha256': sha(GENERATED_AUTO),
            'external_data_cert_sha256': sha(stage.DATA_CERT),
            'frozen_v2_consumer_preimage_sha256': sha(stage.TASK / 'scripts/certify_collision_remainder_limit_node_v2.py'),
            'frozen_v2_failure_sha256': sha(stage.STAGE / 'certification-failure.json'),
            'public_platform_boundary_names': [stage.TARGET],
            'solution_olean': rel(solution_olean), 'solution_olean_sha256': sha(solution_olean),
            'preparation_sha256': sha(stage.STAGE / 'preparation.json'),
            'generated_json_sha256': {name: sha(stage.STAGE / name) for name in [stage.SOURCE_TYPE_JSON,
                stage.GENERATED_TYPE_JSON, stage.SOURCE_REFS_JSON, stage.GENERATED_REFS_JSON,
                stage.OWNED_JSON]},
            'preflights': {name: {'record': rel(stage.STAGE / (name + '.preflight.json')),
                'record_sha256': sha(stage.STAGE / (name + '.preflight.json')),
                'data': records[name]['data']} for name in stage.FILES},
            'implementation_hashes': {rel(SELF): sha(SELF), rel(stage.SELF): sha(stage.SELF)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certify-existing', action='store_true', required=True)
    args = parser.parse_args()
    if args.certify_existing:
        report = validate()
        output = stage.STAGE / CERTIFICATE
        raw = stage.encode(report)
        if output.exists():
            need(output.read_bytes() == raw, 'Refusing to replace existing certificate')
        else:
            output.write_bytes(raw)
        print(json.dumps({'certificate': rel(output), 'sha256': sha(output),
                          'validated': True}, ensure_ascii=False))


if __name__ == '__main__':
    main()

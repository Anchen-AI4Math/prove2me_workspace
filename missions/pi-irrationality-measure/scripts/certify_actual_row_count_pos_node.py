"""Certify actual AP21 contexts and the seven original closed proof CIs offline."""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import stage_actual_row_count_pos_node as stage
import certify_full_row_minor_node as kernel
import certify_selected_minor_clearing_bound_node as pairing
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def written(path: Path, record: dict):
    data = record['data']
    end = datetime.fromisoformat(data['at_utc']).timestamp()
    need(path.is_file() and end - data['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Actual kernel JSON not written in the compiler window: ' + stage.rel(path))
    return stage.read(path)


def types(path: Path, record: dict, roots: list[str]):
    rows = written(path, record)
    need(isinstance(rows, list) and [row.get('name') for row in rows] == roots,
         'Actual TypeOnly theorem roots differ')
    for row in rows:
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['value'] is None and isinstance(row['prettyType'], str)
             and bool(row['prettyType']),
             'Theorem TypeOnly null/value/schema differs: ' + row.get('name', '?'))
        kernel.checked_expr(row['type'], set(row['levelParams']))
    return {row['name']: row for row in rows}


def proofs(path: Path, record: dict, side: str,
           roots: list[str], owners: set[str]):
    doc = written(path, record)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
                      'rootNames', 'boundaryNames', 'rows'}
         and doc['schemaVersion'] == 1 and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source'
                                        else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == [],
         'Actual complete proof reference envelope differs')
    rows = doc['rows']
    names = [row['name'] for row in rows]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual complete proof CI domain/roots differ')
    for row in rows:
        owner = row['owner']['module']
        need(owner in owners and row['closedType'] is True
             and row['closedValue'] is True and set(row['axioms']) <= STD3,
             'Actual source/generated proof CI owner/closure/Std3 differs: ' + row['name'])
        kernel.evidence_row(row, name=row['name'], module=owner, helper=True)
    return {row['name']: row for row in rows}


def project(names):
    return sorted(x for x in names if x.startswith('OAI.') or
                  x.startswith('_private.') and '.OAI.' in x)


def actual_audit():
    """Export one complete finite difference ledger before strict certification."""
    inventory = stage.read(stage.STAGE / stage.INVENTORY)
    src = {row['name']: row for row in stage.read(stage.STAGE / stage.SOURCE_REFS)['rows']}
    gen = {row['name']: row for row in stage.read(stage.STAGE / stage.GENERATED_REFS)['rows']}
    route = stage.read(stage.ROUTE / 'source-route.json')
    mapping = dict(zip(route['helper_names'], inventory['actualPrivateHelpers'], strict=True))
    mapping[stage.TARGET] = 'solution'
    extra_error = None
    try:
        mapping.update(pairing.pair_extra({n: r for n, r in src.items() if n not in mapping},
                                          {n: r for n, r in gen.items() if n not in mapping.values()},
                                          mapping))
    except Exception as exc:
        extra_error = f'{type(exc).__name__}: {exc}'
    pairs = []
    for source_name, generated_name in mapping.items():
        if source_name not in src or generated_name not in gen:
            pairs.append({'source': source_name, 'generated': generated_name,
                          'missingActualRow': True})
            continue
        left, right = src[source_name], gen[generated_name]
        ltype, rtype = kernel.normalized_type(left), kernel.normalized_type(right)
        row = {'source': source_name, 'generated': generated_name,
               'fullTypeEqual': ltype[0] == rtype[0] and
                                kernel.rename_expr(ltype[1], mapping) == rtype[1],
               'axiomsEqual': left['axioms'] == right['axioms'],
               'sourceOwner': left['owner'], 'generatedOwner': right['owner'],
               'closedSourceValue': left['closedValue'],
               'closedGeneratedValue': right['closedValue']}
        for field in ('typeRefs', 'valueRefs', 'allUsedConstants'):
            a = {mapping.get(n, n) for n in left[field]}
            b = set(right[field])
            row[field] = {'equal': a == b, 'sourceOnly': sorted(a - b),
                          'generatedOnly': sorted(b - a),
                          'sourceProject': project(a),
                          'generatedProject': project(b)}
        pairs.append(row)
    return {'schema_version': 1,
            'artifact_kind': 'ap21-actual-row-count-all-actual-CI-read-only-audit',
            'sourceRootNames': stage.read(stage.STAGE / stage.SOURCE_REFS)['rootNames'],
            'generatedRootNames': stage.read(stage.STAGE / stage.GENERATED_REFS)['rootNames'],
            'sourceCINames': sorted(src), 'generatedCINames': sorted(gen),
            'rawOwnedNames': inventory['rawOwnedNames'],
            'rawOwnedOutsideProofClosure': sorted(set(inventory['rawOwnedNames']) - set(gen)),
            'proofClosureOutsideRawOwned': sorted(set(gen) - set(inventory['rawOwnedNames'])),
            'actualPrivateHelperMapping': mapping,
            'actualExtraPairingError': extra_error, 'pairs': pairs,
            'allFullTypesEqual': all(row.get('fullTypeEqual') is True for row in pairs),
            'allAxiomsEqual': all(row.get('axiomsEqual') is True for row in pairs),
            'allProjectRefsEqual': all(all(row[field]['sourceProject'] ==
                                          row[field]['generatedProject']
                                          for field in ('typeRefs', 'valueRefs', 'allUsedConstants'))
                                       for row in pairs if not row.get('missingActualRow')),
            'noLeanOrAPI': True}


def validate():
    stage.check_only()
    prep = stage.read(stage.STAGE / 'preparation.json')
    route = stage.read(stage.ROUTE / 'source-route.json')
    helpers = route['helper_names']
    need(prep['source_name'] == prep['platform_name'] == stage.TARGET
         and prep['platform_theorem_id'] == stage.TARGET_ID
         and prep['original_AST_count'] == 7 and prep['original_source_lines'] == 53
         and prep['original_proof_suffixes_unchanged'] is True
         and prep['six_helper_private_visibility_prefix_only'] is True
         and prep['target_global_solution_name_only_rewritten'] is True
         and prep['source_type_only_names'] == helpers + [stage.TARGET]
         and prep['actual_new_compiler_contexts'] == 3
         and prep['actual_reused_compiler_contexts'] == 1,
         'Frozen seven original AST/source/solution route differs')
    cert = stage.read(stage.DATA_CERT)
    published = stage.read(stage.DATA_PUBLISHED)
    closure = stage.read(stage.CLOSURE)
    target_rows = [r for r in closure['rows'] if r['name'] == stage.TARGET]
    need(cert['validated'] is True and cert['Std3_only'] is True
         and cert['provider_olean_sha256'] == stage.sha(stage.TASK / cert['provider_olean'])
         and published['definition_name'] ==
             'OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData'
         and published['last_publish_verdict']['body']['status'] == 'PUBLISHED'
         and published['target_readback']['body']['status'] == 'Definition'
         and closure['all_missing_data_domains_empty'] is True
         and len(target_rows) == 1 and target_rows[0]['missing_data_CIs'] == [],
         'Published full Def/Std3/type import closure differs')
    old = prep['reused_original_stub_context']
    old_record = context.record(stage.TASK / old['source'], stage.TASK / old['manifest'],
                                'emit-olean', stage.MODULE, stage.TASK / old['root'])
    old_data = old_record['data']
    need(old_data['success'] is True and old_data['exit_code'] == 0
         and old_data['timed_out'] is False and 0 < old_data['seconds'] <= 300
         and old_data['source_sha256_before'] == old_data['source_sha256_after'] ==
             stage.sha(stage.STAGE / stage.TARGET_OUTPUT)
         and old_data['output_olean_sha256'] == old['output_olean_sha256'] ==
             stage.sha(stage.TASK / old['output_olean'])
         and stage.sha(stage.TASK / old['preflight']) == old['preflight_sha256']
         and old['sorryAx_comparator_only'] is True,
         'Reused public Open comparator was not an actual bounded emitter')
    records = {stage.TARGET_OUTPUT: old_record}
    for i, (name, mode) in enumerate(zip(stage.FILES[1:], stage.MODES[1:], strict=True), 2):
        module = Path(name).with_suffix('').as_posix().replace('/', '.')
        record = context.record(stage.STAGE / name, stage.STAGE / f'c{i}.json',
                                mode, module, stage.STAGE)
        data = record['data']
        need(data['success'] is True and data['exit_code'] == 0
             and data['timed_out'] is False and 0 < data['seconds'] <= 300
             and data['timeout_seconds'] == 300 and data['mode'] == mode
             and data['runner'] == stage.rel(stage.RUNNER)
             and data['runner_sha256'] == stage.sha(stage.RUNNER)
             and data['legacy_runner_sha256'] == stage.sha(stage.LEGACY)
             and data['cleanup_completed'] is True,
             'Actual bounded AP21 compiler context differs: ' + name)
        if mode == 'modecheck':
            need(data['output_olean'] is None and data['output_olean_sha256'] is None,
                 'Metadata-only AP21 probe emitted OLean')
        records[name] = record
    solution_olean = stage.V / 'staged-build/lib/lean' / Path(stage.SOLUTION_OUTPUT).with_suffix('.olean')
    need(records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'] ==
         stage.sha(solution_olean), 'Actual global closed solution OLean differs')
    imported = kernel.imported_dep(records[stage.GENERATED_SNAPSHOT],
                                   stage.SOLUTION_MODULE)
    need(Path(imported['path']).resolve() == solution_olean.resolve()
         and imported['sha256_before'] == imported['sha256_after'] ==
             stage.sha(solution_olean),
         'Actual generated metadata imported a different solution OLean')
    inventory = written(stage.STAGE / stage.INVENTORY, records[stage.GENERATED_SNAPSHOT])
    need(set(inventory) == {'schemaVersion', 'probeMainModule', 'solutionModule',
                            'sourceHelpers', 'actualPrivateHelpers',
                            'publicPlatformTarget', 'rawOwnedNames', 'rawOwnedCIs'}
         and inventory['schemaVersion'] == 1
         and inventory['probeMainModule'] == 'GeneratedSnapshot'
         and inventory['solutionModule'] == stage.SOLUTION_MODULE
         and inventory['sourceHelpers'] == helpers
         and inventory['publicPlatformTarget'] == 'solution',
         'Actual raw owned CI inventory envelope differs')
    private = inventory['actualPrivateHelpers']
    generated_roots = private + ['solution']
    need(len(private) == 6 and len(set(private)) == 6
         and all(name.startswith('_private.') for name in private),
         'Six exact source helpers were not compiled as unique private CIs')
    mapping = dict(zip(helpers, private, strict=True))
    mapping[stage.TARGET] = 'solution'
    raw_names = inventory['rawOwnedNames']
    raw_rows = inventory['rawOwnedCIs']
    need(raw_names == sorted(set(raw_names))
         and [r['actualName'] for r in raw_rows] == raw_names
         and set(generated_roots) <= set(raw_names),
         'Actual complete owned CI names or roots differ')
    for row in raw_rows:
        need(row['kind'] == 'theorem' and row['isProp'] is True,
             'Actual owned CI is not a closed Prop theorem: ' + row['actualName'])
        kernel.evidence_row(row['CI'], name=row['actualName'],
                            module=stage.SOLUTION_MODULE, helper=True)
    for source_name, actual in zip(helpers, private, strict=True):
        row = next(r for r in raw_rows if r['actualName'] == actual)
        need(row['privateUserName'] == source_name,
             'Actual privateToUserName helper mapping differs: ' + source_name)
    source_roots = helpers + [stage.TARGET]
    source_types = types(stage.STAGE / stage.SOURCE_TYPES,
                         records[stage.SOURCE_SNAPSHOT], source_roots)
    generated_types = types(stage.STAGE / stage.GENERATED_TYPES,
                            records[stage.GENERATED_SNAPSHOT], generated_roots)
    source_refs = proofs(stage.STAGE / stage.SOURCE_REFS,
                         records[stage.SOURCE_SNAPSHOT], 'source', source_roots,
                         set(prep['source_modules']))
    generated_refs = proofs(stage.STAGE / stage.GENERATED_REFS,
                            records[stage.GENERATED_SNAPSHOT], 'generated',
                            generated_roots, {stage.SOLUTION_MODULE})
    extra = pairing.pair_extra(
        {n: r for n, r in source_refs.items() if n not in mapping},
        {n: r for n, r in generated_refs.items() if n not in mapping.values()}, mapping)
    mapping.update(extra)
    need(set(raw_names) == set(generated_refs),
         'Observed generated raw owned CI outside actual proof closure needs finite audit')
    owned = {r['actualName']: r['CI'] for r in raw_rows}
    for name, row in generated_refs.items():
        need(row == owned[name],
             'Raw ModuleIdx-owned CI differs from proof closure: ' + name)
    for source_name, generated_name in mapping.items():
        if source_name in source_types:
            a, b = source_types[source_name], generated_types[generated_name]
            atype, btype = kernel.normalized_type(a), kernel.normalized_type(b)
            need(atype[0] == btype[0] and
                 kernel.rename_expr(atype[1], mapping) == btype[1],
                 'Original complete source/generated theorem TypeOnly differs: ' + source_name)
        a, b = source_refs[source_name], generated_refs[generated_name]
        atype, btype = kernel.normalized_type(a), kernel.normalized_type(b)
        need(atype[0] == btype[0]
             and kernel.rename_expr(atype[1], mapping) == btype[1]
             and a['axioms'] == b['axioms'],
             'Original full proof CI type/Std3 differs: ' + source_name)
        for field in ('typeRefs', 'valueRefs', 'allUsedConstants'):
            need({mapping.get(n, n) for n in a[field]} == set(b[field]),
                 'Actual source/generated complete proof reference domain differs: '
                 + source_name + ':' + field)
        for used in b['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in generated_refs or
                     used in target_rows[0]['source_graph_type_and_Def_value_dependencies'],
                     'Unknown actual project proof dependency: ' + used)
    return {'schema_version': 1,
            'artifact_kind': 'ap21-actual-row-count-seven-original-AST-closed-validation',
            'validated': True, 'Std3_only': True,
            'source_commit': prep['source_commit'],
            'original_AST_count': 7, 'original_source_lines': 53,
            'original_proof_suffixes_unchanged': True,
            'source_and_generated_full_types_equal': True,
            'source_and_generated_actual_proof_references_paired': True,
            'references_bitwise_equal_under_actual_mapping': True,
            'actual_private_helper_mappings': [
                {'sourceName': name, 'actualName': actual, 'owner': generated_refs[actual]['owner']}
                for name, actual in zip(helpers, private, strict=True)],
            'actual_automatic_CI_pairs': extra,
            'raw_owned_inventory_exact': True,
            'public_platform_boundary_names': [stage.TARGET],
            'platform_theorem_id': stage.TARGET_ID,
            'platform_wire_sha256': prep['platform_wire_sha256'],
            'published_data_certificate_sha256': stage.sha(stage.DATA_CERT),
            'published_data_record_sha256': stage.sha(stage.DATA_PUBLISHED),
            'actual_source_type_import_closure_sha256': stage.sha(stage.CLOSURE),
            'reused_stub_sorryAx_comparator_only': True,
            'reused_stub_olean_sha256': old['output_olean_sha256'],
            'solution_olean': stage.rel(solution_olean),
            'solution_olean_sha256': stage.sha(solution_olean),
            'source_types_sha256': stage.sha(stage.STAGE / stage.SOURCE_TYPES),
            'generated_types_sha256': stage.sha(stage.STAGE / stage.GENERATED_TYPES),
            'source_refs_sha256': stage.sha(stage.STAGE / stage.SOURCE_REFS),
            'generated_refs_sha256': stage.sha(stage.STAGE / stage.GENERATED_REFS),
            'owned_inventory_sha256': stage.sha(stage.STAGE / stage.INVENTORY),
            'preflights': {name: r['data'] for name, r in records.items()},
            'max_file_seconds': max(r['data']['seconds'] for r in records.values()),
            'compiler_manifest_hashes': {f'c{i}.json': stage.sha(stage.STAGE / f'c{i}.json')
                                         for i in (2, 3, 4)},
            'implementation_hashes': {stage.rel(SELF): stage.sha(SELF),
                                      stage.rel(stage.SELF): stage.sha(stage.SELF)},
            'proposal_status': 'Draft', 'submission_ready': False,
            'Lean_started_by_consumer': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--audit-existing', action='store_true')
    mode.add_argument('--certify-existing', action='store_true')
    mode.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.audit_existing:
        report = actual_audit()
        path = stage.STAGE / 'actual-ci-audit.json'
        path.write_bytes(stage.encode(report))
        print(json.dumps({'audit': stage.rel(path), 'pairs': len(report['pairs']),
                          'allFullTypesEqual': report['allFullTypesEqual'],
                          'allProjectRefsEqual': report['allProjectRefsEqual'],
                          'actualExtraPairingError': report['actualExtraPairingError']}))
        return
    report = validate()
    path = stage.STAGE / stage.CERTIFICATE
    if args.certify_existing:
        path.write_bytes(stage.encode(report))
    else:
        need(path.is_file() and path.read_bytes() == stage.encode(report),
             'Saved strict AP21 certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(path),
                      'sha256': stage.sha(path),
                      'max_file_seconds': report['max_file_seconds']}))


if __name__ == '__main__':
    main()

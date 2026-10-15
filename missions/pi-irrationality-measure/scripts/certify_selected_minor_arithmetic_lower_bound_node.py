"""Strict pure replay of the four actual AP16 lower-bound compiler contexts."""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import stage_selected_minor_arithmetic_lower_bound_node as stage
import certify_selected_minor_clearing_bound_node as clearing_cert
import certify_selected_minor_clearing_child_mirror_validation_v5 as mirror_cert
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
TASK, STAGE = stage.TASK, stage.STAGE
read, sha, need, rel = stage.read, stage.sha, stage.need, stage.rel


def written(path, pf):
    end = datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(path.is_file() and end - pf['data']['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Actual JSON was not written in this compiler interval: ' + rel(path))
    return read(path)


def preflight(filename, prep):
    spec = prep['files'][filename]
    module = filename[:-5].replace('/', '.')
    record = context.record(STAGE / filename, STAGE / spec['manifest'],
                            spec['mode'], module, STAGE)
    d = record['data']
    need(d['success'] is True and d['exit_code'] == 0 and d['timed_out'] is False
         and 0 < d['seconds'] <= 300 and d['timeout_seconds'] == 300
         and d['mode'] == spec['mode'] and 'emit_olean' not in d
         and d.get('runner') == rel(stage.RUNNER)
         and d.get('runner_sha256') == sha(stage.RUNNER)
         and d.get('legacy_runner_sha256') == sha(stage.LEGACY_RUNNER)
         and d.get('cleanup_completed') is True,
         'Bounded actual compiler context differs: ' + filename)
    if spec['mode'] == 'emit-olean':
        olean = stage.clearing.base.runner.STAGED_LIB / Path(filename).with_suffix('.olean')
        need(d['output_olean'] == rel(olean) and d['output_olean_sha256'] == sha(olean),
             'Actual solution OLean differs')
    else:
        need(d['output_olean'] is None and d['output_olean_sha256'] is None,
             'A non-emitter unexpectedly emitted OLean')
    return record


def types(filename, pf, names):
    rows = written(STAGE / filename, pf)
    need(isinstance(rows, list) and len(rows) == len(names),
         'TypeOnly CI domain differs')
    out = {}
    for row, name in zip(rows, names, strict=True):
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['name'] == name and row['value'] is None
             and isinstance(row['prettyType'], str) and bool(row['prettyType']),
             'Actual theorem TypeOnly CI differs: ' + name)
        kernel.checked_expr(row['type'], set(row['levelParams']))
        kernel.normalized_type(row)
        out[name] = row
    return out


def proofs(filename, pf, side, roots, modules, boundary):
    doc = written(STAGE / filename, pf)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
         'rootNames', 'boundaryNames', 'rows'} and doc['schemaVersion'] == 1
         and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == sorted(boundary),
         'Actual proof-reference envelope differs')
    names = [row['name'] for row in doc['rows']]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual proof CI domain omits or duplicates roots')
    out = {}
    for row in doc['rows']:
        owner = row['owner']['module']
        need(owner in modules, 'Proof CI owner outside actual source/generated modules: ' + owner)
        out[row['name']] = kernel.evidence_row(row, name=row['name'],
                                                module=owner, helper=True)
    return out


def validate():
    stage.check_only()
    prep = read(STAGE / 'preparation.json')
    need(prep['validated'] is False and prep['submission_ready'] is False
         and prep['proposal_status'] == 'Draft'
         and prep['global_solution_preserves_literal_source_proof'] is True
         and prep['all_helper_proofs_literal_original'] is True
         and prep['existing_port_adaptations'] == []
         and prep['original_proof_AST_units'] == 22
         and prep['original_source_lines'] == 247,
         'Original proof preparation differs')
    graph, closure, provided, rows, commands, _, lcm = stage.route.source_units()
    records = {f: preflight(f, prep) for f in stage.FILES}
    boundary = set(prep['provider_subtracted_names'])
    need(boundary == closure & provided and stage.clearing.TARGET in boundary
         and stage.route.PUBLISHED_CONSTANT_POS in boundary,
         'Actual AP15/lcm theorem boundary differs')
    source = types(stage.SOURCE_TYPE_JSON, records[stage.SOURCE_SNAPSHOT],
                   prep['source_type_only_names'])
    generated = types(stage.GENERATED_TYPE_JSON, records[stage.GENERATED_SNAPSHOT],
                      prep['generated_type_only_names'])
    source_modules = list(stage.HELPER_NAMES)
    generated_modules = [stage.SOLUTION_MODULE, stage.mirror.MODULE,
                         stage.shifted.DEFINITION_MODULE,
                         stage.clearing.scales.PLATFORM_MODULE]
    generated_modules += [stage.clearing.base.ap10.config(k)['platform_module']
                          for k in stage.clearing.base.ap10.CONFIGS]
    generated_modules += [stage.clearing.base.ap9.config(k)['platform_module']
                          for k in stage.clearing.base.ap9.CONFIGS]
    source_refs = proofs(stage.SOURCE_REFS_JSON, records[stage.SOURCE_SNAPSHOT],
                         'source', prep['source_type_only_names'], source_modules, boundary)
    generated_refs = proofs(stage.GENERATED_REFS_JSON, records[stage.GENERATED_SNAPSHOT],
                            'generated', prep['generated_type_only_names'],
                            generated_modules, boundary)
    for row in rows:
        need(source_refs[row['name']]['owner']['module'] == row['module'],
             'Actual source theorem owner differs: ' + row['name'])
    for name in prep['generated_type_only_names']:
        need(generated_refs[name]['owner']['module'] == stage.SOLUTION_MODULE,
             'Generated theorem does not belong to global solution module: ' + name)
    public_map = {n: n for n in prep['inline_helper_names']}
    public_map[stage.TARGET] = 'solution'
    source_extra = {n: r for n, r in source_refs.items() if n not in public_map}
    generated_extra = {n: r for n, r in generated_refs.items()
                       if n not in public_map.values()}
    need(all(n not in graph or graph[n]['isPrivate'] for n in source_extra),
         'Uncertified public source CI lacks original AST')
    mapping = clearing_cert.pair_extra(source_extra, generated_extra, public_map)
    for name, mapped in public_map.items():
        a, b = source[name], generated[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1],
             'Original/generated full theorem type differs: ' + name)
    for name, mapped in mapping.items():
        a, b = source_refs[name], generated_refs[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Paired actual proof CI complete type/Std3 differs: ' + name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need(sorted({mapping.get(x, x) for x in a[field]}) == b[field],
                 'Actual paired proof references differ: ' + name + ':' + field)
    for proof_rows in [source_refs, generated_refs]:
        for row in proof_rows.values():
            for name in row['allUsedConstants']:
                if name in graph or name.startswith('OAI.') or name.startswith('_private.OAI.'):
                    need(name in proof_rows or name in boundary,
                         'Uncovered actual project proof dependency: ' + name)
    parent_cert = clearing_cert.validate()
    parent_path = stage.clearing.STAGE / stage.clearing.CERTIFICATE
    mirror = mirror_cert.validate()
    mirror_path = stage.mirror_validation.STAGE / stage.mirror_validation.CERTIFICATE
    need(parent_path.read_bytes() == stage.encode(parent_cert)
         and mirror_path.read_bytes() == stage.encode(mirror)
         and mirror['validated'] is True and mirror['Std3_only'] is True
         and mirror['public_platform_boundary_names'] == [stage.clearing.TARGET]
         and mirror['artifact_kind'] == 'ap16-private-clearing-child-mirror-validation-v5'
         and mirror['derived_ledger_sha256'] == sha(stage.mirror_validation.LEDGER)
         and mirror['frozen_v4_consumer_sha256'] == sha(stage.mirror_validation.FROZEN_V4_CONSUMER)
         and mirror['actual_closed_automatic_data_helper_pair']['name'] ==
             stage.mirror_validation.AUTO_HELPER
         and mirror['actual_closed_automatic_data_helper_pair']['full_type_axioms_and_all_actual_refs_equal'] is True
         and mirror['platform_boundary_certification_pending'] is False
         and mirror['accepted_parent_Proved'] is True
         and mirror['public_platform_boundary_remains_original_target_only'] is True
         and mirror['provider_source_sha256'] == sha(stage.mirror.EMITTER_STAGE / stage.mirror.OUTPUT)
         and mirror['provider_olean_sha256'] == stage.mirror.EXPECTED_OLEAN
         and mirror['bounded_runner_sha256'] == sha(stage.RUNNER),
         'Actual closed clearing parent/private mirror certificates differ')
    dep = kernel.imported_dep(records[stage.SOLUTION_OUTPUT], stage.mirror.MODULE)
    olean = TASK / mirror['provider_olean']
    need(Path(dep['path']).resolve() == olean.resolve()
         and dep['sha256_before'] == sha(olean) == mirror['provider_olean_sha256'],
         'Actual imported AP15 private mirror OLean differs')
    wire = STAGE / stage.TARGET_OUTPUT
    need(wire.read_bytes() == (prep['preamble'] + prep['formal_statement']).encode()
         and wire.read_bytes() == (STAGE / 'wire-theorem-source.lean').read_bytes(),
         'Exact platform comparator wire differs')
    solution = STAGE / stage.SOLUTION_OUTPUT
    need(b'theorem solution ' in solution.read_bytes() and b'sorry' not in solution.read_bytes(),
         'Global proof is missing or contains sorry')
    return {'schema_version': 1,
            'artifact_kind': 'ap16-selected-minor-arithmetic-lower-bound-validation',
            'source_commit': stage.COMMIT, 'source_name': stage.TARGET,
            'platform_name': stage.PLATFORM_NAME, 'source_module': stage.TARGET_MODULE,
            'source_byte_range': stage.route.TARGET_SOURCE_RANGE,
            'solution_module': stage.SOLUTION_MODULE,
            'solution_source_sha256': sha(solution),
            'solution_olean': records[stage.SOLUTION_OUTPUT]['data']['output_olean'],
            'solution_olean_sha256': records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],
            'preparation_sha256': sha(STAGE / 'preparation.json'),
            'target_wire_sha256': sha(wire), 'preflights': records,
            'actual_closed_AP15_mirror_certificate': rel(mirror_path),
            'actual_closed_AP15_mirror_certificate_sha256': sha(mirror_path),
            'actual_accepted_AP15_publication': prep['required_Accepted_Proved_AP15_publication'],
            'actual_published_lcmConstant_pos': lcm,
            'inline_helper_names': prep['inline_helper_names'],
            'all_helpers_literal_original': True, 'existing_port_adaptations': [],
            'source_and_generated_types_equal': True,
            'source_and_generated_theorem_values_null': True,
            'source_and_generated_actual_proof_references_equal': True,
            'actual_automatic_CI_pairs': [[n, m] for n, m in mapping.items()
                                           if n not in public_map],
            'graph_closure_names': sorted(closure),
            'axioms': {side: {n: r['axioms'] for n, r in proof_rows.items()}
                       for side, proof_rows in [('source', source_refs),
                                                ('generated', generated_refs)]},
            'Std3_only': True,
            'json_sha256': {f: sha(STAGE / f) for f in [stage.SOURCE_TYPE_JSON,
                 stage.GENERATED_TYPE_JSON, stage.SOURCE_REFS_JSON, stage.GENERATED_REFS_JSON]},
            'implementation_hashes': {rel(f): sha(f) for f in [SELF, stage.SELF,
                 stage.route.SELF, Path(kernel.__file__), Path(context.__file__)]},
            'max_file_seconds': max(x['data']['seconds'] for x in records.values()),
            'validated': True, 'submission_ready': False, 'proposal_status': 'Draft',
            'Lean_started_by_consumer': False, 'API_used': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing', action='store_true')
    g.add_argument('--check-only', action='store_true')
    a = p.parse_args()
    result = validate()
    path = STAGE / stage.CERTIFICATE
    raw = stage.encode(result)
    if path.exists():
        need(path.read_bytes() == raw, 'Existing immutable certificate differs')
    elif a.certify_existing:
        path.write_bytes(raw)
    print(json.dumps({'certificate': rel(path),
        'certificate_sha256': sha(path) if path.exists() else None,
        'validated': True, 'Std3_only': True,
        'max_file_seconds': result['max_file_seconds'],
        'Lean_started_by_consumer': False, 'API_used': False},
        ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()

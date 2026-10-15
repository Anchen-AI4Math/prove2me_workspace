"""Strict pure replay of four actual AP15 selected-minor proof preflights."""
from __future__ import annotations

import argparse
from datetime import datetime
from itertools import permutations
import json
from pathlib import Path

import stage_selected_minor_clearing_bound_node as stage
import certify_scales_costs_data_existing as scales_cert
import certify_entry_gaussian_child_mirror as child_cert
import certify_entry_gaussian_node as entry_cert
import certify_full_row_minor_node as kernel
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
TASK, STAGE = stage.TASK, stage.STAGE
read, sha, need, rel = stage.read, stage.sha, stage.need, stage.rel


def written(path, pf):
    end = datetime.fromisoformat(pf['data']['at_utc']).timestamp()
    need(path.is_file() and end - pf['data']['seconds'] - 2 <= path.stat().st_mtime <= end + 2,
         'Actual snapshot was not written during compiler interval: ' + rel(path))
    return read(path)


def preflight(filename, prep):
    spec = prep['files'][filename]
    module = filename[:-5].replace('/', '.')
    record = context.record(STAGE / filename, STAGE / spec['manifest'],
                            spec['mode'], module, STAGE)
    d = record['data']
    need(d['success'] is True and d['exit_code'] == 0 and d['timed_out'] is False
         and 0 < d['seconds'] <= 300 and d['timeout_seconds'] == 300
         and d['mode'] == spec['mode'] and 'emit_olean' not in d,
         'Bounded actual compiler record differs: ' + filename)
    if spec['mode'] == 'emit-olean':
        olean = stage.base.runner.STAGED_LIB / Path(filename).with_suffix('.olean')
        need(d['output_olean'] == rel(olean) and d['output_olean_sha256'] == sha(olean),
             'Actual emitted global solution OLean differs')
    else:
        need(d['output_olean'] is None and d['output_olean_sha256'] is None,
             'Non-emitter created OLean')
    return record


def type_rows(filename, pf, names):
    rows = written(STAGE / filename, pf)
    need(isinstance(rows, list) and len(rows) == len(names), 'TypeOnly CI domain differs')
    result = {}
    for row, name in zip(rows, names, strict=True):
        need(set(row) == {'name', 'levelParams', 'type', 'value', 'prettyType'}
             and row['name'] == name and row['value'] is None
             and isinstance(row['prettyType'], str) and bool(row['prettyType']),
             'Expected exact TypeOnly theorem CI: ' + name)
        kernel.checked_expr(row['type'], set(row['levelParams']))
        kernel.normalized_type(row)
        result[name] = row
    return result


def evidence(row, owner, side):
    if owner not in ['SourceSnapshot', 'GeneratedSnapshot']:
        return kernel.evidence_row(row, name=row['name'], module=owner, helper=True)
    expected = 'SourceSnapshot' if side == 'source' else 'GeneratedSnapshot'
    need(owner == expected and row['owner'] == {'kind': 'OwnModule',
         'moduleIndex': None, 'module': expected},
         'Actual lazy equation owner differs')
    need(set(row) == {'name', 'levelParams', 'closedType', 'closedValue',
         'typeRefs', 'valueRefs', 'allUsedConstants', 'axioms', 'owner', 'type'}
         and row['closedType'] is True and row['closedValue'] is True,
         'Own lazy equation CI schema or closedness differs')
    kernel.checked_expr(row['type'], set(row['levelParams']))
    kernel.normalized_type(row)
    for key in ['typeRefs', 'valueRefs', 'allUsedConstants', 'axioms']:
        need(row[key] == sorted(set(row[key]))
             and all(isinstance(x, str) for x in row[key]),
             'Own lazy equation CI refs malformed')
    need(row['allUsedConstants'] == sorted(set(row['typeRefs'] + row['valueRefs']))
         and kernel.refs(row['type']) == row['typeRefs']
         and set(row['axioms']) <= STD3,
         'Own lazy equation actual refs / Std3 differ')
    return row


def proof_rows(filename, pf, side, roots, modules, boundary):
    doc = written(STAGE / filename, pf)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
         'rootNames', 'boundaryNames', 'rows'} and doc['schemaVersion'] == 1
         and doc['side'] == side
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
         and doc['rootNames'] == roots and doc['boundaryNames'] == sorted(boundary),
         'Actual proof-reference envelope differs')
    names = [r['name'] for r in doc['rows']]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual proof CI domain omits or duplicates roots')
    rows = {}
    for row in doc['rows']:
        owner = row['owner']['module']
        need(owner in modules, 'Actual proof CI owner outside exact source/generated domain: ' + owner)
        rows[row['name']] = evidence(row, owner, side)
    return rows


def equation_pairs(records, source, generated, source_refs, generated_refs):
    pairs = []
    for index, name in enumerate(stage.EQUATIONS, 1):
        docs = []
        for side, types, refs in [('source', source, source_refs),
                                  ('generated', generated, generated_refs)]:
            primary, module, filename = stage.equation_specs(side)[index - 1]
            pf = records[stage.SOURCE_SNAPSHOT if side == 'source' else stage.GENERATED_SNAPSHOT]
            d = written(STAGE / filename, pf)
            need(set(d) == {'side', 'expectedModule', 'primaryBinding',
                 'getEqnsForReturnedSome', 'actualEquationNames', 'equations',
                 'unfolding', 'probeMainModule', 'theoremProofValuesExported'}
                 and d['side'] == side and d['expectedModule'] == module
                 and d['probeMainModule'] == ('SourceSnapshot' if side == 'source' else 'GeneratedSnapshot')
                 and d['getEqnsForReturnedSome'] is True
                 and d['actualEquationNames'] == [name]
                 and d['theoremProofValuesExported'] is False
                 and len(d['equations']) == 1,
                 'Official equation API result differs: ' + name)
            pr = d['primaryBinding']
            need(set(pr) == {'actualName', 'userName', 'levelParams', 'kind',
                 'type', 'value', 'owner', 'axioms'}
                 and pr['actualName'] == pr['userName'] == primary
                 and pr['kind'] == 'def' and pr['value'] is not None
                 and set(pr['owner']) == {'kind', 'index', 'module'}
                 and pr['owner']['kind'] == 'ImportedModule'
                 and pr['owner']['module'] == module
                 and type(pr['owner']['index']) is int and pr['owner']['index'] >= 0,
                 'Official equation primary full Def/owner differs')
            kernel.checked_expr(pr['type'], set(pr['levelParams']))
            kernel.checked_expr(pr['value'], set(pr['levelParams']))
            need(len(pr['axioms']) == len(set(pr['axioms']))
                 and set(pr['axioms']) <= STD3,
                 'Primary Def axioms exceed Std3')
            eq = d['equations'][0]
            need(set(eq) == {'getter', 'inversePrimary', 'CI'}
                 and eq['getter'] == 'Lean.Meta.getEqnsFor?'
                 and eq['inversePrimary'] == primary,
                 'Official equation inverse primary differs')
            ci = eq['CI']
            need(set(ci) == set(pr) and ci['actualName'] == ci['userName'] == name
                 and ci['kind'] == 'theorem' and ci['value'] is None
                 and sorted(ci['axioms']) == refs[name]['axioms']
                 and kernel.normalized_type(ci) == kernel.normalized_type(types[name]),
                 'Official equation CI type/Std3 differs')
            ro = refs[name]['owner']
            need(ci['owner']['kind'] == ro['kind']
                 and ci['owner']['module'] == ro['module'],
                 'Official equation CI actual owner differs')
            if d['unfolding'] is not None:
                u = d['unfolding']
                need(set(u) == {'getter', 'CI'}
                     and u['getter'] == 'Lean.Meta.getUnfoldEqnFor?',
                     'Unexpected unfolding equation getter')
                uc = u['CI']
                need(set(uc) == set(pr) and uc['kind'] == 'theorem'
                     and uc['actualName'] == uc['userName'] and uc['value'] is None
                     and set(uc['axioms']) <= STD3
                     and uc['owner']['module'] in [module, d['probeMainModule']],
                     'Actual unfolding equation CI differs')
                kernel.checked_expr(uc['type'], set(uc['levelParams']))
            docs.append(d)
        a, b = docs
        pa, pb = a['primaryBinding'], b['primaryBinding']
        need(pa['levelParams'] == pb['levelParams']
             and pa['type'] == pb['type'] and pa['value'] == pb['value']
             and sorted(pa['axioms']) == sorted(pb['axioms']),
             'Original/generated primary complete Def type/value/Std3 differs')
        need((a['unfolding'] is None) == (b['unfolding'] is None),
             'Official unfolding API result differs')
        if a['unfolding'] is not None:
            ua, ub = a['unfolding']['CI'], b['unfolding']['CI']
            need(ua['actualName'] == ub['actualName']
                 and kernel.normalized_type(ua) == kernel.normalized_type(ub)
                 and sorted(ua['axioms']) == sorted(ub['axioms']),
                 'Official unfolding CI type/Std3 differs')
        pairs.append({'primary': pa['actualName'], 'equation': name,
                      'getter': 'Lean.Meta.getEqnsFor?',
                      'inverse_getter': 'Lean.Meta.isEqnThm?',
                      'actual_primary_definition_values_equal': True,
                      'equation_types_and_Std3_equal': True,
                      'source_owner': source_refs[name]['owner'],
                      'generated_owner': generated_refs[name]['owner'],
                      'json_sha256': {side + '-equation-' + str(index) + '.json':
                                      sha(STAGE / (side + '-equation-' + str(index) + '.json'))
                                      for side in ['source', 'generated']}})
    return pairs


def pair_extra(source, generated, public_map):
    need(len(source) == len(generated) and len(source) <= 9,
         'Genuine automatic CI domain differs or needs bounded pairing audit')
    left = [source[n] for n in sorted(source)]
    right = [generated[n] for n in sorted(generated)]
    matches = []
    for perm in permutations(right):
        mapping = public_map | {a['name']: b['name']
                                for a, b in zip(left, perm, strict=True)}
        if all(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
               and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                   == kernel.normalized_type(b)[1]
               for a, b in zip(left, perm, strict=True)):
            matches.append(mapping)
        need(len(matches) <= 1, 'Automatic CI types do not give a unique genuine pairing')
    need(len(matches) == 1, 'Automatic CI full types fail to pair')
    return matches[0]


def prerequisite(records, key, result, path, module):
    need(path.is_file() and path.read_bytes() == stage.encode(result)
         and result['validated'] is True and result['Std3_only'] is True,
         'Actual prerequisite certificate does not replay exactly: ' + key)
    olean = TASK / result['provider_olean']
    dep = kernel.imported_dep(records[stage.SOLUTION_OUTPUT], module)
    need(Path(dep['path']).resolve() == olean.resolve()
         and dep['sha256_before'] == sha(olean) == result['provider_olean_sha256'],
         'Actual prerequisite OLean differs: ' + key)
    return {'certificate': rel(path), 'certificate_sha256': sha(path),
            'olean': rel(olean), 'olean_sha256': sha(olean), 'module': module}


def validate():
    stage.check_only()
    prep = read(STAGE / 'preparation.json')
    need(prep['validated'] is False and prep['submission_ready'] is False
         and prep['proposal_status'] == 'Draft'
         and prep['global_solution_preserves_literal_source_proof'] is True,
         'Preparation proof semantics differ')
    graph, closure, provided, units, _, _ = stage.authority()
    records = {f: preflight(f, prep) for f in stage.FILES}
    source = type_rows(stage.SOURCE_TYPE_JSON, records[stage.SOURCE_SNAPSHOT],
                       prep['source_type_only_names'])
    generated = type_rows(stage.GENERATED_TYPE_JSON, records[stage.GENERATED_SNAPSHOT],
                          prep['generated_type_only_names'])
    source_proofs = proof_rows(stage.SOURCE_REFS_JSON,
        records[stage.SOURCE_SNAPSHOT], 'source', prep['source_type_only_names'],
        list(stage.HELPER_NAMES) + ['SourceSnapshot'],
        set(prep['provider_subtracted_names']))
    generated_proofs = proof_rows(stage.GENERATED_REFS_JSON,
        records[stage.GENERATED_SNAPSHOT], 'generated', prep['generated_type_only_names'],
        [stage.SOLUTION_MODULE, stage.scales.PLATFORM_MODULE, stage.child.MODULE,
         stage.base.ap10.config('interpolation')['platform_module'],
         stage.base.ap10.config('arithmetic')['platform_module'],
         stage.base.ap10.config('determinant')['platform_module'],
         'GeneratedSnapshot'], set(prep['provider_subtracted_names']))
    for row in units:
        need(source_proofs[row['name']]['owner']['module'] == row['module'],
             'Source public theorem owner differs: ' + row['name'])
    public_map = {n: n for n in prep['inline_helper_names'] + stage.EQUATIONS}
    public_map[stage.TARGET] = 'solution'
    source_extra = {n: r for n, r in source_proofs.items() if n not in public_map}
    generated_extra = {n: r for n, r in generated_proofs.items()
                       if n not in public_map.values()}
    need(all(n not in graph or graph[n]['isPrivate'] for n in source_extra),
         'A new public source dependency lacks source AST provenance')
    mapping = pair_extra(source_extra, generated_extra, public_map)
    for name, mapped in public_map.items():
        a, b = source[name], generated[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1],
             'Exact original/generated theorem full type differs: ' + name)
    for name, mapped in mapping.items():
        a, b = source_proofs[name], generated_proofs[mapped]
        need(kernel.normalized_type(a)[0] == kernel.normalized_type(b)[0]
             and kernel.rename_expr(kernel.normalized_type(a)[1], mapping)
                 == kernel.normalized_type(b)[1]
             and a['axioms'] == b['axioms'],
             'Actual paired CI full type/Std3 differs: ' + name)
        for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
            need(sorted({mapping.get(x, x) for x in a[field]}) == b[field],
                 'Actual source/generated proof constants differ: ' + name + ':' + field)
    for rows in [source_proofs, generated_proofs]:
        for row in rows.values():
            for name in row['allUsedConstants']:
                if name in graph or name.startswith('OAI.') or name.startswith('_private.OAI.'):
                    need(name in rows or name in prep['provider_subtracted_names'],
                         'Uncovered actual project proof dependency: ' + name)
    scales_result = scales_cert.validate('scalescosts')
    scales_path = stage.scales.STAGE / 'actual-provider-validation.json'
    providers = {'scales_costs': prerequisite(records, 'scales_costs', scales_result,
                    scales_path, stage.scales.PLATFORM_MODULE)}
    child_result = child_cert.validate()
    child_path = stage.child.STAGE / stage.child.CERTIFICATE
    providers['closed_AP14_child'] = prerequisite(records, 'closed_AP14_child',
                    child_result, child_path, stage.child.MODULE)
    for key in stage.base.ap10.CONFIGS:
        config = stage.base.ap10.config(key)
        cert = config['stage'] / ('actual-provider-validation-helper-v2.json'
                                  if key == 'determinant' else 'actual-provider-validation.json')
        report = read(cert)
        need(prep['input_hashes'][rel(cert)] == sha(cert)
             and report['validated'] is True and report['Std3_only'] is True
             and report['platform_module'] == config['platform_module']
             and report['provided_names'] == config['names'],
             'Published AP10 provider exact certificate differs: ' + key)
        olean = TASK / report['provider_olean']
        dep = kernel.imported_dep(records[stage.SOLUTION_OUTPUT],
                                  config['platform_module'])
        need(Path(dep['path']).resolve() == olean.resolve()
             and dep['sha256_before'] == sha(olean) == report['provider_olean_sha256'],
             'Actual imported AP10 OLean differs: ' + key)
        providers['AP10_' + key] = {
            'certificate': rel(cert), 'certificate_sha256': sha(cert),
            'olean': rel(olean), 'olean_sha256': sha(olean),
            'module': config['platform_module']}
    entry_result = entry_cert.validate()
    entry_path = stage.entry.STAGE / stage.entry.CERTIFICATE
    need(entry_path.is_file() and entry_path.read_bytes() == stage.encode(entry_result)
         and entry_result['validated'] is True and entry_result['Std3_only'] is True,
         'Actual AP14 original proof certificate differs')
    pairs = equation_pairs(records, source, generated, source_proofs, generated_proofs)
    target = (STAGE / stage.TARGET_OUTPUT).read_bytes()
    need(target == (prep['preamble'] + prep['formal_statement']).encode()
         and target == (STAGE / 'wire-theorem-source.lean').read_bytes(),
         'Target exact platform wire differs from compiled comparator')
    solution = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    need(b'theorem solution ' in solution and b'sorry' not in solution,
         'Global proof is absent or contains sorry')
    return {'schema_version': 1,
       'artifact_kind': 'ap15-selected-minor-clearing-bound-node-validation',
       'source_commit': stage.COMMIT, 'source_name': stage.TARGET,
       'platform_name': stage.PLATFORM_NAME,
       'source_module': stage.TARGET_MODULE, 'source_byte_range': [16341, 17643],
       'solution_module': stage.SOLUTION_MODULE,
       'solution_source_sha256': sha(STAGE / stage.SOLUTION_OUTPUT),
       'solution_olean': records[stage.SOLUTION_OUTPUT]['data']['output_olean'],
       'solution_olean_sha256': records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],
       'preparation_sha256': sha(STAGE / 'preparation.json'),
       'target_wire_sha256': sha(STAGE / stage.TARGET_OUTPUT),
       'preflights': records, 'actual_provider_bindings': providers,
       'AP14_original_certificate': rel(entry_path),
       'AP14_original_certificate_sha256': sha(entry_path),
       'official_equation_pairs': pairs,
       'all_helpers_literal_original': True, 'existing_port_adaptations': [],
       'source_and_generated_types_equal': True,
       'source_and_generated_theorem_values_null': True,
       'source_and_generated_actual_proof_references_paired': True,
       'actual_automatic_CI_pairs': [[n, m] for n, m in mapping.items()
                                      if n not in public_map],
       'graph_closure_names': sorted(closure),
       'inline_helper_names': prep['inline_helper_names'],
       'axioms': {side: {n: r['axioms'] for n, r in rows.items()}
                  for side, rows in [('source', source_proofs),
                                     ('generated', generated_proofs)]},
       'Std3_only': True,
       'json_sha256': {f: sha(STAGE / f) for f in [stage.SOURCE_TYPE_JSON,
                          stage.GENERATED_TYPE_JSON, stage.SOURCE_REFS_JSON,
                          stage.GENERATED_REFS_JSON]},
       'implementation_hashes': {rel(f): sha(f) for f in [SELF, stage.SELF,
             Path(kernel.__file__), Path(context.__file__),
             Path(kernel.checked_expr.__code__.co_filename)]},
       'max_file_seconds': max(x['data']['seconds'] for x in records.values()),
       'validated': True, 'submission_ready': False,
       'proposal_status': 'Draft', 'Lean_started_by_consumer': False,
       'API_used': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--certify-existing', action='store_true')
    g.add_argument('--check-only', action='store_true')
    args = p.parse_args()
    result = validate()
    path = STAGE / stage.CERTIFICATE
    raw = stage.encode(result)
    if path.exists():
        need(path.read_bytes() == raw, 'Existing immutable certificate differs')
    elif args.certify_existing:
        path.write_bytes(raw)
    print(json.dumps({'certificate': rel(path),
        'certificate_sha256': sha(path) if path.exists() else None,
        'validated': True, 'Std3_only': True,
        'max_file_seconds': result['max_file_seconds'],
        'Lean_started_by_consumer': False, 'API_used': False},
        ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()

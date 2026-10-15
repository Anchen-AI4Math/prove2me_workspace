"""Read-only complete AP16 actual-CI difference inventory before strict certification.

This reports differences; it never permits them in the strict consumer and
does not start Lean, access the API, or write a certificate.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_selected_minor_arithmetic_lower_bound_node as stage
import certify_selected_minor_arithmetic_lower_bound_node as consumer
import certify_selected_minor_clearing_bound_node as clearing_cert
import certify_full_row_minor_node as kernel

TASK, STAGE = stage.TASK, stage.STAGE
read, sha, need = stage.read, stage.sha, stage.need


def project(name):
    return name.startswith('OAI.') or (name.startswith('_private.') and '.OAI.' in name)


def proof_rows(filename, pf, side, roots, boundary):
    doc = consumer.written(STAGE / filename, pf)
    need(set(doc) == {'schemaVersion', 'side', 'probeMainModule',
         'rootNames', 'boundaryNames', 'rows'} and doc['schemaVersion'] == 1
         and doc['side'] == side and doc['rootNames'] == roots
         and doc['probeMainModule'] == ('SourceSnapshot' if side == 'source'
                                        else 'GeneratedSnapshot')
         and doc['boundaryNames'] == sorted(boundary),
         'Actual complete proof-reference envelope differs: ' + side)
    names = [r['name'] for r in doc['rows']]
    need(names == sorted(set(names)) and set(roots) <= set(names),
         'Actual proof CI inventory omits a root or duplicates a name: ' + side)
    rows = {}
    for row in doc['rows']:
        owner = row['owner']['module']
        if row['owner']['kind'] == 'ImportedModule':
            kernel.evidence_row(row, name=row['name'], module=owner, helper=True)
        else:
            need(row['owner'] == {'kind': 'OwnModule', 'moduleIndex': None,
                                 'module': 'SourceSnapshot' if side == 'source'
                                 else 'GeneratedSnapshot'},
                 'Unexpected own-module actual CI owner: ' + row['name'])
            need(row['closedType'] is True and row['closedValue'] is True
                 and row['allUsedConstants'] == sorted(set(row['typeRefs'] + row['valueRefs']))
                 and set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'},
                 'Own-module actual CI is not closed/Std3: ' + row['name'])
            kernel.checked_expr(row['type'], set(row['levelParams']))
        rows[row['name']] = row
    return rows


def full_type_hash(row):
    return stage.sha_bytes(stage.encode(kernel.normalized_type(row)))


def unpaired_row(row):
    return {'name': row['name'], 'owner': row['owner'],
            'full_type_sha256': full_type_hash(row), 'axioms': row['axioms'],
            'project_type_refs': [x for x in row['typeRefs'] if project(x)],
            'project_value_refs': [x for x in row['valueRefs'] if project(x)],
            'nonproject_type_refs': [x for x in row['typeRefs'] if not project(x)],
            'nonproject_value_refs': [x for x in row['valueRefs'] if not project(x)]}


def paired_row(source, generated, mapping):
    a, b = source, generated
    levels_a, expr_a = kernel.normalized_type(a)
    levels_b, expr_b = kernel.normalized_type(b)
    source_type_refs = {mapping.get(x, x) for x in a['typeRefs']}
    generated_type_refs = set(b['typeRefs'])
    source_value_refs = {mapping.get(x, x) for x in a['valueRefs']}
    generated_value_refs = set(b['valueRefs'])
    project_value_a = sorted(x for x in source_value_refs if project(x))
    project_value_b = sorted(x for x in generated_value_refs if project(x))
    deltas = {}
    for field in ['typeRefs', 'valueRefs', 'allUsedConstants']:
        left = {mapping.get(x, x) for x in a[field]}
        right = set(b[field])
        deltas[field] = {'source_only': sorted(left - right),
                         'generated_only': sorted(right - left),
                         'nonproject_source_only': sorted(x for x in left - right if not project(x)),
                         'nonproject_generated_only': sorted(x for x in right - left if not project(x))}
    return {'source_name': a['name'], 'generated_name': b['name'],
            'source_owner': a['owner'], 'generated_owner': b['owner'],
            'source_full_type_sha256': full_type_hash(a),
            'generated_full_type_sha256': full_type_hash(b),
            'normalized_full_type_equal_after_actual_name_mapping':
                levels_a == levels_b and kernel.rename_expr(expr_a, mapping) == expr_b,
            'source_axioms': a['axioms'], 'generated_axioms': b['axioms'],
            'axioms_equal': a['axioms'] == b['axioms'],
            'type_refs_equal': source_type_refs == generated_type_refs,
            'project_value_refs_equal': project_value_a == project_value_b,
            'project_value_refs_source': project_value_a,
            'project_value_refs_generated': project_value_b,
            'actual_reference_differences': deltas}


def run():
    stage.check_only()
    prep = read(STAGE / 'preparation.json')
    records = {name: consumer.preflight(name, prep) for name in stage.FILES}
    boundary = set(prep['provider_subtracted_names'])
    source_types = consumer.types(stage.SOURCE_TYPE_JSON,
                                  records[stage.SOURCE_SNAPSHOT],
                                  prep['source_type_only_names'])
    generated_types = consumer.types(stage.GENERATED_TYPE_JSON,
                                     records[stage.GENERATED_SNAPSHOT],
                                     prep['generated_type_only_names'])
    source = proof_rows(stage.SOURCE_REFS_JSON, records[stage.SOURCE_SNAPSHOT],
                        'source', prep['source_type_only_names'], boundary)
    generated = proof_rows(stage.GENERATED_REFS_JSON, records[stage.GENERATED_SNAPSHOT],
                           'generated', prep['generated_type_only_names'], boundary)
    root_map = {name: name for name in prep['inline_helper_names']}
    root_map[stage.TARGET] = 'solution'
    source_extra = {n: r for n, r in source.items() if n not in root_map}
    generated_extra = {n: r for n, r in generated.items() if n not in root_map.values()}
    extra_pairing_error = None
    try:
        mapping = clearing_cert.pair_extra(source_extra, generated_extra, root_map)
    except Exception as exc:
        mapping = root_map
        extra_pairing_error = str(exc)
    paired = []
    for name, mapped in mapping.items():
        paired.append(paired_row(source[name], generated[mapped], mapping))
    root_type_checks = {}
    for name, mapped in root_map.items():
        a, b = source_types[name], generated_types[mapped]
        la, ea = kernel.normalized_type(a)
        lb, eb = kernel.normalized_type(b)
        root_type_checks[name] = {'generated_name': mapped,
            'type_only_values_both_null': a['value'] is None and b['value'] is None,
            'normalized_full_type_equal_after_actual_name_mapping':
                la == lb and kernel.rename_expr(ea, mapping) == eb,
            'source_full_type_sha256': full_type_hash(a),
            'generated_full_type_sha256': full_type_hash(b)}
    report = {'schema_version': 1,
        'artifact_kind': 'ap16-selected-minor-lower-bound-read-only-actual-CI-audit',
        'source_commit': stage.COMMIT, 'source_name': stage.TARGET,
        'source_root_count': len(prep['source_type_only_names']),
        'generated_root_count': len(prep['generated_type_only_names']),
        'source_actual_CI_count': len(source), 'generated_actual_CI_count': len(generated),
        'source_extra_actual_CI_names': sorted(source_extra),
        'generated_extra_actual_CI_names': sorted(generated_extra),
        'unpaired_source_extra_actual_CIs': [unpaired_row(source_extra[n]) for n in sorted(source_extra)]
            if extra_pairing_error is not None else [],
        'unpaired_generated_extra_actual_CIs': [unpaired_row(generated_extra[n])
            for n in sorted(generated_extra)] if extra_pairing_error is not None else [],
        'automatic_extra_pairing_error': extra_pairing_error,
        'root_type_only_checks': root_type_checks,
        'all_actual_paired_CI_checks': paired,
        'every_root_complete_type_equal': all(x['normalized_full_type_equal_after_actual_name_mapping']
                                               and x['type_only_values_both_null']
                                               for x in root_type_checks.values()),
        'all_actual_CIs_paired': extra_pairing_error is None,
        'strict_consumer_was_not_run': True,
        'reference_differences_are_reported_not_permitted': True,
        'Lean_started': False, 'API_used': False}
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', action='store_true', required=True)
    p.parse_args()
    print(json.dumps(run(), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()

"""Offline AP21 certificate derived from four genuine, immutable compiler contexts.

The original strict consumer is preserved. This successor accounts for the
observed source data closure and two unused generated equation theorems.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import certify_actual_row_count_pos_node as old
import certify_full_row_minor_node as kernel
import stage_actual_row_count_pos_node as stage
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
DEST = stage.V / 'ap21/actual-row-count-pos-node-validation-v2'
CERT = DEST / 'node-validation-v2.json'
AUDIT = DEST / 'finite-actual-CI-ledger.json'
AUTOS = ('OAI.PiExponent.mem_strictWeightedSimplex._simp_1_2',
         'OAI.PiExponent.mem_strictWeightedSimplex._simp_1_3')
UNUSED_EQ = {
    'OAI.PiExponent.InterpolationMatrix.rowWeights.eq_1':
        ('OAI.PiExponent.InterpolationMatrix.rowWeights',
         stage.V / 'ap9/domains/generated-full-ci.jsonl',
         stage.V / 'ap9/domains/actual-provider-validation.json'),
    'OAI.PiExponent.strictWeightedSimplex.eq_1':
        ('OAI.PiExponent.strictWeightedSimplex',
         stage.V / 'ap9/simplex/generated-full-ci.jsonl',
         stage.V / 'ap9/simplex/actual-provider-validation.json'),
}
DATA_PROVIDERS = (
    ('ap7/collision-constant', 'actual-provider-validation.json'),
    ('ap9/simplex', 'actual-provider-validation.json'),
    ('ap9/domains', 'actual-provider-validation.json'),
    ('ap10/determinant', 'actual-provider-validation-helper-v2.json'),
    ('ap10/arithmetic', 'actual-provider-validation.json'),
    ('ap20/literal-interface-data', 'actual-provider-validation.json'),
)
SOURCE_ONLY = {
    'OAI.PiExponent.DeterminantContradiction.FixedData',
    'OAI.PiExponent.DeterminantContradiction.Row',
    'OAI.PiExponent.DeterminantContradiction.actualRowCount',
    'OAI.PiExponent.DeterminantContradiction.collisionConstant',
    'OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1',
    'OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_2',
    'OAI.PiExponent.DeterminantContradiction.finiteDenominators',
    'OAI.PiExponent.InterpolationMatrix.Row',
    'OAI.PiExponent.InterpolationMatrix.rowWeights',
    'OAI.PiExponent.LiteralAnalytic.fixedWeights',
    'OAI.PiExponent.MatrixArithmetic.logWeights',
    'OAI.PiExponent.realWeightedSimplex',
    'OAI.PiExponent.strictWeightedSimplex',
}
CACHE = {
    'OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1',
    'OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_2',
}
DIRECT_DATA = {
    'Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData':
        (stage.V / 'ap19/analytic-remainder-auto-ci-validation-v5/'
         'actual-provider-validation-auto-ci-v5.json',
         'original_emitted_provider_olean', 'original_emitted_provider_olean_sha256'),
    'Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData':
        (stage.V / 'ap14/row-data/actual-provider-validation.json',
         'provider_olean', 'provider_olean_sha256'),
    'Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData':
        (stage.DATA_CERT, 'provider_olean', 'provider_olean_sha256'),
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def rows(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines()
            if line.strip()]


def certified_data():
    result = {}
    hashes = {}
    for relative, certname in DATA_PROVIDERS:
        folder = stage.V / relative
        certpath = folder / certname
        cert = stage.read(certpath)
        source = folder / 'source-full-ci.jsonl'
        generated = folder / 'generated-full-ci.jsonl'
        need(cert['validated'] is True and cert['Std3_only'] is True
             and cert['output_json_sha256'][stage.rel(source)] == stage.sha(source)
             and cert['output_json_sha256'][stage.rel(generated)] == stage.sha(generated),
             'Frozen published data source/generated complete CI evidence differs: '
             + relative)
        hashes[stage.rel(certpath)] = stage.sha(certpath)
        for row in rows(source):
            name = row['resolvedName']
            need(name not in result, 'Duplicate certified source CI: ' + name)
            result[name] = (row, source)
    return result, hashes


def same_source_full_ci(actual, certified, name):
    need(certified['resolvedName'] == name
         and certified['closedType'] is True and certified['closedValue'] is True
         and set(certified['axioms']) <= old.STD3
         and kernel.normalized_type(actual) == kernel.normalized_type(certified)
         and actual['axioms'] == certified['axioms']
         and actual['owner']['module'] == certified['sourceModule']
         and actual['typeRefs'] == kernel.refs(certified['type'])
         and actual['valueRefs'] == kernel.refs(certified['value']),
         'Source-only CI differs from certified full original data value: ' + name)


def auxiliary_caches(actual_source):
    path = (stage.V / 'ap20/analytic-translated-two-layer-reduction-final-v3/'
            'source-actual-auxiliary-CIs.json')
    certpath = (stage.V / 'ap20/analytic-translated-two-layer-reduction-validation-v4/'
                'open-sketch-interface-validation-v4.json')
    cert = stage.read(certpath)
    need(cert['validated'] is True
         and cert['output_json_sha256'][stage.rel(path)] == stage.sha(path),
         'Actual historical two-layer source auxiliary CI witness differs')
    witnesses = {r['name']: r for r in stage.read(path)['actualAuxiliaryCIs']}
    for name in CACHE:
        a, b = actual_source[name], witnesses[name]
        need(b['kind'] == 'theorem' and b['isProp'] is True
             and b['closedType'] is True and b['closedValue'] is True
             and kernel.normalized_type(a) == kernel.normalized_type(b)
             and a['axioms'] == b['axioms'] and set(b['axioms']) <= old.STD3
             and a['owner']['module'] == b['actualOwner']
             and a['typeRefs'] == b['typeRefs']
             and a['valueRefs'] == b['valueRefs'],
             'Historical closed Prop data cache differs: ' + name)
    return {stage.rel(path): stage.sha(path), stage.rel(certpath): stage.sha(certpath)}


def eq_head_and_body(ci_type, primary_value, primary_name):
    typ, value = ci_type, primary_value
    binders = 0
    while isinstance(typ, list) and typ[0] == 'forall':
        need(len(typ) == 4, 'Malformed generated unused equation binder')
        typ = typ[3]
        binders += 1
    value_binders = 0
    while isinstance(value, list) and value[0] == 'lambda':
        need(len(value) == 4, 'Malformed certified full Def value binder')
        value = value[3]
        value_binders += 1
    args = []
    while isinstance(typ, list) and typ[0] == 'app':
        args.insert(0, typ[2])
        typ = typ[1]
    need(binders == value_binders and typ[0:2] == ['const', 'Eq']
         and len(args) == 3 and kernel.refs(args[-2]) == [primary_name]
         and args[-1] == value,
         'Unused closed equation is not exact certified primary Def RHS: ' + primary_name)


def actual_records(prep):
    prior = prep['reused_original_stub_context']
    old_record = context.record(stage.TASK / prior['source'],
                                stage.TASK / prior['manifest'], 'emit-olean',
                                stage.MODULE, stage.TASK / prior['root'])
    old_data = old_record['data']
    need(stage.sha(stage.TASK / prior['preflight']) == prior['preflight_sha256']
         and old_data['output_olean_sha256'] == prior['output_olean_sha256']
         and old_data['source_sha256_before'] == old_data['source_sha256_after'] ==
             stage.sha(stage.STAGE / stage.TARGET_OUTPUT)
         and prior['sorryAx_comparator_only'] is True,
         'Historical real Open comparator emitter differs')
    records = {stage.TARGET_OUTPUT: old_record}
    for i, (name, mode) in enumerate(zip(stage.FILES[1:], stage.MODES[1:], strict=True), 2):
        module = Path(name).with_suffix('').as_posix().replace('/', '.')
        record = context.record(stage.STAGE / name, stage.STAGE / f'c{i}.json',
                                mode, module, stage.STAGE)
        data = record['data']
        need(data['success'] is True and data['exit_code'] == 0
             and data['timed_out'] is False and 0 < data['seconds'] <= 300
             and data['timeout_seconds'] == 300 and data['mode'] == mode
             and data['cleanup_completed'] is True,
             'Bounded actual AP21 compiler context differs: ' + name)
        records[name] = record
    need(records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'] ==
         stage.sha(stage.V / 'staged-build/lib/lean' /
                   Path(stage.SOLUTION_OUTPUT).with_suffix('.olean')),
         'Actual global solution OLean differs')
    imported = kernel.imported_dep(records[stage.GENERATED_SNAPSHOT],
                                   stage.SOLUTION_MODULE)
    need(imported['sha256_before'] ==
         records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],
         'Generated metadata did not import actual global solution')
    bridge = {}
    for module, (path, key_path, key_sha) in DIRECT_DATA.items():
        cert = stage.read(path)
        need(cert['validated'] is True and cert['Std3_only'] is True,
             'Direct historical provider is not certified: ' + module)
        expected = cert[key_sha]
        need(expected == stage.sha(stage.TASK / cert[key_path]),
             'Certified direct provider OLean current bytes differ: ' + module)
        item = kernel.imported_dep(old_record, module)
        need(item['sha256_before'] == expected
             and Path(item['path']).resolve() == (stage.TASK / cert[key_path]).resolve(),
             'Historical c1 actual imported provider differs: ' + module)
        if module.endswith('LiteralAnalyticSummand_InterfaceData'):
            direct = kernel.imported_dep(records[stage.SOLUTION_OUTPUT], module)
            need(direct['sha256_before'] == expected
                 and Path(direct['path']).resolve() == (stage.TASK / cert[key_path]).resolve(),
                 'Closed c2 actual imported provider differs from published full Def CI')
        bridge[module] = {'certificate': stage.rel(path), 'certificate_sha256': stage.sha(path),
                          'actual_olean_sha256': expected,
                          'c1_imported_path': item['path']}
    return records, bridge


def validate():
    stage.check_only()
    prep = stage.read(stage.STAGE / 'preparation.json')
    route = stage.read(stage.ROUTE / 'source-route.json')
    need(prep['original_AST_count'] == 7 and prep['original_source_lines'] == 53
         and prep['platform_name'] == route['target'] == stage.TARGET
         and prep['platform_theorem_id'] == stage.TARGET_ID
         and prep['actual_new_compiler_contexts'] == 3
         and prep['actual_reused_compiler_contexts'] == 1
         and prep['proposal_status'] == 'Draft'
         and prep['submission_ready'] is False,
         'Original seven-proof AP21 frozen plan differs')
    closure = stage.read(stage.CLOSURE)
    target_rows = [r for r in closure['rows'] if r['name'] == stage.TARGET]
    need(closure['all_missing_data_domains_empty'] is True and len(target_rows) == 1
         and target_rows[0]['missing_data_CIs'] == [],
         'Published source type/Def value import closure differs')
    records, bridge = actual_records(prep)
    inventory = old.written(stage.STAGE / stage.INVENTORY,
                            records[stage.GENERATED_SNAPSHOT])
    helpers = route['helper_names']
    need(inventory['schemaVersion'] == 1
         and inventory['solutionModule'] == stage.SOLUTION_MODULE
         and inventory['sourceHelpers'] == helpers
         and inventory['publicPlatformTarget'] == 'solution',
         'Actual generated owner-inventory identity differs')
    private = inventory['actualPrivateHelpers']
    need(len(private) == len(helpers) == 6 and len(set(private)) == 6,
         'Six genuine private source proof helpers differ')
    source_roots = helpers + [stage.TARGET]
    gen_roots = private + ['solution']
    source_types = old.types(stage.STAGE / stage.SOURCE_TYPES,
                             records[stage.SOURCE_SNAPSHOT], source_roots)
    gen_types = old.types(stage.STAGE / stage.GENERATED_TYPES,
                          records[stage.GENERATED_SNAPSHOT], gen_roots)
    source = old.proofs(stage.STAGE / stage.SOURCE_REFS,
                        records[stage.SOURCE_SNAPSHOT], 'source', source_roots,
                        set(prep['source_modules']))
    generated = old.proofs(stage.STAGE / stage.GENERATED_REFS,
                           records[stage.GENERATED_SNAPSHOT], 'generated', gen_roots,
                           {stage.SOLUTION_MODULE})
    mapping = dict(zip(helpers, private, strict=True))
    mapping[stage.TARGET] = 'solution'
    raw = inventory['rawOwnedCIs']
    raw_names = inventory['rawOwnedNames']
    need(raw_names == sorted(set(raw_names))
         and [row['actualName'] for row in raw] == raw_names
         and set(raw_names) == set(generated) | set(UNUSED_EQ),
         'Raw ModuleIdx owner inventory differs from 9 proof CIs plus 2 unused equations')
    owned = {row['actualName']: row for row in raw}
    for row in raw:
        name = row['actualName']
        need(row['kind'] == 'theorem' and row['isProp'] is True
             and row['CI']['closedType'] is True and row['CI']['closedValue'] is True,
             'Generated actual owner CI not a closed Prop theorem: ' + name)
        kernel.evidence_row(row['CI'], name=name, module=stage.SOLUTION_MODULE,
                            helper=True)
        if name in generated:
            need(row['CI'] == generated[name],
                 'Generated owned CI differs from complete proof closure: ' + name)
    for name, private_name in zip(helpers, private, strict=True):
        need(owned[private_name]['privateUserName'] == name,
             'Actual privateToUserName mapping differs: ' + name)
    actual_auto = {row['privateUserName']: row['actualName'] for row in raw
                   if row['privateUserName'] in AUTOS}
    need(set(actual_auto) == set(AUTOS) and len(set(actual_auto.values())) == 2,
         'Actual generated private simplification CI cache domain differs')
    mapping.update(actual_auto)
    need(set(generated) == set(mapping.values())
         and set(source) == set(mapping) | SOURCE_ONLY,
         'Complete actual source/generated theorem plus data CI domains differ')
    for source_name, generated_name in mapping.items():
        a, b = source[source_name], generated[generated_name]
        at, bt = kernel.normalized_type(a), kernel.normalized_type(b)
        need(at[0] == bt[0] and kernel.rename_expr(at[1], mapping) == bt[1]
             and a['axioms'] == b['axioms'],
             'Nine own actual closed proof/cache types or Std3 differ: ' + source_name)
        if source_name in source_types:
            a_type, b_type = source_types[source_name], gen_types[generated_name]
            at, bt = kernel.normalized_type(a_type), kernel.normalized_type(b_type)
            need(at[0] == bt[0] and kernel.rename_expr(at[1], mapping) == bt[1],
                 'Full original TypeOnly theorem differs: ' + source_name)
        for field in ('typeRefs', 'valueRefs', 'allUsedConstants'):
            need({mapping.get(n, n) for n in a[field]} == set(b[field]),
                 'Exact actual closed proof refs differ: ' + source_name + ':' + field)
    certified, provider_hashes = certified_data()
    for name in SOURCE_ONLY - CACHE:
        need(name in certified, 'Uncovered actual source data CI: ' + name)
        same_source_full_ci(source[name], certified[name][0], name)
    aux_hashes = auxiliary_caches(source)
    used_generated = set().union(*(set(r['allUsedConstants']) for r in generated.values()))
    equations = {}
    for name, (primary, generated_jsonl, certpath) in UNUSED_EQ.items():
        row = owned[name]
        need(row['privateUserName'] is None and name not in used_generated,
             'Generated extra equation is private or used by the proof: ' + name)
        cert = stage.read(certpath)
        need(cert['validated'] is True and cert['Std3_only'] is True
             and cert['output_json_sha256'][stage.rel(generated_jsonl)] ==
             stage.sha(generated_jsonl),
             'Certified published primary Def value differs: ' + primary)
        primary_rows = [r for r in rows(generated_jsonl) if r['resolvedName'] == primary]
        need(len(primary_rows) == 1 and primary_rows[0]['closedValue'] is True,
             'Unique certified generated primary Def value missing: ' + primary)
        eq_head_and_body(row['CI']['type'], primary_rows[0]['value'], primary)
        equations[name] = {'primary_def': primary,
                           'primary_generated_full_CI': stage.rel(generated_jsonl),
                           'primary_generated_full_CI_sha256': stage.sha(generated_jsonl),
                           'primary_provider_certificate_sha256': stage.sha(certpath),
                           'actual_equation_type_and_rhs_equal_certified_Def_value': True,
                           'closed_Std3_unused_Prop': True,
                           'owner': row['CI']['owner']}
    for row in generated.values():
        for used in row['allUsedConstants']:
            if used.startswith('OAI.') or used.startswith('_private.') and '.OAI.' in used:
                need(used in generated or used in certified or
                     used in target_rows[0]['source_graph_type_and_Def_value_dependencies'],
                     'Unknown actual project proof dependency: ' + used)
    return {'schema_version': 2,
            'artifact_kind': 'ap21-actual-row-count-seven-original-AST-closed-validation-v2',
            'validated': True, 'Std3_only': True,
            'platform_theorem_id': stage.TARGET_ID,
            'public_platform_boundary_names': [stage.TARGET],
            'source_commit': prep['source_commit'],
            'original_AST_count': 7, 'original_source_lines': 53,
            'original_proof_suffixes_unchanged': True,
            'source_and_generated_full_types_equal': True,
            'own_actual_proof_and_auto_CI_pairs': mapping,
            'source_only_certified_data_CIs': sorted(SOURCE_ONLY),
            'source_only_provider_certificate_hashes': provider_hashes,
            'source_auxiliary_closed_Prop_witness_hashes': aux_hashes,
            'raw_owned_CI_names': raw_names,
            'unused_actual_closed_data_equations': equations,
            'actual_direct_provider_olean_bridges': bridge,
            'references_bitwise_equal_on_nine_own_CI_pairs': True,
            'external_instance_reference_deltas': [],
            'actual_import_closure_sha256': stage.sha(stage.CLOSURE),
            'original_consumer_preimage_sha256': stage.sha(old.SELF),
            'original_finite_domain_audit_sha256':
                stage.sha(stage.STAGE / 'actual-ci-audit.json'),
            'preflights': {name: r['data'] for name, r in records.items()},
            'max_file_seconds': max(r['data']['seconds'] for r in records.values()),
            'output_json_sha256': {
                stage.rel(stage.STAGE / name): stage.sha(stage.STAGE / name)
                for name in (stage.SOURCE_TYPES, stage.GENERATED_TYPES,
                             stage.SOURCE_REFS, stage.GENERATED_REFS, stage.INVENTORY)},
            'compiler_manifest_hashes': {
                f'c{i}.json': stage.sha(stage.STAGE / f'c{i}.json') for i in (2, 3, 4)},
            'solution_olean_sha256': records[stage.SOLUTION_OUTPUT]['data']['output_olean_sha256'],
            'implementation_hashes': {stage.rel(SELF): stage.sha(SELF),
                                      stage.rel(old.SELF): stage.sha(old.SELF),
                                      stage.rel(stage.SELF): stage.sha(stage.SELF)},
            'proposal_status': 'Draft', 'submission_ready': False,
            'Lean_started_by_consumer': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--audit-static', action='store_true')
    group.add_argument('--certify-existing', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.audit_static:
        # Intentionally no deep validation: Root runs the sole complete replay.
        need(stage.STAGE.joinpath('actual-ci-audit.json').is_file(),
             'Genuine full-domain audit is required')
        print(json.dumps({'consumer_sha256': stage.sha(SELF),
                          'original_audit_sha256': stage.sha(
                              stage.STAGE / 'actual-ci-audit.json'),
                          'source_only_data_names': len(SOURCE_ONLY),
                          'observed_own_auto_names': len(AUTOS),
                          'observed_unused_equations': len(UNUSED_EQ),
                          'deep_replay_started': False}))
        return
    result = validate()
    if args.certify_existing:
        DEST.mkdir(parents=True, exist_ok=True)
        need(not CERT.exists(), 'Derived AP21 certificate already exists')
        CERT.write_bytes(stage.encode(result))
    else:
        need(CERT.is_file() and CERT.read_bytes() == stage.encode(result),
             'Saved derived strict AP21 certificate differs')
    print(json.dumps({'validated': True, 'certificate': stage.rel(CERT),
                      'sha256': stage.sha(CERT),
                      'max_file_seconds': result['max_file_seconds']}))


if __name__ == '__main__':
    main()

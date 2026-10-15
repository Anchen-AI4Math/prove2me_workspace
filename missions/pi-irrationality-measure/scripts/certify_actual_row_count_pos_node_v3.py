"""Offline AP21 complete project-reference certificate from immutable contexts.

The original strict consumer is preserved. This successor accounts for the
observed source data closure and two unused generated equation theorems.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import certify_actual_row_count_pos_node as old
import certify_actual_row_count_pos_node_v2 as preimage
import certify_full_row_minor_node as kernel
import stage_actual_row_count_pos_node as stage
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
DEST = stage.V / 'ap21/actual-row-count-pos-node-validation-v3'
CERT = DEST / 'node-validation-v3.json'
V2_FAILURE = stage.V / 'ap21/actual-row-count-pos-node-validation-v2/failed-consumer-record.json'
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
PROJECT_PROVIDERS = (
    ('ap2/s/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/structural-generated.jsonl',
     'ap2/s/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/provider-validation-structural.json',
     'ap2/publication/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/publication.json', 'structural'),
    ('providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/structural-generated.jsonl',
     'providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/provider-validation-structural.json',
     'providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/publication.json', 'structural'),
    ('providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic/fast-generated.jsonl',
     'providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic/provider-validation-fast.json',
     'ap7/publication/Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic/publication.json', 'fast'),
    ('ap7/collision-constant/generated-full-ci.jsonl',
     'ap7/collision-constant/actual-provider-validation.json',
     'ap7/collision-constant/publication-draft/publication.json', 'modern'),
    ('ap9/simplex/generated-full-ci.jsonl',
     'ap9/simplex/actual-provider-validation.json',
     'ap9/simplex/publication/publication.json', 'modern'),
    ('ap9/domains/generated-full-ci.jsonl',
     'ap9/domains/actual-provider-validation.json',
     'ap9/domains/publication/publication.json', 'modern'),
    ('ap10/determinant/generated-full-ci.jsonl',
     'ap10/determinant/actual-provider-validation-helper-v2.json',
     'ap10/determinant/publication-helper-v2/publication.json', 'modern'),
    ('ap10/arithmetic/generated-full-ci.jsonl',
     'ap10/arithmetic/actual-provider-validation.json',
     'ap10/arithmetic/publication/publication.json', 'modern'),
    ('ap20/literal-interface-data/generated-full-ci.jsonl',
     'ap20/literal-interface-data/actual-provider-validation.json',
     'ap20/literal-interface-data/publication/publication.json', 'modern'),
)


def certified_project_references(actual_project_names):
    """Bind every observed external OAI ref to a published typed full CI.

    The actual project domain is calculated from the nine generated proof rows;
    these exact nine provider records must cover it with no unknown names.
    """
    ledger = {}
    provider_records = {}
    for jsonl_rel, cert_rel, publication_rel, kind in PROJECT_PROVIDERS:
        jsonl_path, certpath, pubpath = (stage.V / jsonl_rel, stage.V / cert_rel,
                                        stage.V / publication_rel)
        cert, pub = stage.read(certpath), stage.read(pubpath)
        need(cert['validated'] is True,
             'Actual typed project provider certificate not validated: ' + cert_rel)
        if kind == 'modern':
            need(cert['Std3_only'] is True
                 and cert['output_json_sha256'][stage.rel(jsonl_path)] == stage.sha(jsonl_path),
                 'Published modern full-CI hash/Std3 differs: ' + jsonl_rel)
            olean, olean_sha = cert['provider_olean'], cert['provider_olean_sha256']
        elif kind == 'structural':
            need(cert['generated_jsonl_sha256'] == stage.sha(jsonl_path)
                 and cert['types_equal'] is True
                 and cert['definition_values_equal'] is True
                 and cert['axioms_equal_and_std3'] is True
                 and cert['whole_atomic_graph_ci_coverage_equal'] is True,
                 'Published structural generated full-CI parity differs: ' + jsonl_rel)
            pf = cert['provider_preflight']
            need(stage.sha(stage.TASK / pf['record']) == pf['record_sha256'],
                 'Published structural provider actual preflight record differs')
            olean, olean_sha = pf['output_olean'], pf['output_olean_sha256']
        else:
            snap = cert['fast_generated_snapshot']
            need(cert['status'] == 'local-kernel-provider-validated'
                 and cert['proof_axioms'] == 'Std3'
                 and snap['generated_jsonl_sha256'] == stage.sha(jsonl_path)
                 and cert['snapshot_comparison']['types_equal'] is True
                 and cert['snapshot_comparison']['values_equal'] is True
                 and cert['snapshot_comparison']['axioms_equal_and_std3'] is True,
                 'Published fast generated full-CI parity differs: ' + jsonl_rel)
            pfs = [x for x in cert['preflights'] if x['role'] == 'provider-bundle']
            need(len(pfs) == 1 and
                 stage.sha(stage.TASK / pfs[0]['record']) == pfs[0]['record_sha256'],
                 'Published fast provider actual preflight record differs')
            olean, olean_sha = pfs[0]['output_olean'], pfs[0]['output_olean_sha256']
        need(stage.sha(stage.TASK / olean) == olean_sha,
             'Actual certified project provider OLean differs: ' + cert_rel)
        readback = pub['target_readback']
        body = readback['body']
        if 'raw_body_utf8' in readback or 'raw_body_sha256' in readback:
            need(stage.digest(readback['raw_body_utf8'].encode()) ==
                 readback['raw_body_sha256'],
                 'Saved newer public Definition raw-body hash differs')
        else:
            need(set(readback) == {'http_status', 'body'},
                 'Historical parsed-only public Definition readback schema differs')
        need(readback['http_status'] == 200
             and pub['last_publish_verdict']['body']['status'] == 'PUBLISHED'
             and body['status'] == 'Definition'
             and body['theorem_id'] == pub['definition_id']
             and body['theorem_name'] == pub['definition_name']
             and body['visibility'] == 'public'
             and body['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
             and body['deprecated_at'] is None,
             'Fresh saved public Definition readback differs: ' + publication_rel)
        provider_records[stage.rel(certpath)] = {
            'certificate_sha256': stage.sha(certpath),
            'full_CI_jsonl_sha256': stage.sha(jsonl_path),
            'public_readback_sha256': stage.sha(pubpath),
            'published_definition_id': pub['definition_id'],
            'certified_provider_olean_sha256': olean_sha,
        }
        for row in rows(jsonl_path):
            name = row['resolvedName']
            if name not in actual_project_names:
                continue
            opaque_theorem = (kind == 'structural' and row['envKind'] == 'theorem'
                              and row['value'] is None and row['closedValue'] is None)
            if opaque_theorem:
                certificates = [x for x in cert['generated_row_certificates']
                                if x['source_name'] == name]
                need(len(certificates) == 1
                     and certificates[0]['std3_only'] is True
                     and certificates[0]['kernel_metadata_complete'] is True
                     and certificates[0]['module'] == cert['platform_module']
                     and certificates[0]['axioms'] == row['axioms'],
                     'Published structural opaque theorem actual row certificate differs: '
                     + name)
            need(name not in ledger and row['closedType'] is True
                 and (opaque_theorem or
                      row['closedValue'] is True and row['value'] is not None)
                 and set(row['axioms']) <= old.STD3,
                 'Duplicate or open actual referenced published CI: ' + name)
            kernel.checked_expr(row['type'], set(row['levelParams']))
            if not opaque_theorem:
                kernel.checked_expr(row['value'], set(row['levelParams']))
            ledger[name] = {
                'provider_certificate': stage.rel(certpath),
                'full_CI_jsonl': stage.rel(jsonl_path),
                'env_kind': row['envKind'],
                'closed_type': True,
                'closed_value': True if not opaque_theorem else None,
                'opaque_theorem_proof_certified_Std3_without_value_export': opaque_theorem,
                'axioms': row['axioms'],
                'complete_type_sha256': stage.digest(stage.encode(row['type'])),
                'complete_value_sha256': (None if opaque_theorem else
                                          stage.digest(stage.encode(row['value']))),
                'type_refs': kernel.refs(row['type']),
                'value_refs': (None if opaque_theorem else kernel.refs(row['value'])),
            }
    need(set(ledger) == set(actual_project_names),
         'Observed actual generated project refs outside exact certified published CI domain: '
         + str(sorted(set(actual_project_names) - set(ledger))))
    return ledger, provider_records


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
    actual_project = {used for row in generated.values()
                      for used in row['allUsedConstants']
                      if used.startswith('OAI.') or
                      used.startswith('_private.') and '.OAI.' in used}
    external_project = actual_project - set(raw_names)
    project_ledger, project_providers = certified_project_references(external_project)
    need(len(actual_project) == 31 and len(external_project) == 23
         and set(project_ledger) == external_project,
         'Genuine complete generated project-reference domain differs')
    failure = stage.read(V2_FAILURE)
    need(failure['exit_code'] == 1 and failure['certificate_created'] is False
         and failure['consumer_sha256'] == stage.sha(preimage.SELF)
         and failure['original_full_domain_audit_sha256'] ==
             stage.sha(stage.STAGE / 'actual-ci-audit.json'),
         'Preserved original derived-v2 strict failure preimage differs')
    return {'schema_version': 3,
            'artifact_kind': 'ap21-actual-row-count-seven-original-AST-closed-validation-v3',
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
            'all_actual_generated_project_references': sorted(actual_project),
            'typed_published_external_project_CI_ledger': project_ledger,
            'typed_published_external_provider_records': project_providers,
            'references_bitwise_equal_on_nine_own_CI_pairs': True,
            'external_instance_reference_deltas': [],
            'actual_import_closure_sha256': stage.sha(stage.CLOSURE),
            'original_consumer_preimage_sha256': stage.sha(old.SELF),
            'v2_consumer_preimage_sha256': stage.sha(preimage.SELF),
            'v2_actual_failure_record_sha256': stage.sha(V2_FAILURE),
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
                                      stage.rel(preimage.SELF): stage.sha(preimage.SELF),
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
        # Finite complete external project CI check, without old deep replay.
        need(stage.STAGE.joinpath('actual-ci-audit.json').is_file(),
             'Genuine full-domain audit is required')
        generated = stage.read(stage.STAGE / stage.GENERATED_REFS)['rows']
        raw = set(stage.read(stage.STAGE / stage.INVENTORY)['rawOwnedNames'])
        actual_project = {used for row in generated for used in row['allUsedConstants']
                          if used.startswith('OAI.') or
                          used.startswith('_private.') and '.OAI.' in used}
        external_project = actual_project - raw
        ledger, provider_records = certified_project_references(external_project)
        DEST.mkdir(parents=True, exist_ok=True)
        audit_path = DEST / 'finite-project-domain-audit.json'
        audit = {'artifact_kind': 'ap21-actual-complete-generated-project-CI-audit',
                 'actual_project_names': sorted(actual_project),
                 'external_project_names': sorted(external_project),
                 'typed_published_CIs': ledger,
                 'actual_published_provider_records': provider_records,
                 'original_full_domain_audit_sha256': stage.sha(
                     stage.STAGE / 'actual-ci-audit.json'),
                 'v2_failure_record_sha256': stage.sha(V2_FAILURE),
                 'deep_node_validation_started': False, 'Lean_started': False,
                 'API_used': False}
        if audit_path.exists():
            need(audit_path.read_bytes() == stage.encode(audit),
                 'Existing finite project domain audit differs')
        else:
            audit_path.write_bytes(stage.encode(audit))
        print(json.dumps({'consumer_sha256': stage.sha(SELF),
                          'original_audit_sha256': stage.sha(
                              stage.STAGE / 'actual-ci-audit.json'),
                          'all_actual_project_refs': len(actual_project),
                          'typed_published_external_refs': len(external_project),
                          'typed_published_providers': len(provider_records),
                          'finite_project_audit_sha256': stage.sha(audit_path),
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

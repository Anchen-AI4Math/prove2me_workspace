"""Prepare exact seven-file PF publication inputs OFFLINE. No API/Lean/imported client."""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re
import unicodedata

OUT = Path(__file__).resolve().parent
PF = OUT.parent
TASK = PF.parents[2]
WORKSPACE = TASK.parents[1]
DOCS = TASK / 'formalization/platform/readback-2026-10-07/api-docs-v0.12.1'
NEW_PROPOSAL = '19653cff-d481-498a-a717-10630d1ca1b7'
TITLE = 'Irrationality of ζ（9）'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE = '2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77'
AUTHOR = '5a9491c73cbbb980b411a3389a4c5acd6f0e5ceb71149c8a508f9553660f0ebf'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
DOC_PINS = {
 'SKILL.md': '6693ed2a822a415b84bfb59240c1504895cda267a46ea348de9cd0a1905131e6',
 'references/mission_captain.md': '85be7ad6e2a9ff1ed70a5100b01c436270660accd36f81e1a16039b7282cfe3e',
 'references/missions.md': '6064c213b1ab65eac8da26f8834efbfa013da60a592b6c6201c702383be86fa9',
 'references/prove.md': '8b231b0494719c4a90abc95687fcd183a24cfcb0636ddcfd9de050d9f5146a18',
 'references/contribute.md': '0c21104fdec143aef4d1dacb208f528b4a1068050a77af642bc1e21cb1471ce1',
 'references/setup.md': 'fca66035b392f696238882ffc4113bf625f0d266402b90e3f0d36d541bad8363',
}
EXPECTED_PAYLOADS = {
 'Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.lean': (2387, '2781de146990caba0ae3fc1e913dfdfb65e40b3dc06a87628d597c86fa81f42e'),
 'Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_polynomial.lean': (529, 'bef2c154fbb15ea53831a0e1d4c536b4298129cfb90f9537780d30a15388bb9b'),
 'Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_global.lean': (712, '2755f905ce4978453a4aa07f72df62e435c11319f824dbc0421c1b1773319115'),
 'Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_injective.lean': (663, 'dda392c7e58ebd1e325e17da75fe3354d13ae663f4d0e22dacef2b63becd72c5'),
 'Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_polynomial.lean': (18873, '90eefdfcd2d8fd4a5dcff75df8b378ae3b97d80346245a2df380468adc31d551'),
 'Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_global.lean': (19051, 'a76fb8426da6ede692f2a8628bc91eab6ed3408aa55d653159fe60af597b6965'),
 'Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_injective.lean': (18995, '968e382bcee06b9c13431fc7beebb68d715608fb311258c140ed8df80b301c69'),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_bytes().decode('utf-8'))


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


def binding(path):
    return dict(task_relative=path.relative_to(TASK).as_posix(), bytes=path.stat().st_size, sha256=sha(path))


def docs_gate():
    for relative, expected in DOC_PINS.items():
        assert sha(DOCS / relative) == expected, relative
    return [binding(DOCS / relative) for relative in DOC_PINS]


def bound_path(row):
    base = TASK if row.get('task_relative') else WORKSPACE
    relative = row.get('task_relative') or row['root_relative']
    path = (base / relative).resolve()
    assert path.is_relative_to(base.resolve()), relative
    return path


def check_binding(row):
    path = bound_path(row)
    assert path.is_file() and path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)


def positive(check):
    assert ('passed' in check) != ('pass' in check), 'Explicit report check schema required'
    return check.get('passed', check.get('pass')) is True


def require_root_pin(pin_path):
    """Pure fail-closed hook for a future Root driver; does not create/assume a pin."""
    docs_gate()
    manifest = load(OUT / 'prepared-publication-v2.json')
    for row in manifest['seven_payloads']:
        check_binding(row['staged_source'])
        check_binding(row['publication_source_copy'])
    pin = load(pin_path)  # Missing pin is an error, never a PASS or placeholder.
    assert pin['purpose'] == 'generic-numerator-PF-global-publication'
    assert pin['new_proposal_id'] == NEW_PROPOSAL
    assert unicodedata.normalize('NFKC', pin['new_proposal_title']) == unicodedata.normalize('NFKC', TITLE)
    assert pin['source_sha256'] == SOURCE and pin['platform_author_sha256'] == AUTHOR
    assert pin['Root_rehashed_all_independent_bindings'] is True
    assert pin['Root_reviewed_actual_source_reachable_full_types_values_and_Std3'] is True
    assert pin['prepared_publication_sha256'] == sha(OUT / 'prepared-publication-v2.json')
    assert pin['prepared_payloads'] == [{k:r[k] for k in ['local_path','bytes','sha256']} for r in manifest['seven_payloads']]
    author_path = PF / 'author-audit.json'
    assert sha(author_path) == AUTHOR
    author = load(author_path)
    assert author['verdict'] == 'PASS' and len(author['checks']) == 24 and all(positive(c) for c in author['checks'])
    assert len(author['stable_files']) == 1441
    for row in author['stable_files']:
        check_binding(row)
    independent_binding = pin['independent_report']
    check_binding(independent_binding)
    independent = load(bound_path(independent_binding))
    assert independent['verdict'] == 'PASS' and independent['checks'] and all(positive(c) for c in independent['checks'])
    assert independent['stable_files'], 'Actual independent bound evidence required'
    for row in independent['stable_files']:
        check_binding(row)
    assert set(pin['evidence_bindings']) == {'source_graph','reachable_closure','complete_theorem_types','whole_definition_values','Std3','actual_findOLean','boundaries'}
    for rows in pin['evidence_bindings'].values():
        assert rows
        for row in rows:
            check_binding(row)
    return dict(status='ROOT_PIN_AND_ALL_SOURCE_EVIDENCE_REHASHED',
                independent_report_sha256=independent_binding['sha256'], API_calls=0, Lean_calls=0)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-root-pin', type=Path)
    args = parser.parse_args()
    if args.check_root_pin:
        print(json.dumps(require_root_pin(args.check_root_pin)))
        return
    assert not (OUT / 'prepared-publication-v2.json').exists(), 'Preserve an existing preparation'
    doc_bindings = docs_gate()
    author_path = PF / 'author-audit.json'
    assert sha(author_path) == AUTHOR
    author = load(author_path)
    assert author['verdict'] == 'PASS' and len(author['checks']) == 24 and all(positive(c) for c in author['checks'])
    assert len(author['stable_files']) == 1441 and len(author['seven_payloads']) == 7
    plan = load(PF / 'target-plan.json')
    requests = load(PF / 'problems-request.json')
    assert requests['env'] == ENV and requests['private'] is False
    assert len(plan['targets']) == len(requests['problems']) == 3
    payloads = []
    bound = {str(bound_path(r)): r for r in author['stable_files']}
    for relative, (size, expected) in EXPECTED_PAYLOADS.items():
        source = PF / 'staged' / relative
        raw = source.read_bytes()
        assert len(raw) == size and sha(source) == expected
        assert str(source.resolve()) in bound and bound[str(source.resolve())]['sha256'] == expected
        assert raw.decode('utf-8').encode('utf-8') == raw
        target = OUT / 'payloads' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        assert target.read_bytes() == raw
        payloads.append(dict(local_path=relative, bytes=size, sha256=expected,
                             staged_source=binding(source), publication_source_copy=binding(target)))
    for item, target in zip(requests['problems'], plan['targets']):
        assert item['theorem_name'] == target['theorem_name']
        reference = PF / 'staged' / target['local_reference']
        assert reference.read_bytes().decode('utf-8') == item['preamble'] + '\n' + item['formal_statement'] + '\n'
        code = (PF / 'staged' / target['local_solution']).read_bytes().decode('utf-8')
        assert re.search(r'(?m)^theorem solution\b', code)
        assert not re.search(r'(?m)^import (Theorems|Solutions)\.', code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', code)
    assert collections.Counter(x['kind'] for x in author['actual_native_records']) == {
        'definition_full_expression':11,'proof_full_type':34,'generated_helper_full_type':1}
    for records in [author['actual_native_records']] + list(author['actual_staged_records'].values()):
        for record in records:
            if 'axioms' in record:
                assert set(record['axioms']) <= STANDARD
    comparisons = author['comparisons']
    assert len(comparisons) == 3
    for row in comparisons:
        assert all(row[k] == v for k,v in {
            'definition_full_type_value_equal':11, 'native_named_proof_full_types_equal':34,
            'solution_full_type_equal':1, 'generated_helpers_equal':1,
            'full_definition_Expr_equal_and_kernel_equal':5, 'whole_function_rfl':5,
            'exact_forall_proofs':3, 'actual_full_type_kernel_equal':4,
            'closed_boundary_types_equal':9}.items())
        assert row['all_private_helpers_covered'] is True
    metadata = load(OUT / 'publication-metadata-v2.json')
    definition = metadata['definition']
    definition_code = (PF / 'staged' / plan['local_definition']).read_bytes().decode('utf-8')
    definition_payload = dict(definition_name=plan['definition'], env=ENV, private=False,
                              definition=definition_code, **definition)
    jobs = [('01-definition', '/submit-definition', definition_payload)]
    for i, item in enumerate(requests['problems'], 2):
        prose = metadata['problems'][item['theorem_name']]
        prepared = {**item, 'natural_language_statement':prose['natural_language_statement']}
        jobs.append((str(i).zfill(2)+'-problem-'+item['theorem_name'].split('.')[-1], '/submit-problem',
                     dict(env=ENV, private=False, problems=[prepared])))
    business_posts = []
    for key, endpoint, value in jobs:
        path = OUT / 'requests-v2' / (key + '.json')
        path.parent.mkdir(parents=True, exist_ok=True)
        # Match the existing official Client.call JSON encoding exactly; no newline/BOM.
        path.write_bytes(json.dumps(value, ensure_ascii=False).encode('utf-8'))
        business_posts.append(dict(operation=key, method='POST', endpoint=endpoint,
                                   wire_JSON_body=binding(path), automatically_retried=False))
    for target in plan['targets']:
        item = metadata['problems'][target['theorem_name']]
        path = OUT / 'proof-explanations-v2' / (target['theorem_name'].split('.')[-1] + '.md')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(item['explanation'].encode('utf-8'))
        business_posts.append(dict(operation='prove-'+target['theorem_name'], method='POST', endpoint='/verify',
            theorem_id='FROM_EXACT_PUBLISHED_CANONICAL_READBACK_NOT_YET_AVAILABLE', proof_type='prove',
            file_source=binding(OUT/'payloads'/target['local_solution']), explanation=binding(path),
            multipart_body='Build and persist exact bytes before intent journal; no env field', automatically_retried=False))
    extract = dict(author_report=binding(author_path), report_role=author['role'], checks=len(author['checks']),
        stable_files_count=len(author['stable_files']), native_records=46,
        staged_record_kinds={k:dict(collections.Counter(x['kind'] for x in v)) for k,v in author['actual_staged_records'].items()},
        comparisons=comparisons, actual_Std3_reports=author['actual_axiom_records'],
        native_source_bindings=[r for r in author['stable_files'] if
            str(r.get('task_relative') or r.get('root_relative') or '').endswith('CoefficientMapNumeratorPartialFractions.lean')],
        reachable_SOURCE_and_actual_receipt_bindings=[r for r in author['stable_files'] if
            'reachable' in str(r.get('task_relative') or r.get('root_relative') or '').lower()],
        independent_platform_report_hash=None, independent_platform_PASS_claimed=False)
    dump(OUT / 'author-evidence-contract-v2.json', extract)
    prepared = dict(status='PURE_PREPARATION_WAITING_FOR_ROOT_INDEPENDENT_PIN_NOT_PUBLICATION_PASS',
        new_proposal_id=NEW_PROPOSAL, requested_title=TITLE, NFKC_exact_title=unicodedata.normalize('NFKC',TITLE),
        proposal_mutation_permitted=False, mission_link_permitted=False, old_mission_write_permitted=False,
        environment=ENV, Lean_toolchain='leanprover/lean4:v4.33.1', native_source_sha256=SOURCE,
        platform_author_sha256=AUTHOR, seven_payloads=payloads, docs_pins=doc_bindings,
        business_posts=business_posts, target_plan=binding(PF/'target-plan.json'),
        original_problems_request=binding(PF/'problems-request.json'), metadata=binding(OUT/'publication-metadata-v2.json'),
        original_official_client=binding(TASK/'scripts/publish_mission_2026_10_02.py'),
        existing_Matrix_transaction_SOURCE=binding(TASK/'scripts/publish_matrix_proofs_new_mission_2026_10_07.py'),
        author_evidence_contract=binding(OUT/'author-evidence-contract-v2.json'),
        future_Root_independent_pin_required=True, independent_report_sha256=None,
        API_calls=0, Lean_calls=0, Root_module_installations=0, credentials_read=False,
        frozen_proposal_checkpoint=dict(reference_items=88, definitions=18, milestones=69,
            supporting_Proved=67, saved_complete_proof_receipts=54),
        after_all_three_global_ACCEPTED=dict(global_saved_complete_proof_receipts=57,
            new_PF_Accepted_but_not_referenced=3, proposal_counts_unchanged=True))
    dump(OUT / 'prepared-publication-v2.json', prepared)
    print(json.dumps(dict(status=prepared['status'], seven_payloads=7,
        business_POSTs_planned=7, prepared_publication_sha256=sha(OUT/'prepared-publication-v2.json'),
        independent_report_sha256=None, API_calls=0, Lean_calls=0)))


if __name__ == '__main__':
    main()

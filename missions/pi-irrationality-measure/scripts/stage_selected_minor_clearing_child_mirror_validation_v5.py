"""Freeze a read-only v5 derivation ledger over the unchanged v4 mirror contexts."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_selected_minor_clearing_child_mirror_probe_v4 as v4
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
TASK, STAGE = v4.TASK, v4.V / 'ap16/clearing-child-mirror-validation-v5'
CONSUMER = TASK / 'scripts/certify_selected_minor_clearing_child_mirror_validation_v5.py'
FROZEN_V4_CONSUMER = TASK / 'scripts/certify_selected_minor_clearing_child_mirror_probe_v4.py'
LEDGER = STAGE / 'derivation-ledger.json'
CERTIFICATE = 'local-child-validation.json'
AUTO_HELPER = 'OAI.PiExponent.InterpolationMatrix.matrix._proof_1'
read, sha, encode, need, rel = v4.read, v4.sha, v4.encode, v4.need, v4.rel


def ledger():
    v4.check_only()
    failed = v4.STAGE / 'failed-strict-consumer-record.json'
    failure = read(failed)
    need(failure['actual_exit_code'] == 1
         and failure['observed_error'] ==
             'ValueError: Auxiliary data equation uses an uncertified project constant'
         and failure['complete_uncovered_project_references'] == {
             'OAI.PiExponent.InterpolationMatrix.matrix.eq_1': [AUTO_HELPER]}
         and failure['certificate_written'] is False,
         'Preserved genuine v4 strict failure is not the single actual automatic CI')
    need(sha(FROZEN_V4_CONSUMER) ==
         'fbad9ab9f271cdd05b4cfe3b61dd2704d6b83421aae1020e1814faf464b4136d',
         'Frozen failed v4 consumer changed')
    for path, digest in failure['inputs'].items():
        need(sha(TASK / path) == digest, 'Exact failed v4 input changed: ' + path)
    source_record = read(v4.parent.STAGE / v4.parent.CERTIFICATE)
    source_pf = source_record['preflights'][v4.parent.SOURCE_SNAPSHOT]
    emitter = context.record(v4.EMITTER_STAGE / v4.OUTPUT,
                             v4.EMITTER_STAGE / 'c1.json', 'emit-olean',
                             v4.MODULE, v4.EMITTER_STAGE)
    generated = context.record(v4.STAGE / v4.SNAPSHOT,
                               v4.STAGE / 'c2.json', 'modecheck',
                               'GeneratedSnapshot', v4.STAGE)
    need(emitter['data']['success'] is True and generated['data']['success'] is True
         and generated['data'].get('runner') == rel(v4.RUNNER)
         and generated['data'].get('cleanup_completed') is True
         and emitter['data']['output_olean_sha256'] == v4.EXPECTED_OLEAN,
         'Reused actual bounded v4 contexts or unchanged OLean differ')
    source_doc = read(v4.parent.STAGE / v4.parent.SOURCE_REFS_JSON)
    generated_doc = read(v4.STAGE / v4.REFS_JSON)
    source = [r for r in source_doc['rows'] if r['name'] == AUTO_HELPER]
    target = [r for r in generated_doc['rows'] if r['name'] == AUTO_HELPER]
    need(len(source) == len(target) == 1,
         'The actual automatic helper is absent or duplicated in source/generated CI')
    matrix = next(r for r in v4.primary_evidence()[0]
                  if r['name'] == 'OAI.PiExponent.InterpolationMatrix.matrix')
    paths = [SELF, CONSUMER, FROZEN_V4_CONSUMER, v4.SELF,
             v4.STAGE / 'preparation.json', v4.STAGE / 'c2.json',
             v4.STAGE / v4.SNAPSHOT,
             (v4.STAGE / v4.SNAPSHOT).with_suffix('.lean.preflight.json'),
             v4.STAGE / v4.TYPE_JSON, v4.STAGE / v4.REFS_JSON,
             v4.STAGE / v4.MAPPING_JSON,
             v4.STAGE / 'generated-equation-1.json',
             v4.STAGE / 'generated-equation-2.json', failed,
             v4.EMITTER_STAGE / v4.OUTPUT,
             v4.EMITTER_STAGE / 'c1.json',
             (v4.EMITTER_STAGE / v4.OUTPUT).with_suffix('.lean.preflight.json'),
             v4.ACCEPTED, v4.parent.STAGE / v4.parent.CERTIFICATE,
             v4.parent.STAGE / v4.parent.SOURCE_REFS_JSON,
             v4.parent.STAGE / v4.parent.SOURCE_TYPE_JSON,
             TASK / matrix['certificate'], TASK / matrix['publication'],
             v4.RUNNER, v4.LEGACY_RUNNER,
             context.file(emitter['data']['output_olean'])]
    pins = {rel(path): sha(path) for path in paths}
    return {'schema_version': 1,
            'artifact_kind': 'ap16-private-clearing-child-v5-pure-derivation-ledger',
            'source_name': v4.parent.TARGET, 'platform_module': v4.MODULE,
            'public_platform_boundary_names': [v4.parent.TARGET],
            'exact_automatic_helper_name': AUTO_HELPER,
            'source_helper_owner': source[0]['owner'],
            'generated_helper_owner': target[0]['owner'],
            'source_helper_CI_sha256': v4.sha_bytes(encode(source[0])),
            'generated_helper_CI_sha256': v4.sha_bytes(encode(target[0])),
            'source_snapshot_preflight': source_pf['data']['source'],
            'v4_actual_emitter_record': emitter['record'],
            'v4_actual_generated_record': generated['record'],
            'v4_actual_emitter_olean_sha256': v4.EXPECTED_OLEAN,
            'frozen_v4_failure_record': rel(failed),
            'frozen_v4_failure_record_sha256': sha(failed),
            'original_AP10_matrix_complete_Def_certificate_sha256': matrix['certificate_sha256'],
            'published_AP10_matrix_definition_sha256': matrix['publication_sha256'],
            'input_hashes': dict(sorted(pins.items())),
            'new_Lean_files': [], 'Lean_started': False,
            'API_used': False, 'validated': False, 'submission_ready': False,
            'proposal_status': 'Draft'}


def check_only():
    raw = encode(ledger())
    need(LEDGER.is_file() and LEDGER.read_bytes() == raw,
         'Immutable derived v5 ledger differs')
    return {'ledger': rel(LEDGER), 'ledger_sha256': sha(LEDGER),
            'reused_actual_v4_contexts': True, 'new_Lean_files': [],
            'Lean_started': False, 'API_used': False, 'validated': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare', action='store_true')
    g.add_argument('--check-only', action='store_true')
    a = p.parse_args()
    if a.prepare:
        raw = encode(ledger())
        if LEDGER.exists():
            need(LEDGER.read_bytes() == raw, 'Refusing overwrite derived v5 ledger')
        else:
            LEDGER.parent.mkdir(parents=True, exist_ok=True)
            LEDGER.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()

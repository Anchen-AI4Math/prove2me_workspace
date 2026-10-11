"""Publish either complete, kernel-certified ap2 provider; proposals stay Draft.

Preparation does a fresh full read-only kernel/lineage replay. Subsequent polls
only read already submitted immutable payloads and GET the known server job.
They cannot create a new POST or substitute a different source payload.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

import admissible_provider_manifest_bridge as bridge
import replay_admissible_provider_windows as windows_replay
import complete_admissible_provider as complete
import stage_admissible_provider as stage
import generate_shared_source_snapshot as base
from publish_context_provider_bundle import TASK, ROOT, ENV, COMMIT, read, sha, encode, save_preserving

NAMES = {'WeightSeparation': stage.WEIGHT, 'AdmissibleParameters': stage.ADMISSIBLE}
API_SHA = '4b525b2dc18f5f2bdbaba57eab1089ab4a6308644c625343df1e0d2444065d38'


def require(value, message):
    if not value:
        raise ValueError(message)


def publication_stage(key):
    require(key in NAMES, 'Unsupported provider')
    return stage.DEST / 'publication' / ('Def_' + NAMES[key].replace('.', '_'))


def prepare(key):
    replay = windows_replay.validate()
    cert_path = TASK / replay['certificate']
    certificate = read(cert_path)
    require(certificate['validated'] is True and certificate['source_commit'] == COMMIT,
            'Complete source/kernel certificate required')
    for field in ['types_equal', 'full_definition_values_equal', 'Std3_only',
                  'theorem_values_null', 'complete_inductive_constructor_recursor_metadata_equal',
                  'recursor_rules_full_rhs_equal', 'full_provider_ci_domains_checked']:
        require(certificate.get(field) is True, 'Incomplete kernel comparison: ' + field)
    require(certificate['admissible_provider_rows'] == 58 and certificate['weight_provider_rows'] == 4,
            'Unexpected complete CI domains')
    module = NAMES[key]
    manifest_path, manifest = complete.provider_paths(module)
    entry = certificate['provider_manifests'][module]
    names = entry['declarations']
    require(len(names) == len(set(names)) == (4 if key == 'WeightSeparation' else 58),
            'Incomplete provider declaration domain')
    require(entry['sha256'] == sha(manifest_path) and entry['path'] == base.task_relative(manifest_path)
            and entry['platform_module'] == manifest['platform_module'], 'Manifest certificate differs')
    source_path = (ROOT / manifest['output']).resolve()
    require(source_path.is_relative_to((stage.DEST / 's/Definitions').resolve()), 'Unexpected source path')
    raw = source_path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == entry['source_sha256'] == manifest['output_sha256'], 'Certified source changed')
    name = module.replace('.', '_')
    require(manifest['platform_module'] == 'Definitions.Def_' + name, 'Definition name/module differs')
    metadata_path = TASK / 'platform/admissible-provider-metadata' / (key + '.json')
    metadata = read(metadata_path)
    require(set(metadata['declarations']) == set(names) and len(metadata['declarations']) == len(names),
            'Metadata declaration domain differs')
    for field in ['definition_title', 'natural_language_statement', 'explanation']:
        require(isinstance(metadata.get(field), str) and metadata[field].strip(), 'Missing metadata: ' + field)
    require('openai-pi-exponent-017' in metadata.get('tags', []), 'Missing source provenance tag')
    plan_path = TASK / manifest['provider_plan']
    require(sha(plan_path) == manifest['provider_plan_sha256'], 'Source unit plan changed')
    units = {row['id']: row for row in read(plan_path)['units']}
    selected = [units[key] for key in manifest['selected_units']]
    start, end = min(r['start']['line'] for r in selected), max(r['end']['line'] for r in selected)
    url = f'https://github.com/openai/math/blob/{COMMIT}/lean/{module.replace(".", "/")}.lean#L{start}-L{end}'
    metadata = dict(metadata, source=f'OpenAI math, commit {COMMIT}: {url}', source_commit=COMMIT,
                    source_module=module, platform_module=manifest['platform_module'],
                    selected_source_units=[dict(id=r['id'], start_line=r['start']['line'],
                                                end_line=r['end']['line']) for r in selected])
    payload = dict(definition_name=name, definition_title=metadata['definition_title'],
                   definition=raw.decode('utf-8'), natural_language_statement=metadata['natural_language_statement'],
                   source=metadata['source'], tags=metadata['tags'], env=ENV, private=False)
    wire = json.dumps(payload, ensure_ascii=False).encode('utf-8')
    digest_wire = hashlib.sha256(wire).hexdigest()
    prep = dict(schema_version=1, prepared_at_utc=datetime.now(timezone.utc).isoformat(),
                publisher_script_sha256=sha(Path(__file__)), offline_prepare_only=True,
                definition_name=name, definition_module=manifest['platform_module'],
                environment=ENV, visibility='public', mission_proposal_status='Draft',
                metadata_input_sha256=sha(metadata_path), payload_sha256=digest_wire,
                wire_body_sha256=digest_wire, bundle_source_sha256=digest,
                bundle_manifest_sha256=sha(manifest_path), validation_sha256=sha(cert_path),
                uploaded_definition_bytes=len(raw), kernel_comparison_declarations=names,
                complete_kernel_replay=replay, manifest_bridge_sha256=sha(stage.DEST / 'manifest-bridge.json'),
                consumer_sha256=sha(Path(complete.__file__)), adapter_sha256=sha(Path(bridge.__file__)),
                windows_adapter_sha256=sha(Path(windows_replay.__file__)),
                source_scope_partial=True, full_platform_dependency_closure_complete=False)
    directory = publication_stage(key)
    directory.mkdir(parents=True, exist_ok=True)
    record_path = directory / 'publication.json'
    if record_path.exists():
        prior = read(record_path)
        require(not prior.get('publish_intent') and not prior.get('job_id') and not prior.get('definition_id'),
                'Publication already started; use --poll to avoid another full preparation or POST')
    for filename, data in [('metadata.json', encode(metadata)), ('publish-payload.json', wire),
                           ('prepare-record.json', encode(prep))]:
        save_preserving(directory / filename, data)
    return directory, metadata, payload, prep


def known_job(key):
    directory = publication_stage(key)
    metadata, payload, prep, record = [read(directory / p) for p in
                                     ['metadata.json', 'publish-payload.json', 'prepare-record.json', 'publication.json']]
    require(record.get('publish_intent') and record.get('job_id'), 'GET-only polling requires a known prior POST/job')
    require(payload['definition_name'] == NAMES[key].replace('.', '_') == prep['definition_name']
            and payload['env'] == ENV and payload['private'] is False, 'Saved publication identity differs')
    require(sha(directory / 'publish-payload.json') == prep['wire_body_sha256'] == prep['payload_sha256']
            == record['publish_payload_sha256'], 'Saved wire payload changed')
    require(record['publish_intent']['payload'] == payload, 'Prior POST payload differs')
    require(prep['publisher_script_sha256'] == sha(Path(__file__))
            and prep['consumer_sha256'] == sha(Path(complete.__file__))
            and prep['adapter_sha256'] == sha(Path(bridge.__file__))
            and prep['windows_adapter_sha256'] == sha(Path(windows_replay.__file__)), 'Frozen publisher/consumer changed')
    cert_path = stage.DEST / 'complete-validation.json'
    manifest_path, manifest = complete.provider_paths(NAMES[key])
    require(sha(cert_path) == prep['validation_sha256']
            and sha(manifest_path) == prep['bundle_manifest_sha256']
            and sha(ROOT / manifest['output']) == prep['bundle_source_sha256'], 'Published source evidence changed')
    require(hashlib.sha256(payload['definition'].encode()).hexdigest() == prep['bundle_source_sha256'],
            'Payload is not the certified source bytes')
    return directory, metadata, payload, prep


def advance(saved):
    api_path = TASK / 'scripts/publish_closed_definition_bundle.py'
    require(sha(api_path) == API_SHA, 'Frozen at-most-once definition API publisher changed')
    spec = importlib.util.spec_from_file_location('ap2_definition_api', api_path)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    return api.advance(*saved)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('provider', choices=NAMES)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--prepare-and-advance', action='store_true')
    mode.add_argument('--poll', action='store_true')
    args = parser.parse_args()
    saved = known_job(args.provider) if args.poll else prepare(args.provider)
    if args.poll or args.prepare_and_advance:
        record = advance(saved)
        result = dict(advanced=True, definition_name=saved[2]['definition_name'],
                      job_id=record.get('job_id'), definition_id=record.get('definition_id'),
                      status=record.get('last_publish_verdict', {}).get('body', {}).get('status'))
    else:
        result = dict(prepared_offline=True, payload_sha256=saved[3]['payload_sha256'])
    print(json.dumps(result, ensure_ascii=True))


if __name__ == '__main__':
    main()

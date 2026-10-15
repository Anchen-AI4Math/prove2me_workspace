"""Pure offline publication preparation for the original AP20 collision limit."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_collision_remainder_limit_node_v2 as consumer
import stage_collision_remainder_limit_node_v2 as stage

TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
SELF = Path(__file__).resolve()
ONLINE = TASK / 'scripts/publish_collision_remainder_limit_node.py'
DEST = STAGE / 'publication'
CERT = STAGE / stage.CERTIFICATE
LOOKUP = stage.V / 'ap20/exact-new-analytic-and-collision-name-lookup.json'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
API = ROOT / 'scripts/p2m_api.py'
API_REVIEW = stage.V / 'api-review-20261011-v0.12.4/manifest.json'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding='utf-8'))
def encode(value): return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode()


def resolve(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def exact(path, raw):
    if path.exists():
        need(path.read_bytes() == raw, 'Frozen publication artifact differs: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def static():
    stage.check_only()
    prep = read(STAGE / 'preparation.json')
    need(prep['artifact_kind'] == 'ap20-collision-remainder-literal-proof-preparation'
         and prep['source_name'] == stage.TARGET and prep['platform_name'] == stage.TARGET
         and prep['source_commit'] == stage.route.data.COMMIT
         and prep['source_line_count'] == 15 and len(prep['exact_source_units']) == 2
         and prep['original_proof_suffixes_unchanged'] is True
         and prep['proposal_status'] == 'Draft' and prep['validated'] is False,
         'Original 2-AST proof preparation differs')
    lookup = read(LOOKUP)
    rows = [x for x in lookup['records'] if x['theorem_name'] == stage.TARGET]
    need(lookup['environment'] == ENV and lookup['read_only'] is True
         and len(rows) == 1 and rows[0]['environment'] == ENV
         and rows[0]['lookup_total'] == 0 and rows[0]['matches'] == []
         and len(rows[0]['pages']) == 1
         and rows[0]['pages'][0]['parsed_body'] == {'theorems': [], 'total': 0}
         and digest(rows[0]['pages'][0]['raw_body_utf8'].encode()) == rows[0]['pages'][0]['raw_body_sha256'],
         'Saved actual exact-name query is not the genuine zero-match predecessor')
    preamble = (stage.ROUTE / 'candidate/preamble.lean').read_bytes()
    formal = (stage.ROUTE / 'candidate/formal-statement.lean').read_bytes()
    theorem = (STAGE / stage.TARGET_OUTPUT).read_bytes()
    solution = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    need(theorem == preamble + formal == (STAGE / 'wire-theorem-source.lean').read_bytes()
         and b'sorry' in formal and b'sorry' not in solution
         and b'theorem solution ' in solution and solution.count(b'theorem solution ') == 1,
         'Exact comparator/closed global solution wire differs')
    source = read(STAGE / 'academic-metadata.json')
    need(set(source) == {'theorem_title', 'natural_language_statement', 'source', 'tags'}
         and source['source'].startswith('https://github.com/openai/math/blob/' + prep['source_commit']),
         'Original source academic metadata differs')
    problem = {'theorem_name': stage.TARGET, 'theorem_title': source['theorem_title'],
               'natural_language_statement': source['natural_language_statement'],
               'preamble': preamble.decode(), 'formal_statement': formal.decode(),
               'source': source['source'], 'tags': source['tags']}
    publish = {'problems': [problem], 'env': ENV, 'private': False}
    verify = {'env': ENV, 'proof_type': 'prove',
              'target_theorem_name': stage.TARGET, 'theorem_id': None,
              'theorem_id_binding': 'exact public theorem name/environment/preamble/formal_statement readback',
              'explanation': 'Apply the accepted normalized logarithm limit and the original log-add helper, then unfold the original collision remainder and close the algebraic identity.',
              'file': {'filename': Path(stage.SOLUTION_OUTPUT).name,
                       'source': stage.ws(STAGE / stage.SOLUTION_OUTPUT),
                       'sha256': sha(STAGE / stage.SOLUTION_OUTPUT),
                       'utf8': solution.decode()}}
    manifest = {'schema_version': 1, 'artifact_kind': 'ap20-collision-remainder-proof-publication-manifest',
                'theorem_name': stage.TARGET, 'environment': ENV, 'visibility': 'public',
                'preamble': problem['preamble'], 'formal_statement': problem['formal_statement'],
                'statement': stage.ws(STAGE / stage.TARGET_OUTPUT), 'statement_sha256': sha(STAGE / stage.TARGET_OUTPUT),
                'solution': stage.ws(STAGE / stage.SOLUTION_OUTPUT), 'solution_sha256': sha(STAGE / stage.SOLUTION_OUTPUT),
                'source_commit': prep['source_commit'], 'source_units': prep['exact_source_units'],
                'original_AST_units': 2, 'original_source_lines': 15,
                'source_only_route_sha256': sha(stage.ROUTE / 'route-preparation.json'),
                'prior_exact_name_lookup_sha256': sha(LOOKUP),
                'certificate': stage.ws(CERT), 'validated': CERT.is_file(),
                'proposal_status': 'Draft', 'submission_ready': False}
    return prep, manifest, source, publish, verify


def historical(cert):
    artifacts = {}
    deps = {}
    for witness in cert['preflights'].values():
        data = witness['data']
        need(sha(resolve(witness['record'])) == witness['record_sha256'], 'Compiler record changed')
        need(data['source_unchanged'] is True
             and data['source_sha256_before'] == data['source_sha256_after'] == sha(resolve(data['source']))
             and data['manifest_unchanged'] is True
             and data['manifest_sha256_before'] == data['manifest_sha256_after'] == sha(resolve(data['manifest']))
             and data['log_sha256'] == data['stdout_and_stderr_sha256'] == sha(resolve(data['log'])),
             'Historical source/manifest/log before-after witness differs')
        artifacts[witness['record']] = witness['record_sha256']
        for field, key in [('source', 'source_sha256_before'), ('manifest', 'manifest_sha256_before'),
                           ('log', 'log_sha256')]:
            artifacts[data[field]] = data[key]
        for dep in data['dependency_oleans']:
            need(dep['stable_during_compile'] is True
                 and dep['sha256_before'] == dep['sha256_after'] == sha(Path(dep['path'])),
                 'Historical imported OLean changed')
            deps[dep['path']] = dep['sha256_before']
        if data['output_olean']:
            need(sha(resolve(data['output_olean'])) == data['output_olean_sha256'],
                 'Emitted proof OLean changed')
            deps[data['output_olean']] = data['output_olean_sha256']
    return dict(sorted(artifacts.items())), dict(sorted(deps.items()))


def prepare():
    need(CERT.is_file(), 'Four actual contexts and strict closed-proof certificate are pending')
    prep, manifest, metadata, publish, verify = static()
    cert = read(CERT)
    replay = consumer.validate()
    need(cert == replay and CERT.read_bytes() == stage.encode(replay)
         and cert['validated'] is True and cert['Std3_only'] is True
         and cert['closed_global_solution'] is True
         and cert['raw_owned_inventory_exact'] is True
         and cert['source_and_generated_full_types_equal'] is True
         and cert['source_and_generated_actual_proof_references_paired'] is True
         and cert['literal_original_proof_suffixes'] is True,
         'Single complete strict replay differs from actual certificate')
    actual_seconds = [row['data']['seconds'] for row in cert['preflights'].values()]
    need(len(actual_seconds) == 4 and all(0 < seconds <= 300 for seconds in actual_seconds)
         and prep['submission_ready'] is False and prep['proposal_status'] == 'Draft'
         and prep['Lean_started'] is False and prep['API_used'] is False,
         'Actual compiler budget or Draft/pure consumer boundary differs')
    compiler_manifest_sha256 = {name: sha(STAGE / name) for name in stage.MANIFESTS}
    artifacts, deps = historical(cert)
    pin_files = {stage.rel(p): sha(p) for p in [SELF, ONLINE, API, API_REVIEW,
        Path(stage.__file__), Path(consumer.__file__), CERT, LOOKUP,
        STAGE / 'preparation.json', STAGE / stage.TARGET_OUTPUT,
        STAGE / stage.SOLUTION_OUTPUT, STAGE / 'academic-metadata.json',
        STAGE / 'wire-theorem-source.lean', stage.ROUTE / 'candidate/preamble.lean',
        stage.ROUTE / 'candidate/formal-statement.lean'] if p.resolve().is_relative_to(TASK.resolve())}
    pin_files[str(API)] = sha(API)
    api_review = read(API_REVIEW)
    need(api_review['official_tag'] == 'v0.12.4'
         and api_review['official_commit'] == '78989800ba0b3149ee34205257025bd0f617e8ef',
         'Official reviewed API version differs')
    for row in api_review['documents']:
        document = API_REVIEW.parent / row['name']
        need(sha(document) == row['sha256'], 'Official reviewed API document changed')
        pin_files[stage.rel(document)] = row['sha256']
    pin_files.update(prep['input_hashes'])
    pin_files.update({stage.rel(STAGE / name): expected
                      for name, expected in cert['generated_json_sha256'].items()})
    pin_files.update(cert['implementation_hashes'])
    pin_files.update(artifacts)
    for path, expected in pin_files.items():
        need(sha(resolve(path)) == expected, 'Frozen publication input differs: ' + path)
    payloads = {'publish-payload.json': encode(publish),
                'verification-payload.json': encode(verify)}
    pins = {'schema_version': 1, 'artifact_kind': 'ap20-collision-remainder-frozen-publication',
            'theorem_name': stage.TARGET, 'environment': ENV, 'visibility': 'public',
            'offline_wrapper_sha256': sha(SELF), 'online_wrapper_sha256': sha(ONLINE),
            'stage_preparation_sha256': sha(STAGE / 'preparation.json'),
            'validation_sha256': sha(CERT), 'manifest_sha256': digest(encode(manifest)),
            'metadata_sha256': digest(encode(metadata)),
            'payload_sha256': {name: digest(raw) for name, raw in payloads.items()},
            'actual_solution_olean_sha256': cert['solution_olean_sha256'],
            'historical_and_input_hashes': dict(sorted(pin_files.items())),
            'historical_dependency_olean_hashes': deps,
            'actual_max_file_seconds': max(actual_seconds),
            'compiler_manifest_sha256': compiler_manifest_sha256,
            'certification_semantics': {
                'validated': True, 'Std3_only': True, 'closed_global_solution': True,
                'submission_ready': False, 'proposal_status': 'Draft',
                'Lean_started_by_consumer': False, 'API_used': False},
            'one_complete_strict_replay_performed': True,
            'subsequent_HTTP_guards_hash_only': True, 'proposal_status': 'Draft',
            'submission_ready': False, 'API_used': False}
    exact(DEST / 'manifest.json', encode(manifest))
    exact(DEST / 'metadata.json', encode(metadata))
    exact(DEST / 'validation.json', CERT.read_bytes())
    exact(DEST / 'wire-theorem-source.lean', (STAGE / 'wire-theorem-source.lean').read_bytes())
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / 'preparation.json', encode(pins))
    return {'prepared': True, 'network_used': False, 'strict_replay_count': 1,
            'theorem_name': stage.TARGET, 'proposal_status': 'Draft'}


def frozen():
    pins = read(DEST / 'preparation.json')
    need(sha(SELF) == pins['offline_wrapper_sha256'] and sha(ONLINE) == pins['online_wrapper_sha256']
         and sha(STAGE / 'preparation.json') == pins['stage_preparation_sha256']
         and sha(CERT) == pins['validation_sha256'], 'Frozen publication implementation changed')
    for path, expected in pins['historical_and_input_hashes'].items():
        need(sha(resolve(path)) == expected, 'Frozen publication input changed: ' + path)
    for path, expected in pins['historical_dependency_olean_hashes'].items():
        need(sha(Path(path)) == expected, 'Frozen imported OLean changed: ' + path)
    need(all(sha(STAGE / name) == expected
             for name, expected in pins['compiler_manifest_sha256'].items())
         and 0 < pins['actual_max_file_seconds'] <= 300
         and pins['certification_semantics'] == {
             'validated': True, 'Std3_only': True, 'closed_global_solution': True,
             'submission_ready': False, 'proposal_status': 'Draft',
             'Lean_started_by_consumer': False, 'API_used': False},
         'Frozen actual bounded certification semantics changed')
    need(sha(DEST / 'manifest.json') == pins['manifest_sha256']
         and sha(DEST / 'metadata.json') == pins['metadata_sha256']
         and sha(DEST / 'validation.json') == pins['validation_sha256']
         and sha(DEST / 'wire-theorem-source.lean') == sha(STAGE / 'wire-theorem-source.lean')
         and all(sha(DEST / name) == value for name, value in pins['payload_sha256'].items()),
         'Frozen payload or public comparator changed')
    return read(DEST / 'manifest.json'), read(DEST / 'metadata.json'), {
        name: (DEST / name).read_bytes() for name in pins['payload_sha256']}, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare-only', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare_only:
        print(json.dumps(prepare(), ensure_ascii=False))
    else:
        frozen()
        print(json.dumps({'checked': True, 'network_used': False}, ensure_ascii=False))


if __name__ == '__main__':
    main()

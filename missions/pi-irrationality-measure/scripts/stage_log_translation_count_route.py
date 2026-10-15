"""Pure four-original-AST route to the translation-count logarithmic limit."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
STAGE = TASK / 'verification/ap20/log-translation-term-count-route-v2'
AST = TASK / 'verification/ast-unit-inventory.json'
SCOPES = TASK / 'verification/ast-scope-inventory.json'
PUBLISHED = TASK / 'verification/ap19/analytic-remainder-data/publication-v4/publication.json'
CERT = (TASK / 'verification/ap19/analytic-remainder-auto-ci-validation-v5/'
        'actual-provider-validation-auto-ci-v5.json')
LOGDIV_CERT = TASK / 'verification/ap19/log-div-child-mirror/local-child-validation.json'
COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
MODULE = 'Theorems.Thm_OAI_PiExponent_tendsto_log_translationTermCount_div'
TARGET = 'OAI.PiExponent.tendsto_log_translationTermCount_div'
SPECS = [
    ('OAI.PiExponent.tendsto_natFloor_affine_div',
     'OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor', 372, 1379),
    ('OAI.PiExponent.tendsto_natFloor_mul_add_one_div',
     'OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit', 313, 636),
    ('OAI.PiExponent.tendsto_translationTermCount_normalized',
     'OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit', 640, 1501),
    (TARGET, 'OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit', 1505, 1801),
]


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def need(cond: bool, message: str) -> None:
    if not cond:
        raise ValueError(message)


def source_units() -> tuple[list[tuple[bytes, dict]], dict]:
    ast = json.loads(AST.read_text(encoding='utf-8'))
    scopes = json.loads(SCOPES.read_text(encoding='utf-8'))
    units = []
    pins = [Path(__file__), AST, SCOPES]
    for name, module, start, end in SPECS:
        port = TASK / ('port/lean/' + module.replace('.', '/') + '.lean')
        source = TASK / ('source/lean/' + module.replace('.', '/') + '.lean')
        module_ast = next(m for m in ast['modules'] if m['module'] == module)
        module_scope = next(m for m in scopes['modules'] if m['source'] == module.replace('.', '/') + '.lean')
        unit = next(u for u in module_ast['units'] if u['graph_names'] == [name])
        scope = next(s for s in module_scope['declarations'] if s['verified_name'] == name)
        command = port.read_bytes()[start:end]
        value_start = unit['valueStart']['offset'] - start
        contexts = [port.read_bytes()[c['range']['start']['offset']:c['range']['end']['offset']].decode()
                    for c in scope['context_commands']]
        need([unit['start']['offset'], unit['end']['offset']] == [start, end]
             and unit['graph_kinds'] == ['theorem'] and unit['privateTok'] is None
             and module_ast['source_sha256'] == module_scope['source_sha256'] == sha(port.read_bytes())
             and source.read_bytes().replace(b'\r\n', b'\n').count(command.replace(b'\r\n', b'\n')) == 1
             and command[value_start:value_start + 2] == b':='
             and b'sorry' not in command
             and scope['namespace'] == 'OAI.PiExponent'
             and contexts == ['open Filter Topology'],
             'Original four-command AST/scope/proof/source differs: ' + name)
        units.append((command, {
            'name': name, 'module': module, 'source': rel(port), 'original': rel(source),
            'source_sha256': sha(port.read_bytes()),
            'original_sha256': sha(source.read_bytes()),
            'start': start, 'end': end,
            'source_lines': [unit['start']['line'], unit['end']['line']],
            'command_sha256': sha(command),
            'proof_suffix_sha256': sha(command[value_start:]),
            'value_start': value_start, 'ast': unit, 'scope': scope,
            'context_commands': contexts,
        }))
        pins += [port, source]
    publication = json.loads(PUBLISHED.read_text(encoding='utf-8'))
    cert = json.loads(CERT.read_text(encoding='utf-8'))
    logdiv = json.loads(LOGDIV_CERT.read_text(encoding='utf-8'))
    body = publication['target_readback']['body']
    need(publication['definition_id'] == '04008248-130e-40ba-b6a3-df3e9b9df91b'
         and publication['last_publish_verdict']['body']['status'] == 'PUBLISHED'
         and body['status'] == 'Definition' and body['visibility'] == 'public'
         and body['definition'] == publication['publish_intent']['payload']['definition']
         and body['deprecated_at'] is None
         and cert['validated'] is True and cert['Std3_only'] is True
         and 'OAI.PiExponent.translationTermCount' in cert['provided_names']
         and logdiv['validated'] is True and logdiv['Std3_only'] is True
         and logdiv['accepted_theorem_id'] == '8b1c0341-2978-4a9d-8acc-8a5e3538cbda',
         'Actual Published translation Definition or Accepted LogDiv boundary differs')
    pins += [PUBLISHED, CERT, LOGDIV_CERT]
    return units, {rel(p): sha(p.read_bytes()) for p in pins}


def files() -> dict[str, bytes]:
    units, pins = source_units()
    commands = [u[0] for u in units]
    names = [u[1]['name'] for u in units]
    need(names == [s[0] for s in SPECS] and
         commands[0].startswith(b'theorem tendsto_natFloor_affine_div') and
         commands[3].startswith(b'theorem tendsto_log_translationTermCount_div'),
         'Exact four theorem name tokens changed')
    local = [b'private ' + cmd for cmd in commands[:3]]
    target = commands[3]
    old = b'theorem tendsto_log_translationTermCount_div'
    solution = target.replace(old, b'theorem solution', 1)
    need(solution[len(b'theorem solution'):] == target[len(old):],
         'Original target proof changed beyond the global theorem name token')
    imports = (
        b'import Mathlib.Analysis.SpecialFunctions.Log.Basic\n'
        b'import Mathlib.Analysis.SpecificLimits.Normed\n'
        b'import Mathlib.Analysis.Asymptotics.SpecificAsymptotics\n'
        b'import Mathlib.Tactic\n'
        b'import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData\n'
        b'import Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow\n'
    )
    context = b'\nnamespace OAI\n\nopen Filter Topology\n\nnamespace PiExponent\n\n'
    global_context = (b'\nend PiExponent\n\nend OAI\n\n'
                      b'open Filter Topology\nopen OAI.PiExponent\n\n')
    sol = imports + context + b'\n\n'.join(local) + global_context + solution + b'\n'
    value_start = units[3][1]['value_start']
    formal = target[:value_start].replace(old, b'theorem ' + TARGET.encode(), 1) + b':= by\n  sorry\n'
    preamble = (imports.split(b'import Theorems.', 1)[0] +
                b'\nopen Filter Topology\nopen OAI.PiExponent\n\n')
    theorem = preamble + formal
    need(sol.count(b'private theorem ') == 3 and sol.count(b'theorem solution') == 1
         and b'sorry' not in sol and b'import Solutions.' not in sol,
         'Grouped closed candidate proof/visibility differs')
    outputs = {f'source-unit-{i}.lean.txt': cmd for i, cmd in enumerate(commands, 1)}
    outputs['candidate/Sol.lean.txt'] = sol
    outputs['candidate/Target-comparator.lean.txt'] = theorem
    outputs['candidate/preamble.lean.txt'] = preamble
    outputs['candidate/formal-statement.lean.txt'] = formal
    rows = [u[1] for u in units]
    outputs['route-preparation.json'] = (json.dumps({
        'schema_version': 1,
        'artifact_kind': 'ap20-four-original-AST-log-translation-count-closed-candidate',
        'source_commit': COMMIT, 'target': TARGET, 'platform_module': MODULE,
        'source_units': rows, 'original_source_lines': 42,
        'source_helpers_private_visibility_prefix_only': True,
        'target_source_proof_suffix_unchanged': True,
        'candidate_global_solution_name_only': True,
        'published_definition_name': 'OAI.PiExponent.translationTermCount',
        'published_definition_id': '04008248-130e-40ba-b6a3-df3e9b9df91b',
        'accepted_logdiv_theorem_id': '8b1c0341-2978-4a9d-8acc-8a5e3538cbda',
        'published_data_owned_automatic_CIs_for_translationTermCount': [],
        'comparator_is_sorry_placeholder': True,
        'closed_solution_candidate_not_compiled': True,
        'exact_name_lookup_pending': True,
        'compiler_manifests_emitted': False,
        'proposal_status': 'Draft', 'API_used': False, 'Lean_started_by_producer': False,
        'input_hashes': pins,
        'files': {name: sha(raw) for name, raw in outputs.items()},
    }, ensure_ascii=False, indent=2) + '\n').encode()
    return outputs


def check_only() -> dict:
    outputs = files()
    for name, raw in outputs.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Staged translation route bytes differ: ' + name)
    return {'files': len(outputs), 'exact_source_theorem_AST_units': 4,
            'original_source_lines': 42, 'candidate_closed_proof_compiled': False,
            'Lean_started_by_producer': False, 'API_used': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing staged source-route overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()

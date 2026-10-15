"""Pure source-only route for the exact analytic-remainder theorem proof."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
STAGE = TASK / 'verification/ap20/analytic-remainder-source-route'
AST = TASK / 'verification/ast-unit-inventory.json'
SCOPES = TASK / 'verification/ast-scope-inventory.json'
PARENT_WIRE = (TASK / 'verification/ap19/analytic-aggregate-two-child-reduction-final/'
               'publication-v3/child-readbacks/tendsto_analyticRemainder.json')
COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
SPECS = [
    ('OAI.PiExponent.DeterminantContradiction.finiteDenominators_two_le',
     'OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction', 1000, 1143),
    ('OAI.PiExponent.DeterminantContradiction.logWeights_eq',
     'OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction', 1147, 1317),
    ('OAI.PiExponent.LiteralAnalytic.fixedWeights_pos',
     'OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand', 2236, 2478),
    ('OAI.PiExponent.LiteralAnalytic.tendsto_analyticRemainder',
     'OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate', 3610, 4682),
]
DIRECT_OPEN_CHILDREN = [
    'OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized',
    'OAI.PiExponent.tendsto_log_translationTermCount_div',
]
ACCEPTED_CHILD = 'OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def need(cond: bool, reason: str) -> None:
    if not cond:
        raise ValueError(reason)


def files() -> dict[str, bytes]:
    ast = json.loads(AST.read_text(encoding='utf-8'))
    scopes = json.loads(SCOPES.read_text(encoding='utf-8'))
    wire = json.loads(PARENT_WIRE.read_text(encoding='utf-8'))
    need(wire['theorem_id'] == '3e3f6c16-7b23-4a33-be85-b7748629724e'
         and wire['theorem_name'] == SPECS[-1][0]
         and wire['status'] == 'Open'
         and wire['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
         and wire['visibility'] == 'public', 'Existing exact analytic child public wire changed')
    results = {}
    units = []
    input_paths = [Path(__file__), AST, SCOPES, PARENT_WIRE]
    for index, (name, module, start, end) in enumerate(SPECS, 1):
        source = TASK / ('port/lean/' + module.replace('.', '/') + '.lean')
        original = TASK / ('source/lean/' + module.replace('.', '/') + '.lean')
        ast_module = next(x for x in ast['modules'] if x['module'] == module)
        scope_module = next(x for x in scopes['modules'] if x['source'] == module.replace('.', '/') + '.lean')
        unit = next(x for x in ast_module['units'] if x['graph_names'] == [name])
        scope = next(x for x in scope_module['declarations'] if x['verified_name'] == name)
        raw = source.read_bytes()[start:end]
        need([unit['start']['offset'], unit['end']['offset']] == [start, end]
             and unit['graph_kinds'] == ['theorem']
             and unit['privateTok'] is None
             and ast_module['source_sha256'] == sha(source.read_bytes())
             and scope_module['source_sha256'] == sha(source.read_bytes())
             and original.read_bytes().replace(b'\r\n', b'\n').count(raw.replace(b'\r\n', b'\n')) == 1
             and b'sorry' not in raw and len(raw) > 0,
             'Original AST, scope, source bytes, or proof differs: ' + name)
        proof_start = unit['valueStart']['offset'] - start
        need(raw[proof_start:proof_start + 2] == b':=',
             'Original proof-value start differs: ' + name)
        contexts = [source.read_bytes()[c['range']['start']['offset']:
                                       c['range']['end']['offset']].decode('utf-8')
                    for c in scope['context_commands']]
        units.append({'name': name, 'module': module, 'source': rel(source),
                      'source_sha256': sha(source.read_bytes()),
                      'original': rel(original),
                      'original_sha256': sha(original.read_bytes()),
                      'start': start, 'end': end,
                      'source_lines': [unit['start']['line'], unit['end']['line']],
                      'command_sha256': sha(raw),
                      'proof_suffix_sha256': sha(raw[proof_start:]),
                      'scope': scope, 'ast': unit, 'context_commands': contexts})
        results[f'source-unit-{index}.lean.txt'] = raw
        input_paths += [source, original]
    target = results['source-unit-4.lean.txt']
    need(target.startswith(b'theorem tendsto_analyticRemainder')
         and b'MatrixCounting.tendsto_rowCount_normalized' in target
         and b'tendsto_collisionRemainder_of_normalized_pow' in target
         and b'tendsto_log_translationTermCount_div' in target
         and b'finiteDenominators_two_le' in target
         and b'fixedWeights_pos' in target,
         'Exact direct source proof references differ')
    results['candidate/source-command-bundle.lean.txt'] = (
        b'\n\n'.join(results[f'source-unit-{i}.lean.txt'] for i in range(1, 5)))
    metadata = {
        'schema_version': 1,
        'artifact_kind': 'ap20-source-faithful-analytic-remainder-route-only',
        'source_commit': COMMIT,
        'target': SPECS[-1][0],
        'existing_open_theorem_id': wire['theorem_id'],
        'existing_open_wire_sha256': sha((wire['preamble'] + wire['formal_statement']).encode()),
        'source_units': units,
        'groupable_source_helpers': [x[0] for x in SPECS[:3]],
        'direct_open_theorem_children_requiring_real_platform_interfaces': DIRECT_OPEN_CHILDREN,
        'accepted_collision_child': ACCEPTED_CHILD,
        'source_target_proof_unchanged': True,
        'source_helper_proof_suffixes_unchanged': True,
        'no_invented_normalized_actual_row_count_theorem': True,
        'closed_solution_claimed': False,
        'compiler_manifests_emitted': False,
        'proposal_status': 'Draft',
        'Lean_started_by_producer': False,
        'API_used': False,
        'input_hashes': {rel(p): sha(p.read_bytes()) for p in input_paths},
        'files': {name: sha(raw) for name, raw in results.items()},
    }
    results['route-preparation.json'] = (json.dumps(metadata, ensure_ascii=False, indent=2) + '\n').encode()
    return results


def check_only() -> dict:
    staged = files()
    for name, content in staged.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == content,
             'Source-only route file differs: ' + name)
    return {'files': len(staged), 'source_AST_units': 4,
            'direct_open_theorem_children': DIRECT_OPEN_CHILDREN,
            'closed_solution_claimed': False, 'Lean_started_by_producer': False,
            'API_used': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    x = parser.add_mutually_exclusive_group(required=True)
    x.add_argument('--prepare', action='store_true')
    x.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, content in files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == content, 'Refusing source-only route overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()

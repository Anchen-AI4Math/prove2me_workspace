"""Assemble a source-faithful grouped proof candidate; two theorem edges remain Open."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import stage_analytic_remainder_source_route as route

TASK = route.TASK
STAGE = TASK / 'verification/ap20/analytic-remainder-grouped-candidate'
SOURCE = route.STAGE
TARGET = route.SPECS[-1][0]
CHILDREN = route.DIRECT_OPEN_CHILDREN


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def assemble() -> tuple[bytes, dict]:
    route.check_only()
    data = json.loads((SOURCE / 'route-preparation.json').read_text(encoding='utf-8'))
    commands = [(SOURCE / f'source-unit-{i}.lean.txt').read_bytes() for i in range(1, 5)]
    for row, command in zip(data['source_units'], commands, strict=True):
        value_start = row['ast']['valueStart']['offset'] - row['start']
        if sha(command) != row['command_sha256'] or command[value_start:value_start + 2] != b':=':
            raise ValueError('Original source theorem AST command changed: ' + row['name'])
    helpers = [b'private ' + command for command in commands[:3]]
    target = commands[3]
    old = b'theorem tendsto_analyticRemainder'
    if not target.startswith(old) or target.count(old) != 1:
        raise ValueError('Original target theorem name token changed')
    global_solution = target.replace(old, b'theorem solution', 1)
    if global_solution[len(b'theorem solution'):] != target[len(old):]:
        raise ValueError('Original target proof suffix changed')
    body = (
        b'-- Source-faithful candidate only: two theorem imports below await real Open-child interfaces.\n'
        b'import Mathlib.Tactic\n'
        b'import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData\n'
        b'import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData\n'
        b'import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData\n'
        b'import Theorems.Thm_OAI_PiExponent_tendsto_collisionRemainder_of_normalized_pow\n'
        b'-- PENDING import Theorems.Thm_OAI_PiExponent_MatrixCounting_tendsto_rowCount_normalized\n'
        b'-- PENDING import Theorems.Thm_OAI_PiExponent_tendsto_log_translationTermCount_div\n\n'
        b'namespace OAI\n\nopen Filter\nopen scoped Topology\n\n'
        b'namespace PiExponent.DeterminantContradiction\n\n'
        + helpers[0] + b'\n\n' + helpers[1] +
        b'\n\nend PiExponent.DeterminantContradiction\n\nend OAI\n\n'
        b'namespace OAI\n\nopen scoped BigOperators\n\n'
        b'namespace PiExponent.LiteralAnalytic\nopen DeterminantContradiction\n\n'
        + helpers[2] +
        b'\n\nend PiExponent.LiteralAnalytic\n\nend OAI\n\n'
        b'open scoped BigOperators Topology\nopen Filter\n'
        b'open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic\n\n'
        + global_solution + b'\n'
    )
    if b'sorry' in body or body.count(b'private theorem ') != 3 or body.count(b'theorem solution') != 1:
        raise ValueError('Grouped candidate visibility or proof placeholders changed')
    report = {
        'schema_version': 1,
        'artifact_kind': 'ap20-analytic-remainder-three-exact-helper-grouped-candidate',
        'source_commit': data['source_commit'],
        'target': TARGET,
        'existing_open_theorem_id': data['existing_open_theorem_id'],
        'original_helper_commands_sha256': [x['command_sha256'] for x in data['source_units'][:3]],
        'original_helper_proof_suffixes_sha256': [x['proof_suffix_sha256'] for x in data['source_units'][:3]],
        'original_target_proof_suffix_sha256': data['source_units'][3]['proof_suffix_sha256'],
        'target_name_only_rewritten_to_global_solution': True,
        'helpers_only_private_visibility_prefix_added': True,
        'pending_actual_open_child_interfaces': CHILDREN,
        'candidate_sha256': sha(body),
        'closed_proof_claimed': False,
        'compiler_manifests_emitted': False,
        'Lean_started_by_producer': False,
        'API_used': False,
        'inputs': {
            str((SOURCE / f'source-unit-{i}.lean.txt').relative_to(TASK)).replace('\\', '/'): sha(commands[i-1])
            for i in range(1, 5)
        },
    }
    return body, report


def main() -> None:
    body, report = assemble()
    outputs = {
        STAGE / 'Sol-candidate.lean.txt': body,
        STAGE / 'candidate-preparation.json':
            (json.dumps(report, ensure_ascii=False, indent=2) + '\n').encode(),
    }
    for path, raw in outputs.items():
        if path.exists() and path.read_bytes() != raw:
            raise ValueError('Refusing grouped candidate overwrite: ' + str(path))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    print(json.dumps({'candidate_sha256': report['candidate_sha256'],
                      'pending_open_children': CHILDREN,
                      'closed_proof_claimed': False}))


if __name__ == '__main__':
    main()

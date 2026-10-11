"""Prepare a fresh native project; do not execute Lean or Lake."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/ps1'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def put(path, data):
    assert path.resolve().is_relative_to(TASK.resolve())
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, 'Preserving differing preparation file: ' + str(path)
    else:
        path.write_bytes(data)


kernel_review = TASK / 'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json'
assert sha(kernel_review) == '7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
review = json.loads(kernel_review.read_text(encoding='utf-8'))
assert review['verdict'] == 'PASS' and all(c['pass'] for c in review['checks'])
fixed = {r['root_relative']: r for r in review['stable_files']}
assert not (PROJECT / 'b').exists(), 'No cache borrowing or reset is allowed.'
names = ['CoefficientMap', 'CoefficientMapJet', 'CoefficientMapInjectivity',
         'CoefficientMapPartialFractions', 'CoefficientMapReflection',
         'CoefficientMapFiniteSum', 'CoefficientMapSummation', 'CoefficientMapAggregate',
         'CoefficientMapTelescoper', 'CoefficientMapShiftDegree', 'CoefficientMapKernelBridge',
         'CoefficientMapConnection', 'CoefficientMapParameterShift']
paths = ['missions/zeta9/formalization/' + n + '.lean' for n in names]
paths.append('Definitions/Def_ZetaNine_HarmonicStability.lean')
records = []
for relative in paths:
    source = ROOT / relative
    if relative in fixed:
        assert sha(source) == fixed[relative]['sha256'] and source.stat().st_size == fixed[relative]['bytes']
        origin = 'frozen KernelBridge independent native source binding'
    elif relative.endswith('/CoefficientMapConnection.lean'):
        assert sha(source) == '098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
        origin = 'frozen Connection source; separate native independent PASS'
    else:
        assert relative.endswith('/CoefficientMapParameterShift.lean')
        origin = 'uncompiled source candidate; not a PASS binding'
    destination = PROJECT / relative
    put(destination, source.read_bytes())
    records.append({'root_relative': relative, 'project_relative': relative,
                    'bytes': source.stat().st_size, 'sha256': sha(source), 'origin': origin})

configuration = f'''import Lake
open Lake DSL
package zeta9ParameterShiftNative where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{ENV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapParameterShift]
  globs := #[.submodules `missions.zeta9.formalization]
lean_lib Definitions
'''
put(PROJECT / 'lakefile.lean', configuration.encode('utf-8'))
for name in ('lean-toolchain', 'lake-manifest.json'):
    put(PROJECT / name, (ROOT / name).read_bytes())
assert (PROJECT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
objects = [PROJECT / 'b/lib/lean' / relative.replace('.lean', '.olean') for relative in paths]
max_path = max(len(str(path)) + 64 for path in objects)
assert max_path <= 259
state = {'status': 'PREPARATION_ONLY', 'Lean_Lake_executed': False,
         'candidate_sha256': sha(TASK / 'formalization/CoefficientMapParameterShift.lean'),
         'project': str(PROJECT), 'fresh_build_directory_absent': True,
         'native_objects_borrowed': False, 'only_Mathlib_package_cache_to_be_shared': True,
         'package_junction_pending': True, 'planned_object_path_plus_64_max': max_path,
         'mathlib_rev': ENV, 'lean_toolchain': 'leanprover/lean4:v4.33.1', 'sources': records,
         'remaining': ['first actual native build', 'exact type and axiom audit',
                       'independent mathematical replay', 'five formal-output transport']}
put(OUT / 'preparation-state.json', (json.dumps(state, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))
print('Fresh native preparation only; no Lean/Lake; parent bytes pinned; path+64:', max_path)

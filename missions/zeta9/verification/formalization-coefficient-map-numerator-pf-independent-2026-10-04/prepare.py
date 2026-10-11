"""Pure preparation only. This file cannot launch Lean, Lake or a compiler."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
PROJECT = TASK / '.rt/pfi'
AUTHOR = TASK / 'verification/formalization-coefficient-map-numerator-pf-2026-10-04'
AUTHOR_SHA = '7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5'
SOURCE_SHA = '2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77'
DATA_SHA = 'ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'
REVISION = '0df444a360eaa60ab8c11dca51a86af692955474'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content if isinstance(content, bytes) else content.encode('utf-8'))

def dump(path, value):
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def record(path):
    return {'root_relative': path.relative_to(ROOT).as_posix(),
            'sha256': sha(path), 'bytes': path.stat().st_size}

assert not PROJECT.exists(), 'Independent pfi enrollment requires a genuinely absent project'
assert not (OUT / 'preparation-freeze.json').exists(), 'Never mutate an earlier frozen preparation'
assert sha(AUTHOR / 'author-audit.json') == AUTHOR_SHA
author = load(AUTHOR / 'author-audit.json')
assert author['verdict'] == 'PASS' and len(author['checks']) == 24
assert len(author['stable_files']) == 188
for item in author['stable_files']:
    observed = record(ROOT / item['root_relative'])
    assert all(observed[key] == item[key] for key in ['root_relative', 'sha256', 'bytes'])
source = TASK / 'formalization/CoefficientMapNumeratorPartialFractions.lean'
data = TASK / 'formalization/CoefficientMapFormalTransportData.lean'
assert sha(source) == SOURCE_SHA and sha(data) == DATA_SHA

names = ['CoefficientMap', 'CoefficientMapJet', 'CoefficientMapInjectivity',
         'CoefficientMapPartialFractions', 'CoefficientMapReflection',
         'CoefficientMapFiniteSum', 'CoefficientMapSummation', 'CoefficientMapAggregate',
         'CoefficientMapShiftDegree', 'CoefficientMapTelescoper', 'CoefficientMapKernelBridge',
         'CoefficientMapConnection', 'CoefficientMapParameterShift',
         'CoefficientMapFormalTransportData', 'CoefficientMapNumeratorPartialFractions']
paths = [Path('Definitions/Def_ZetaNine_HarmonicStability.lean')] + [
    Path('missions/zeta9/formalization') / (name + '.lean') for name in names]
stable_author_map = {x['root_relative']: x for x in author['stable_files']}
sources = []
for rel in paths:
    original = ROOT / rel
    assert rel.as_posix() in stable_author_map
    observed = record(original)
    assert all(observed[key] == stable_author_map[rel.as_posix()][key]
               for key in ['root_relative', 'sha256', 'bytes'])
    write(PROJECT / rel, original.read_bytes())
    sources.append(dict(record(original), project_relative=rel.as_posix(),
                        module=rel.with_suffix('').as_posix().replace('/', '.')))
assert len(sources) == 16

# Enroll the actual import closure. Mathlib imports are fixed package dependencies;
# no other task source, Root build cache, author object or old independent object is copied.
available = {x['module'] for x in sources}
imports = []
for item in sources:
    current = (ROOT / item['root_relative']).read_text(encoding='utf-8-sig')
    for line in current.splitlines():
        if line.startswith('import '):
            for module in line.removeprefix('import ').split():
                assert module.startswith('Mathlib.') or module in available, module
                imports.append({'from': item['module'], 'import': module})
    assert not re.search(r'(?m)^\s*(axiom|sorry|admit|unsafe)\b', current)

for name in ['lean-toolchain', 'lake-manifest.json']:
    write(PROJECT / name, (ROOT / name).read_bytes())
write(PROJECT / 'lakefile.lean', '''import Lake
open Lake DSL
package zeta9NumeratorPFIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "''' + REVISION + '''"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions]
  globs := #[.submodules `missions.zeta9.formalization]
lean_lib Definitions
''')
assert (PROJECT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
manifest = load(PROJECT / 'lake-manifest.json')
mathlib = next(x for x in manifest['packages'] if x['name'] == 'mathlib')
assert mathlib['rev'] == REVISION

plan = load(AUTHOR / 'audit-plan.json')
definitions = plan['actual_definition_names']
proofs = plan['actual_proof_names']
assert len(definitions) == 16 and len(proofs) == 24
source_declarations = re.findall(r'(?m)^(def|theorem)\s+(\w+)', source.read_text(encoding='utf-8-sig'))
assert len(source_declarations) == 27
assert [kind for kind, _ in source_declarations].count('def') == 4
assert [kind for kind, _ in source_declarations].count('theorem') == 23

helper = (AUTHOR / 'helper.lean').read_text(encoding='utf-8-sig')
helper = helper.replace('-- Own author runtime full Expr audit;', '-- Source-only imported helper for this fresh independent runtime audit;')
helper = helper.replace('import Lean\n', '')
write(OUT / 'helper-source-only.lean', helper)
source_audit = 'import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\nimport Lean\n' + helper + '\nrun_meta do\n'
source_audit += ''.join('  emitIndependentDefinition `' + n + '\n' for n in definitions)
source_audit += ''.join('  emitIndependentProof `' + n + '\n' for n in proofs)
write(OUT / 'source_audit.lean', source_audit)

# Whole definitions are rebuilt from these actual source bodies, including the
# real Classical.choose witness. This is source extraction, not independently
# guessed mathematical values; actual Meta/rfl checks must still execute later.
def declarations_only(path):
    text = re.sub(r'/\-.*?\-/', '', path.read_text(encoding='utf-8-sig'), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    markers = list(re.finditer(r'(?m)^(def|theorem)\s+(\w+)', text))
    result = []
    for index, marker in enumerate(markers):
        if marker[1] != 'def':
            continue
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        body = text[marker.start():end].split('\nend ')[0].strip()
        result.append((marker[2], body))
    return result

common = '''import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
'''
value_aliases = common + '''namespace NumeratorPFIndependentDataValues
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
'''
data_defs = declarations_only(data)
pf_defs = declarations_only(source)
assert len(data_defs) == 12 and len(pf_defs) == 4
value_aliases += '\n\n'.join(body for name, body in data_defs)
value_aliases += '''
end NumeratorPFIndependentDataValues
namespace NumeratorPFIndependentValues
open ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity
'''
value_aliases += '\n\n'.join(body for name, body in pf_defs)
value_aliases += '\nend NumeratorPFIndependentValues\n'
write(PROJECT / 'IndependentValues.lean', value_aliases)
aliases = ['NumeratorPFIndependentDataValues.' + n for n, _ in data_defs]
aliases += ['NumeratorPFIndependentValues.' + n for n, _ in pf_defs]
value_audit = 'import IndependentValues\nimport Lean\n' + helper + '\n'
value_proofs = []
for index, (name, alias) in enumerate(zip(definitions, aliases)):
    proof = 'independent_whole_value_' + str(index + 1).zfill(2)
    value_proofs.append(proof)
    value_audit += f'theorem {proof} : {name} = {alias} := rfl\n'
value_audit += '\nrun_meta do\n'
for name, alias in zip(definitions, aliases):
    value_audit += f'  checkIndependentNativeAlias `{name} `{alias}\n'
for name in value_proofs:
    value_audit += f'  emitIndependentProof `{name}\n'
write(OUT / 'whole_values.lean', value_audit)

expected = (OUT / 'expected_types.lean').read_text(encoding='utf-8-sig')
expected_names = re.findall(r'(?m)^theorem\s+(\w+)', expected)
assert len(expected_names) == 24
assert expected_names == [name.rsplit('.', 1)[1] for name in proofs]
expected += '\n' + helper
expected += '''
private def compareIndependentExpected (source expected : Lean.Name) : Lean.MetaM Unit := do
  let a ← Lean.getConstInfo source
  let b ← Lean.getConstInfo expected
  let eq ← Lean.Meta.isDefEq a.type b.type
  unless eq do throwError "Whole source/independently-written expected type mismatch: {source}"
  IO.println (Lean.Json.mkObj [("kind",Lean.Json.str "independent_complete_type_kernel"),
    ("source",Lean.Json.str source.toString),("expected",Lean.Json.str expected.toString),
    ("whole_type_kernel_equal",Lean.toJson eq),
    ("actual_type_repr",Lean.Json.str (reprStr a.type)),
    ("expected_type_repr",Lean.Json.str (reprStr b.type))]).compress

run_meta do
'''
for original, name in zip(proofs, expected_names):
    expected += f'  emitIndependentProof `NumeratorPFIndependentExpected.{name}\n'
    expected += f'  compareIndependentExpected `{original} `NumeratorPFIndependentExpected.{name}\n'
write(OUT / 'expected_types_prepared.lean', expected)

boundaries = (OUT / 'own_boundaries.lean').read_text(encoding='utf-8-sig')
boundary_names = re.findall(r'(?m)^theorem\s+(\w+)', boundaries)
boundaries += '\n' + helper + '\nrun_meta do\n'
boundaries += ''.join(f'  emitIndependentProof `NumeratorPFIndependentBoundaries.{name}\n' for name in boundary_names)
write(OUT / 'own_boundaries_prepared.lean', boundaries)

# Author source replays have explicitly separate provenance. Only .lean is copied.
for original, destination in [('types.lean', 'author_types_replay.lean'),
                              ('values.lean', 'author_values_replay.lean'),
                              ('b2.lean', 'author_boundaries_replay.lean')]:
    write(OUT / destination, (AUTHOR / original).read_bytes())
write(PROJECT / 'ValueAliases.lean', (TASK / '.rt/np1/ValueAliases.lean').read_bytes())

resolver = '''import Lean
open Lean
run_meta do
  let ep ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),
    ("LEAN_PATH",Json.str (ep.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
'''
for module in [x['module'] for x in sources] + ['IndependentValues', 'ValueAliases']:
    resolver += f'  let p ← findOLean `{module}\n'
    resolver += f'  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "{module}"),("object",Json.str p.toString)]).compress\n'
write(OUT / 'actual_resolver.lean', resolver)
objects = [PROJECT / 'b/lib/lean' / Path(module.replace('.', '/')).with_suffix('.olean')
           for module in [x['module'] for x in sources] + ['IndependentValues', 'ValueAliases']]
assert all(len(str(path)) + 64 <= 259 for path in objects)
assert not (PROJECT / 'b').exists() and not (PROJECT / '.lake/build').exists()
assert not list(PROJECT.rglob('*.olean'))
prepared_files = sorted([p for p in OUT.iterdir() if p.is_file()] +
                        [p for p in PROJECT.rglob('*') if p.is_file()])
prep = {'status': 'PURE_PREPARATION_WAIT_EXPLICIT_LEAN_LANE',
        'Lean_Lake_compiler_invocations': 0, 'verdict': None,
        'independent_lane_granted': False,
        'independent_project_initially_absent': True,
        'own_build_and_Lake_build_cache_absent': True,
        'author_audit': record(AUTHOR / 'author-audit.json'),
        'author_all_188_stable_files_verified': author['stable_files'],
        'source_sha256': SOURCE_SHA, 'Data_sha256': DATA_SHA,
        'fresh_full_source_build_order': sources, 'actual_import_edges': imports,
        'fixed_Mathlib_revision': REVISION,
        'Lean_toolchain': 'leanprover/lean4:v4.33.1',
        'shared_package_cache_only': (ROOT / '.lake/packages').as_posix(),
        'author_Root_or_old_independent_proof_objects_copied': 0,
        'prepared_counts_not_execution': {
            'full_source_builds': 16, 'Data_PF_definitions': 16,
            'Data_PF_original_proof_types': 24, 'independent_expected_whole_types': 24,
            'whole_definition_value_Meta_comparisons': 16, 'whole_function_rfl_proofs': 16,
            'independent_boundary_proofs': len(boundary_names),
            'author_boundary_replays': 15, 'actual_own_object_resolutions': 18},
        'expected_object_paths': [p.relative_to(TASK).as_posix() for p in objects],
        'max_object_path_chars': max(len(str(p)) for p in objects),
        'max_object_path_plus64_le259': True,
        'independent_boundary_names': boundary_names,
        'definition_value_provenance': 'full source-only bodies; future actual Meta/rfl required',
        'expected_type_provenance': 'independently written complete forall types, no source proof copied',
        'proof_and_convergence_boundary':
          'Strict proper reconstruction and jet injectivity, regular-point quotient; m0 X8 gives 1/t; X9 has zero jets but is improper. No PF parameter/five-output transport, coefficient-array uniqueness, integer heights, HasSum transport or irrationality claimed.',
        'stable_files': [record(p) for p in prepared_files]}
dump(OUT / 'preparation-freeze.json', prep)
print(json.dumps({'preparation_sha256': sha(OUT / 'preparation-freeze.json'),
                  'author_bindings': 188, 'fresh_sources': len(sources),
                  'prepared_counts_not_execution': prep['prepared_counts_not_execution'],
                  'Lean_Lake_compiler_invocations': 0,
                  'stable_files': len(prep['stable_files']),
                  'max_path_plus64': prep['max_object_path_chars'] + 64}, indent=2))

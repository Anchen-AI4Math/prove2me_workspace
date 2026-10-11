"""Pure independent native preparation. Never executes Lean or imports proof objects."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib, json, re, sys
sys.dont_write_bytecode = True

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
AUTHOR = TASK / 'verification/formalization-analytic-phase-upper-bound-2026-10-07'
PROJECT = TASK / '.rt/api1'
TOOLCHAIN = Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1').resolve()
PYTHON = 'C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
REV = '0df444a360eaa60ab8c11dca51a86af692955474'
AUTHOR_SHA = 'a8f8cf52008b69f7b8e7e868a3c754ebc72c89f4f6f1aa89f9ca2bfdf1ff2647'
EXPECTED = {
 'AnalyticPhase': '2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd',
 'AnalyticPhaseUpperBound': '388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635',
}
ORIGINAL = {
 'AnalyticPhase': '475f95ba7e9c977a78b6efa8e0f1599d2ec32fcc20e46bfb1bfb3b5e309ea38c',
 'AnalyticPhaseUpperBound': '9e0ed4cb7757b17af9a64b69927a3fa47c440d1828f239be50e473ab24a21c16',
}
NS = 'ZetaNine.AnalyticPhase.'

def sha(path):
 h = hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda: f.read(1024 * 1024), b''): h.update(b)
 return h.hexdigest()

def load(path): return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def write(path, data):
 Path(path).parent.mkdir(parents=True, exist_ok=True)
 Path(path).write_bytes(data if isinstance(data, bytes) else data.encode('utf-8'))
def dump(path, data): write(path, json.dumps(data, ensure_ascii=False, indent=2) + '\n')
def binding(path):
 path = Path(path)
 return dict(task_relative=path.relative_to(TASK).as_posix(), bytes=path.stat().st_size, sha256=sha(path))
def prefixes(text):
 result = {}
 for m in re.finditer(r'(?m)^theorem (\w+)', text):
  end = text.index(':=', m.end())
  result[m.group(1)] = text[m.start():end + 2]
 return result
def defs(text):
 return {m.group(1): m.group(0) for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)', text)}
def args(prefix, name):
 tail = prefix[len('theorem ' + name):]
 result, pos = [], 0
 while True:
  while pos < len(tail) and tail[pos].isspace(): pos += 1
  if tail[pos] == ':': break
  opener = tail[pos]
  assert opener in '({'
  closer = ')' if opener == '(' else '}'
  depth, end = 1, pos + 1
  while depth:
   if tail[end] == opener: depth += 1
   elif tail[end] == closer: depth -= 1
   end += 1
  result += tail[pos + 1:end - 1].split(':', 1)[0].split()
  pos = end
 return ' '.join(result)
def quoted(names): return '#[' + ', '.join('``' + n for n in names) + ']'

IMPORT = '''import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
open Lean Meta Elab Command
'''
EMITTER = '''
private def apEmit (j : Json) : MetaM Unit := do
  liftM <| IO.println ("PHI_RECORD|" ++ j.compress)

private def apAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def apRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let mut value := Json.null
  let mut typed := false
  if let some e := ci.value? true then
    value := toJson (reprStr e)
    typed ← isDefEq (← inferType e) ci.type
    unless typed do throwError "Declaration value does not have its full type: {n}"
  apEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("full_value_typed",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← apAxioms n)]
'''

def verify_author_critical():
 report = AUTHOR / 'author-audit.json'
 assert sha(report) == AUTHOR_SHA
 a = load(report)
 rows = [b for b in a['stable_bindings'] if b.get('task_relative')]
 def check(b):
  rel = Path(b['task_relative'])
  assert not rel.is_absolute() and '..' not in rel.parts
  path = TASK / rel
  assert path.resolve().is_relative_to(TASK.resolve())
  assert path.name not in {'credentials.json', '.env'}
  assert path.stat().st_size == b['bytes'] and sha(path) == b['sha256'], str(path)
  return b
 with ThreadPoolExecutor(max_workers=2) as pool: checked = list(pool.map(check, rows))
 dump(OUT / 'author-critical-input-inspection.json', dict(
  author_report=binding(report), independently_rehashed_task_bindings=checked,
  count=len(checked), differences=0, Lean_executed=False,
  fixed_package_and_intrinsic_toolchain_bindings_deferred_to_full_final_hash=True,
  complete_author_binding_count=len(a['stable_bindings']),
  author_PASS_string_is_not_independent_evidence=True))
 return a

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 a = verify_author_critical()
 assert not PROJECT.exists(), 'No resetting any existing api1 environment'
 PROJECT.mkdir(parents=True)
 originals, theorems, definitions, source_contracts = {}, {}, {}, []
 for name, expected in EXPECTED.items():
  original = TASK / 'formalization' / (name + '.lean')
  export = AUTHOR / 'native-export' / (name + '.lean')
  assert sha(original) == ORIGINAL[name] and sha(export) == expected
  text = original.read_text(encoding='utf-8-sig')
  actual = export.read_text(encoding='utf-8-sig')
  assert prefixes(text) == prefixes(actual) and defs(text) == defs(actual)
  assert text[:text.index('theorem ')] == actual[:actual.index('theorem ')]
  assert not re.search(r'\b(sorry|admit|native_decide)\b', actual)
  assert not re.search(r'(?m)^\s*(axiom|opaque|constant)\s', actual)
  private = PROJECT / 'missions/zeta9/formalization' / (name + '.lean')
  write(private, export.read_bytes())
  source_contracts.append(dict(module=name, shared_source=binding(original),
   frozen_author_export=binding(export), independent_fresh_source=binding(private),
   all_original_headers_and_definitions_exact=True))
  originals[name] = text
  theorems.update(prefixes(text)); definitions.update(defs(text))
 assert len(theorems) == 34 and len(definitions) == 7
 write(PROJECT / 'lean-toolchain', (ROOT / 'lean-toolchain').read_bytes())
 manifest = TASK / '.rt/aph1/lake-manifest.json'
 manifest_data = load(manifest)
 assert any(p.get('name') == 'mathlib' and p.get('rev') == REV for p in manifest_data['packages'])
 write(PROJECT / 'lake-manifest.json', manifest.read_bytes())
 write(PROJECT / 'lakefile.lean', f'''import Lake
open Lake DSL
package zeta9ActualPhaseIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib ActualPhaseIndependent where
  roots := #[`missions.zeta9.formalization.AnalyticPhaseUpperBound]
  globs := #[.one `missions.zeta9.formalization.AnalyticPhase, .one `missions.zeta9.formalization.AnalyticPhaseUpperBound]
''')
 leaf = '''from pathlib import Path
import json, os, subprocess, sys
PROJECT = Path(__file__).resolve().parent
PACKAGES = Path(r"D:\\users\\self_projects\\prove2me_workspace\\.lake\\packages").resolve()
env = dict(os.environ)
selected = {}
for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
 original = [raw for raw in env.get(key, '').split(os.pathsep) if raw]
 allowed = []
 for raw in original:
  resolved = (PROJECT / Path(raw)).resolve()
  if resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(PACKAGES):
   allowed.append(str(resolved))
 own = str(PROJECT / 'b/lib/lean') if key == 'LEAN_PATH' else str(PROJECT)
 if own not in allowed: allowed.insert(0, own)
 env[key] = os.pathsep.join(allowed)
 selected[key] = dict(original=original, filtered=allowed)
selected['actual_environment'] = {k: env.get(k) for k in ['LEAN_NUM_THREADS', 'LAKE_JOBS']}
Path(env['PHASE_INDEPENDENT_PATH_RECEIPT']).write_text(json.dumps(selected, indent=2)+'\\n', encoding='utf-8')
result = subprocess.run(sys.argv[1:], env=env)
sys.exit(result.returncode)
'''
 write(PROJECT / 'leaf.py', leaf)
 types = IMPORT + EMITTER + '\nrun_cmd liftTermElabM do\n'
 types += '  for n in ' + quoted([NS+n for n in definitions]) + ' do apRecord "definition" n\n'
 types += '  for n in ' + quoted([NS+n for n in theorems]) + ' do apRecord "theorem" n\n'
 types += '''  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if #[`missions.zeta9.formalization.AnalyticPhase,
          `missions.zeta9.formalization.AnalyticPhaseUpperBound].contains m then
      let data := env.header.moduleData[i]!
      apEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do apRecord "module_declaration" n
      for n in data.extraConstNames do
        if (env.find? n).isSome then apRecord "module_extra" n
'''
 kernel = IMPORT + EMITTER + '\nnamespace APIndOriginalDefs\n'
 for name, decl in definitions.items():
  head, body = decl.split(':=', 1)
  for dep in definitions: body = re.sub(r'\b'+re.escape(dep)+r'\b', NS+dep, body)
  kernel += head + ':=' + body + '\n\n'
 kernel += 'end APIndOriginalDefs\n\n'
 for name in definitions:
  kernel += f'theorem independent_original_value_{name} : APIndOriginalDefs.{name} = {NS}{name} := rfl\n'
 kernel += '\nnamespace APIndExpected\n'
 for name, prefix in theorems.items():
  kernel += prefix + ' by\n  exact @'+NS+name+' '+args(prefix,name)+'\n\n'
 kernel += '''theorem exact_open_domain : ∀ x : ℝ, 1 < x →
    ZetaNine.AnalyticPhase.phase x ≤ (-2641 / 250 : ℝ) :=
  ZetaNine.AnalyticPhase.phase_global_upper_bound
end APIndExpected
'''
 author_kernel = (AUTHOR / 'controls-v4/APKernel.lean').read_text(encoding='utf-8')
 meta_start = author_kernel.index('private def apProofHelpers')
 meta_end = author_kernel.index('\nrun_cmd liftTermElabM do', meta_start)
 kernel += '\n' + author_kernel[meta_start:meta_end] + '\nrun_cmd liftTermElabM do\n'
 for name in definitions:
  kernel += f'  apCompare "definition_compare" ``{NS}{name} ``APIndOriginalDefs.{name} true\n'
  kernel += f'  apRecord "definition_rfl" ``independent_original_value_{name}\n'
 for name in theorems:
  kernel += f'  apCompare "theorem_compare" ``{NS}{name} ``APIndExpected.{name} false\n'
 kernel += f'  apCompare "exact_domain_compare" ``{NS}phase_global_upper_bound ``APIndExpected.exact_open_domain false\n'
 boundary_old = (AUTHOR / 'controls-v2/APBoundary.lean').read_text(encoding='utf-8')
 boundary_start = boundary_old.index('namespace APBoundary')
 boundary = IMPORT + EMITTER + boundary_old[boundary_start:].replace('APBoundary', 'APIndBoundary')
 boundaries = re.findall(r'(?m)^theorem (\w+)', boundary)
 assert len(boundaries) == 15
 resolver = IMPORT + '''
run_cmd liftTermElabM do
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    let j := Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]
    liftM <| IO.println ("PHI_RECORD|" ++ j.compress)
'''
 for name, text in [('APIPhaseTypes.lean', types), ('APIPhaseKernel.lean', kernel),
                    ('APIPhaseBoundary.lean', boundary), ('APIPhaseResolver.lean', resolver)]:
  write(PROJECT / name, text); write(OUT / 'controls-v1' / name, text)
 write(OUT / 'README.md', '''Pure independent preparation; no Lean execution yet.
Fresh .rt/api1 must SOURCE-compile both frozen author exports. Only fixed Mathlib
packages and intrinsic pinned Lean 4.33.1 are allowed, with actual canonical path
resolution. No Root, aph1 or foreign mission proof objects are imported.
34 exact source theorem headers, 7 full definition bodies/whole-function rfls,
27 source-module auxiliaries, helper full expressions and 15 boundaries are
prepared. Every original Expr.equal result stays raw; no metadata/binder erasure.
Root must separately grant a serial Lean lane before run_independent.py runs.
The phase bound alone does not prove complete Z9.A or irrationality.
''')
 dump(OUT / 'preparation-state.json', dict(
  role='independent native actual Phase auditor; not author', Lean_executed=False,
  API_executed=False, project_task_relative='.rt/api1', project_initially_absent=True,
  proof_objects_copied=False, fresh_source_count=2, source_contracts=source_contracts,
  expected_theorem_prefixes=theorems, original_full_definition_source=definitions,
  theorem_count=34, definition_count=7, typed_boundary_names=boundaries,
  auxiliary_expected_names=a['actual_auxiliary_names'],
  full_proof_values_and_actual_value_typing_added=True,
  helper_template_source=binding(AUTHOR / 'controls-v4/APKernel.lean'),
  template_reuse_is_SOURCE_control_only_not_objects=True,
  mathlib_revision=REV, packages_junction_not_yet_created=True,
  no_Lean_until_separate_explicit_Root_lane_grant=True,
  configs=[binding(PROJECT / n) for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']],
  controls=[binding(PROJECT / n) for n in ['APIPhaseTypes.lean','APIPhaseKernel.lean','APIPhaseBoundary.lean','APIPhaseResolver.lean']]))
 print('PURE independent preparation ready: 2 fresh SOURCE copies, 34 types, 7 full definitions, 15 boundaries; no Lean.')
 print('Preparation SHA256:', sha(OUT / 'preparation-state.json'))
 print('Critical author binding count:', len(load(OUT / 'author-critical-input-inspection.json')['independently_rehashed_task_bindings']))

if __name__ == '__main__': main()

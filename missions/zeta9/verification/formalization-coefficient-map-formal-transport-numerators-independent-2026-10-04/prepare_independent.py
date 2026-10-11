"""Pure preparation only. This script never calls Lean, Lake or a compiler."""
from pathlib import Path
import hashlib, json, re, subprocess

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/ni1'
AUTHOR = TASK / 'verification/formalization-coefficient-map-formal-transport-numerators-2026-10-04'
EXPECTED = {
    'author-audit.json': 'a33fa1bbf2844365a313b8d54526cf5815e8e58010411d4624bb056518b5d37a',
    'source-manifest.json': '27523bbf055c5d30dd50c2523ea4a458bb1e48459e946e648070381a55842212',
    'SHA256SUMS.txt': '3a34c7de19472ae8466383a2f039a58c6e6720e95afec1917d3fd59aa0a39450',
}
MODULE = 'missions.zeta9.formalization.CoefficientMapFormalTransportNumerators'
DATA = 'missions.zeta9.formalization.CoefficientMapFormalTransportData'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data if isinstance(data, bytes) else data.encode('utf8'))
def dump(p, obj): write(p, json.dumps(obj, indent=2, ensure_ascii=False)+'\n')
def bind(p): return {'root_relative':p.relative_to(ROOT).as_posix(), 'bytes':p.stat().st_size, 'sha256':sha(p)}

def strip_comments(text):
    out=[]; i=0; depth=0
    while i<len(text):
        if text.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif depth and text.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        elif not depth and text.startswith('--',i):
            stop=text.find('\n',i)
            if stop<0:stop=len(text)
            out.extend(' '*(stop-i)); i=stop
        else:
            out.append('\n' if text[i]=='\n' else (' ' if depth else text[i])); i+=1
    assert depth==0
    return ''.join(out)

def declarations(text, module):
    clean=strip_comments(text)
    namespace=re.search(r'^namespace\s+(\S+)',clean,re.M).group(1)
    rows=[]
    pattern=r'^(?P<private>private\s+)?(?:noncomputable\s+)?(?P<kind>theorem|lemma|def|abbrev)\s+(?P<name>[\w\u0080-\uffff]+)'
    for m in re.finditer(pattern,clean,re.M):
        rows.append({'module':module,'kind':m['kind'],'private':bool(m['private']),
            'name':namespace+'.'+m['name'],'short_name':m['name']})
    return rows

def lean_list(strings): return json.dumps(strings,ensure_ascii=False)

def prepare():
    assert not PROJECT.exists(), 'New project must be genuinely empty; never overwrite a prior run'
    controls=[]
    for name, expected in EXPECTED.items():
        p=AUTHOR/name; assert sha(p)==expected,(name,sha(p))
        write(OUT/'author-frozen-inputs'/name,p.read_bytes()); controls.append(bind(p))
    author=load(AUTHOR/'author-audit.json')
    assert author['verdict']=='PASS' and len(author['stable_files'])==282
    assert len(author['checks'])==16 and all(c['pass'] for c in author['checks'])
    actual=[]
    for row in author['stable_files']:
        p=ROOT/row['root_relative']
        assert p.is_file() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],str(p)
        actual.append(row)
    manifest=load(AUTHOR/'source-manifest.json')
    assert manifest['files']==actual
    sums=(AUTHOR/'SHA256SUMS.txt').read_text(encoding='utf8').splitlines()
    assert len(sums)==282
    sum_rows={line.split(None,1)[1].lstrip('* '):line.split(None,1)[0] for line in sums}
    assert sum_rows=={r['root_relative']:r['sha256'] for r in actual}
    originals={r['root_relative']:r for r in actual}
    modules=load(AUTHOR/'preparation-state.json')['parent_modules']+[MODULE]
    # Dependency order: the genuine HS source precedes the thirteen PS parents.
    modules.remove('Definitions.Def_ZetaNine_HarmonicStability')
    modules.insert(0,'Definitions.Def_ZetaNine_HarmonicStability')
    assert len(modules)==17 and len(set(modules))==17
    copied=[]; graph=[]
    for module in modules:
        rel=Path(module.replace('.','/')).with_suffix('.lean')
        source=ROOT/rel
        assert rel.as_posix() in originals,rel
        write(PROJECT/rel,source.read_bytes())
        copied.append({'module':module,'original':bind(source),'own_copy':bind(PROJECT/rel)})
        graph.extend(declarations(source.read_text(encoding='utf8'),module))
    assert not (PROJECT/'b').exists()
    for name in ['lean-toolchain','lake-manifest.json']:
        write(PROJECT/name,(ROOT/name).read_bytes())
    write(PROJECT/'lakefile.lean','''import Lake
open Lake DSL
package zeta9NumeratorIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  globs := #[.submodules `missions.zeta9.formalization]
lean_lib Definitions
''')
    packages=PROJECT/'.lake/packages'
    packages.parent.mkdir(parents=True,exist_ok=True)
    # The only executable here is a filesystem junction operation; no compiler.
    result=subprocess.run(['powershell','-NoProfile','-Command',
        f"New-Item -ItemType Junction -Path '{packages}' -Target '{ROOT/'.lake/packages'}' | Out-Null"],capture_output=True)
    write(OUT/'junction.log',result.stdout+result.stderr)
    write(OUT/'junction-exit.txt',str(result.returncode)+'\n')
    assert result.returncode==0 and packages.is_junction()
    assert packages.resolve()==(ROOT/'.lake/packages').resolve()
    assert not (PROJECT/'b').exists()
    # Independently recopy all actual Data definitions, only renaming the namespace.
    data_src=(ROOT/Path(DATA.replace('.','/')).with_suffix('.lean')).read_text(encoding='utf8')
    alias=data_src.replace('ZetaNine.CoefficientMapFormalTransportData','ZetaNine.NumeratorsIndependentDataValues')
    alias='import '+DATA+'\n'+alias
    data_defs=[r for r in graph if r['module']==DATA and r['kind']=='def']
    assert len(data_defs)==12
    alias+='\nnamespace NumeratorsIndependentValueCertificates\n'
    for r in data_defs:
        alias+=f"theorem value_{r['short_name']} : @{r['name']} = @ZetaNine.NumeratorsIndependentDataValues.{r['short_name']} := by rfl\n"
    alias+='end NumeratorsIndependentValueCertificates\n'
    write(PROJECT/'IndependentDataValues.lean',alias)
    # All source declarations, including private theorem values, are identified
    # from source inventory, not from guessed namespace-prefix counts.
    inventory=[{'name':r['name'],'kind':r['kind'],'private':r['private']} for r in graph]
    dump(OUT/'source-declaration-inventory.json',graph)
    audit='import '+MODULE+'\nimport Lean\nopen Lean Meta\n'
    audit+='''set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let env ← getEnv
'''
    for row in inventory:
        n=row['name']; kind=row['kind']
        audit+=f'''  do
    let wanted := "{n}"
    let found := env.constants.toList.filter fun (name, _) =>
      name.toString == wanted || name.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Exact source declaration resolution failed {{wanted}}"
    let (name, ci) := found.head!
    let actualKind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "proof"
      | _ => "other"
    unless actualKind == "{'definition' if kind in ['def','abbrev'] else 'proof'}" do
      throwError "Source declaration kind mismatch {{name}}"
    let axioms ← collectAxioms name
    unless axioms.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard source axiom {{name}}"
    let typePP ← ppExpr ci.type
    let value := ci.value?
    IO.println (Json.mkObj [("kind",Json.str "actual_source_declaration"),
      ("source_kind",Json.str "{kind}"),("source_name",Json.str wanted),
      ("actual_name",Json.str name.toString),("full_type_expr",Json.str (reprStr ci.type)),
      ("full_value_expr",Json.str (reprStr value)),("full_type_pp_diagnostic",Json.str typePP.pretty),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
'''
    write(PROJECT/'IndependentSourceGraph.lean',audit)
    values='''import IndependentDataValues
import Lean
open Lean Meta
run_meta do
'''
    for r in data_defs:
        name=r['name']; alias_name='ZetaNine.NumeratorsIndependentDataValues.'+r['short_name']
        cert='NumeratorsIndependentValueCertificates.value_'+r['short_name']
        values+=f'''  do
    let .defnInfo original ← getConstInfo `{name} | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `{alias_name} | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `{cert}
    let axs ← collectAxioms `{cert}
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "{name}"),("alias",Json.str "{alias_name}"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    write(PROJECT/'IndependentFullValues.lean',values)
    # Full forall type aliases are extracted only from the genuine final source.
    native=(ROOT/Path(MODULE.replace('.','/')).with_suffix('.lean')).read_text(encoding='utf8')
    clean=strip_comments(native)
    pat=re.compile(r'^(private\s+)?theorem\s+(\w+)([\s\S]*?)\s*:=',re.M)
    headers=list(pat.finditer(clean)); assert len(headers)==15
    type_module='''import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapKernelBridge CoefficientMapParameterShift
open CoefficientMapInjectivity CoefficientMapPartialFractions
namespace NumeratorsIndependentWholeTypes
'''
    pairs=[]
    for match in headers:
        private,short,body=match.groups()
        # Find the theorem result colon outside every binder.
        depth=0; split=None
        for i,ch in enumerate(body):
            if ch in '([{':depth+=1
            elif ch in ')]}':depth-=1
            elif ch==':' and depth==0:split=i;break
        assert split is not None,short
        binders=body[:split].strip(); typ=body[split+1:].strip()
        statement=('∀ '+binders+',\n    '+typ) if binders else typ
        full='ZetaNine.CoefficientMapFormalTransportNumerators.'+short
        alias_name='NumeratorsIndependentWholeTypes.expected_'+short
        proof='by\n  field_simp [hx, hy, hM]\n  <;> ring' if private else full
        type_module+=f'theorem expected_{short} : {statement} :=\n  {proof}\n\n'
        pairs.append((full,alias_name))
    type_module+='end NumeratorsIndependentWholeTypes\n'
    type_module+='open Lean Meta\nrun_meta do\n'
    for original,expected in pairs:
        type_module+=f'''  do
    let wanted := "{original}"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `{expected}
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {{name}}"
    let axs ← collectAxioms `{expected}
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "{expected}"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
    write(PROJECT/'IndependentWholeTypes.lean',type_module)
    own_modules=modules+['IndependentDataValues','IndependentWholeTypes']
    resolver='''import Lean
open Lean
def main : IO Unit := do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_search_path"),("value",Json.str (path.getD ""))]).compress
'''
    resolver+='  for m in ('+lean_list(own_modules)+' : List String) do\n'
    resolver+='''    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println (Json.mkObj [("kind",Json.str "actual_own_module_resolution"),
      ("module",Json.str m),("path",Json.str p.toString)]).compress
'''
    write(PROJECT/'IndependentResolver.lean',resolver)
    # Paths are reserved, not built. Every actual proof object must be created here.
    object_paths=[PROJECT/'b/lib/lean'/Path(m.replace('.','/')).with_suffix('.olean') for m in own_modules]
    assert all(not p.exists() for p in object_paths)
    assert max(len(str(p)) for p in object_paths)+64<=259
    runtime=[bind(PROJECT/n) for n in ['lean-toolchain','lake-manifest.json','lakefile.lean']]
    record={'status':'PURE_PREPARATION_ONLY_NO_LEAN_OR_LAKE_EXECUTED',
        'Lean_invocations':0,'Lake_invocations':0,'compiler_invocations':0,
        'author_control_bindings':controls,'verified_author_bindings':actual,
        'verified_author_binding_count':282,'verified_SUMS_members':282,
        'own_project':str(PROJECT),'fresh_source_modules_planned':17,
        'author_Root_independent_or_previous_PF_objects_reused':0,
        'mathlib_only_shared_package_junction':str(packages),
        'source_copies':copied,'runtime_bindings':runtime,
        'source_declaration_count':len(graph),'source_definition_count':sum(r['kind'] in ['def','abbrev'] for r in graph),
        'source_proof_count':sum(r['kind'] in ['theorem','lemma'] for r in graph),
        'whole_forall_type_comparisons_planned':15,'whole_actual_Data_value_comparisons_planned':12,
        'whole_Data_value_actual_rfl_certificates_planned':12,
        'own_module_resolutions_planned':19,'own_proof_object_cache_absent':True,
        'max_own_object_path':max(len(str(p)) for p in object_paths),
        'boundary_script_pending_preparation':True,'frozen_author_source':bind(ROOT/Path(MODULE.replace('.','/')).with_suffix('.lean'))}
    dump(OUT/'preparation-verification.json',record)
    print('PURE PREP:',len(graph),'actual source declarations; 282 bindings and SUMS members verified; fresh17sources; objects0; Lean0/Lake0')

if __name__=='__main__':prepare()

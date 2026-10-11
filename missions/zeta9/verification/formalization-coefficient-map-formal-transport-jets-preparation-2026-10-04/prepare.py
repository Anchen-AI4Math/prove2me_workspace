"""Pure candidate source writer/freeze. Never runs Lean, Lake or shell tools."""
from pathlib import Path
import hashlib,json,sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
SOURCE=TASK/'formalization/CoefficientMapFormalTransportJets.lean'
APPENDIX=TASK/'verification/coefficient-map-local-transport-offline-2026-10-04/appendix-jet-insertion-v2'
OLD_NS='ZetaNine.CoefficientMapJetInsertionCandidate'
NS='ZetaNine.CoefficientMapFormalTransportJets'
NAMES=['pole_factor','pole_comp_shift_factor','pole_upper','upper_cleared_denominator',
    'shift_successor_comp','lower_cleared_denominator','upper_whole_actual_series',
    'lower_whole_actual_series','local_zero_of_shift_X_nine','upper_all_actual_jets',
    'lower_all_actual_jets','double_all_actual_jets']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path,text):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(text if isinstance(text,bytes) else text.encode('utf-8'))
def dump(path,doc):write(path,json.dumps(doc,ensure_ascii=False,indent=2)+'\n')
def bind(path):return dict(root_relative=path.relative_to(ROOT).as_posix(),
    bytes=path.stat().st_size,sha256=sha(path))


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not SOURCE.exists(),'Do not overwrite candidate source.'
    assert not (OUT/'preparation-manifest.json').exists(),'Do not overwrite frozen preparation.'
    manifest=json.loads((APPENDIX/'appendix-manifest.json').read_text(encoding='utf-8-sig'))
    for row in manifest['files']+manifest['read_source_bindings']:
        path=TASK/row['task_relative']
        assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256']
    source=(APPENDIX/'JetInsertionCandidate.lean').read_text(encoding='utf-8-sig')
    start=source.index('/-!');stop=source.index('-/',start)+2
    new_header='''/-!
UNCOMPILED COMPLETE WRITTEN CANDIDATE. No Lean/Lake invocation has been
performed for this module. These are proposed proof scripts, not verified facts.
The generic insertions retain arbitrary numerators and m=0. The actual chosen
transport retains n>=1, every actual pole and orders one through nine, including
the right boundary -c(n+1,s). Finite rho cancellation adds no parity or analytic
premise. The formal constant/matrix output bridge remains a later obligation.
-/'''
    source=source[:start]+new_header+source[stop:]
    source=source.replace('import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions',
        'import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\n'
        'import missions.zeta9.formalization.CoefficientMapFiniteSum')
    source=source.replace(OLD_NS,NS)
    for name in NAMES:
        assert 'theorem '+name+'_candidate ' in source,name
        source=source.replace(name+'_candidate',name)
    ending='\nend '+NS+'\n'
    assert source.count(ending)==1
    tail=(OUT/'candidate-tail.lean').read_text(encoding='utf-8-sig')
    source=source.replace(ending,'\n'+tail+'\nend '+NS+'\n')
    declaration_lines=[line for line in source.splitlines() if line.startswith('theorem ')]
    assert len(declaration_lines)==26
    assert not any(word in source.split() for word in ['sorry','admit','axiom'])
    write(SOURCE,source);write(OUT/'prepared-source.lean',SOURCE.read_bytes())
    scheduling,active,done=[],set(),set()
    def visit(module):
        if module in done:return
        assert module not in active
        active.add(module)
        path=ROOT/(module.replace('.','/')+'.lean')
        assert path.is_file()
        deps=[d for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('import ') for d in line[7:].split()
            if d.startswith('missions.zeta9.formalization.')
            or d=='Definitions.Def_ZetaNine_HarmonicStability']
        for dep in deps:visit(dep)
        active.remove(module);done.add(module)
        scheduling.append(dict(bind(path),module=module,import_scheduling_only=deps))
    visit('missions.zeta9.formalization.CoefficientMapFormalTransportJets')
    write(OUT/'README.md','''# Uncompiled actual jet transport candidate

This is pure preparation. The source contains 26 complete written proof scripts
and no admitted proof. None has been run by Lean, and no theorem/type/kernel
PASS, actual oracle, platform acceptance or formal five-output transport is
claimed. The source count is lexical inventory only.

The first twelve insertion scripts are copied from the fixed real appendix;
only theorem/namespace names and the module header/import are changed. Five
generic series/jet linearity scripts are added. The actual chosen all-jet bridge
uses the real cleared numerator identity, not an abstract transport relation.
Its two boundary scripts retain c(0,s) and -c(n+1,s). Two generic finite padding
identities, three real extended-array sums and one full nine-rho cancellation
script complete the proposed module.

Generic insertion retains arbitrary A, m=0, and the real pole/order guards.
Actual chosen transport retains n>=1, j<=n+2, 1<=s<=9. Finite rho transport
has no Even, degree, PF-existence, zeta independence or summability hypothesis.
The real Connection witness already supplies the required P/q equation.

No local proof project or object cache was created. The import schedule is
derived from actual import lines only; it is not a compiled declaration graph.
The Root agent must grant a serial Lean lane before any elaboration or audit.
The next module still needs the true finite harmonic constant correction,
proper/regular PF point evaluations and matrix assembly in the direction
F(n+2)=Gamma(n)*F(n).

Potential elaboration repairs are ordinary coercion/cast rewrites, Nat addition
normalization at range successors, whole-series uniqueness inference and the
new finite padding induction. Failures must be retained if a later compile
requires repairs. This preparation writes no Root/scope/API/credential files.
''')
    stable=[SOURCE]+[path for path in sorted(OUT.rglob('*')) if path.is_file()
        and '__pycache__' not in path.parts and path.name not in
        ['preparation-manifest.json','PREPARATION_SHA256SUMS.txt']]
    report=dict(status='UNCOMPILED_COMPLETE_WRITTEN_CANDIDATE_ONLY',Lean_invocations=0,
        Lake_invocations=0,actual_parser_oracle_claimed=False,kernel_PASS_claimed=False,
        source=bind(SOURCE),pure_source_inventory_count=26,
        source_inventory_is_lexical_not_actual_declaration_graph=True,
        source_initially_absent=True,local_project_created=False,compiler_objects_borrowed=False,
        appendix=bind(APPENDIX/'JetInsertionCandidate.lean'),
        appendix_manifest=bind(APPENDIX/'appendix-manifest.json'),
        exact_copied_generic_theorem_names=NAMES,
        actual_import_scheduling_only=scheduling,
        mathematical_hypotheses_added_to_actual_transport=[],
        pending=['Root lane grant','real source compilation and complete source/type/axiom audits',
            'actual generic m0/improper numerator and chosen boundary controls',
            'independent native review','finite formal constant correction and matrix assembly'],
        formal_five_output_transport_proved=False,rho_theorem_kernel_verified=False,
        Root_API_scope_credentials_modified=False,files=[bind(path) for path in stable])
    dump(OUT/'preparation-manifest.json',report)
    write(OUT/'PREPARATION_SHA256SUMS.txt',''.join(sha(path)+'  '+path.relative_to(ROOT).as_posix()+'\n'
        for path in stable+[OUT/'preparation-manifest.json']))
    for row in report['files']:
        path=ROOT/row['root_relative']
        assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256']
    print(json.dumps(dict(status=report['status'],source_sha256=sha(SOURCE),
        source_bytes=SOURCE.stat().st_size,pure_inventory=26,
        actual_import_source_schedule=len(scheduling),Lean_invocations=0,
        manifest_sha256=sha(OUT/'preparation-manifest.json'),
        sums_sha256=sha(OUT/'PREPARATION_SHA256SUMS.txt'),frozen_files=len(stable))))


if __name__=='__main__':main()

from run import *
import re

verify()
data=(TASK/'formalization/CoefficientMapFormalTransportData.lean').read_text(encoding='utf8')
pf=(TASK/'formalization/CoefficientMapNumeratorPartialFractions.lean').read_text(encoding='utf8')
def stripped(s): return re.sub(r'--[^\n]*','',re.sub(r'/\*[\s\S]*?\*/','',s))
data_defs=re.findall(r'^def\s+(\w+)',stripped(data),re.M)
pf_defs=re.findall(r'^def\s+(\w+)',stripped(pf),re.M)
data_proofs=re.findall(r'^theorem\s+(\w+)',stripped(data),re.M)
pf_proofs=re.findall(r'^theorem\s+(\w+)',stripped(pf),re.M)
def bodies(s):
    declarations=list(re.finditer(r'^(def|theorem|end)\b[^\n]*',s,re.M))
    return [s[m.start():declarations[i+1].start() if i+1<len(declarations) else len(s)]
            for i,m in enumerate(declarations) if m.group(1)=='def']
alias='import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n'
alias+='namespace ZetaNine.NPFDataValueAliases\nopen CoefficientMapConnection CoefficientMapJet CoefficientMapInjectivity\n'
alias+='\n'.join(bodies(data))+'\nend ZetaNine.NPFDataValueAliases\n'
alias+='namespace ZetaNine.NPFValueAliases\nopen CoefficientMapInjectivity CoefficientMapPartialFractions CoefficientMapFormalTransportData\n'
alias+='\n'.join(bodies(pf))+'\nend ZetaNine.NPFValueAliases\n'
definitions=[];proofs=[];values=[]
for prefix,namespace,names in [('Data','CoefficientMapFormalTransportData',data_defs),('PF','CoefficientMapNumeratorPartialFractions',pf_defs)]:
    aliasnamespace='NPFDataValueAliases' if prefix=='Data' else 'NPFValueAliases'
    for name in names:
        original='ZetaNine.'+namespace+'.'+name
        duplicate='ZetaNine.'+aliasnamespace+'.'+name
        thm='value_'+prefix+'_'+name
        alias+='theorem '+thm+' : '+duplicate+' = '+original+' := rfl\n'
        definitions.append(original)
        values.append({'original':original,'alias':duplicate,'closed_rfl':thm})
for namespace,names in [('CoefficientMapFormalTransportData',data_proofs),('CoefficientMapNumeratorPartialFractions',pf_proofs)]:
    proofs+=['ZetaNine.'+namespace+'.'+name for name in names]
write(PROJECT/'ValueAliases.lean',alias)
helper=(TASK/'formalization/platform/coefficient-map-kernel-bridge/independent/full-kernel-audit.helper.lean').read_text(encoding='utf8')
helper=helper.replace('-- Independent runtime audit helper; prepared but never compiled in this batch.',
                      '-- Own author runtime full Expr audit; helper source copied and hash-bound, no objects borrowed.')
write(OUT/'helper.lean',helper)
typ='import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\n'+helper+'\nrun_meta do\n'
typ+=''.join('  emitIndependentDefinition `'+name+'\n' for name in definitions)
typ+=''.join('  emitIndependentProof `'+name+'\n' for name in proofs)
write(OUT/'types.lean',typ)
val='import ValueAliases\n'+helper+'\nrun_meta do\n'
for row in values:
    val+='  checkIndependentNativeAlias `'+row['original']+' `'+row['alias']+'\n'
    val+='  emitIndependentProof `'+row['closed_rfl']+'\n'
write(OUT/'values.lean',val)
modules=[row['module'] for row in load(OUT/'preparation.json')['reused_parent_objects']]
modules+=['missions.zeta9.formalization.CoefficientMapFormalTransportData','missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions','ValueAliases']
resolver='import Lean\nopen Lean\nrun_meta do\n  let ep ← IO.getEnv "LEAN_PATH"\n'
resolver+='  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (ep.getD "")),("Lean_version",Json.str Lean.versionString)]).compress\n'
resolver+='  for n in ['+', '.join('`'+m for m in modules)+'] do\n    let p ← findOLean n\n'
resolver+='    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str n.toString),("object",Json.str p.toString)]).compress\n'
write(OUT/'resolver.lean',resolver)
boundary=(OUT/'boundary_base.lean').read_text(encoding='utf8')
boundary_names=re.findall(r'^theorem\s+(\w+)',stripped(boundary),re.M)
boundary=boundary.replace('import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions',
                          'import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\nimport Lean',1)
boundary+='\n'+helper.replace('import Lean\n','',1)+'\nrun_meta do\n'
boundary+=''.join('  emitIndependentProof `'+name+'\n' for name in boundary_names)
write(OUT/'boundaries.lean',boundary)
dump(OUT/'audit-plan.json',{'actual_definition_names':definitions,'actual_proof_names':proofs,
                          'full_value_aliases':values,'actual_module_resolver_names':modules,
                          'own_endpoint_and_boundary_names':boundary_names,
                          'no_Lean_invocations_in_audit_preparation':True})
print('Prepared own audits:',len(definitions),'Defs',len(proofs),'proofs',len(values),'full-value aliases',len(modules),'resolver modules.',flush=True)

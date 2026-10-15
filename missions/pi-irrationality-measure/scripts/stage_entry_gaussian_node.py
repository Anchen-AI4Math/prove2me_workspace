"""Pure AP14 staging of the original cleared interpolation-entry proof closure."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_shifted_gaussian_child_mirror as child
import stage_row_translation_data_provider as rowdata
import generate_equation_provenance_probe as equation
parent=child.parent;mean=parent.mean;base=parent.base
TASK,ROOT,V=parent.TASK,parent.ROOT,parent.V
SELF=Path(__file__).resolve();STAGE=V/'ap14/entry-gaussian';COMMIT=parent.COMMIT
AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE=parent.AST,parent.SCOPES,parent.GRAPH,parent.RUNTIME,parent.SNAPSHOT_CORE
TARGET_MODULE='OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic'
TARGET='OAI.PiExponent.InterpolationMatrix.entry_truncatedLog_cleared_gaussian';PLATFORM_NAME=TARGET
TARGET_OUTPUT='Theorems/Thm_'+TARGET.replace('.','_')+'.lean'
SOLUTION_MODULE='Solutions.Sol_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian_ap14_global'
SOLUTION_OUTPUT=SOLUTION_MODULE.replace('.','/')+'.lean'
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT='SourceSnapshot.lean','GeneratedSnapshot.lean'
SOURCE_TYPE_JSON,GENERATED_TYPE_JSON='source-types.json','generated-types.json'
SOURCE_REFS_JSON,GENERATED_REFS_JSON='source-proof-references.json','generated-proof-references.json'
FILES=[TARGET_OUTPUT,SOLUTION_OUTPUT,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT];MODES=['modecheck','emit-olean','modecheck','modecheck'];MANIFESTS=['c1.json','c2.json','c3.json','c4.json'];CERTIFICATE='node-validation.json'
INTERPOLATION=base.ap10.config('interpolation')
IMPORTS=['Mathlib.Tactic',INTERPOLATION['platform_module'],rowdata.PLATFORM_MODULE,child.MODULE]
HELPER_NAMES={rowdata.SOURCE_MODULE:['multiIndex_apply','shifted_X_pow','shifted_product_expansion','shift_monomial_one','shiftCoefficient_eq'],'OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix':['exponentVector_apply'],TARGET_MODULE:['entry_eq_binomial_product','entry_eq_zero_of_not_le','scalar_product_mul_coeff','gaussian_center_cast']}
PREFIXES={m:('OAI.PiExponent.RowTranslation.' if m==rowdata.SOURCE_MODULE else 'OAI.PiExponent.InterpolationMatrix.') for m in HELPER_NAMES}
EQUATIONS=['OAI.PiExponent.InterpolationMatrix.entry.eq_1','OAI.PiExponent.InterpolationMatrix.monomialImage.eq_1','OAI.PiExponent.RowTranslation.shiftCoefficient.eq_1']
read,sha,sha_bytes,encode,need,rel,workspace_rel,verification_rel=parent.read,parent.sha,parent.sha_bytes,parent.encode,parent.need,parent.rel,parent.workspace_rel,parent.verification_rel
PROBE=mean.PROBE.replace('ActualMeanBoundsProofSnapshot','EntryGaussianProofSnapshot')

def authority():
    rowdata.check_only();child.check_only()
    route=read(V/'ap12/arithmetic-route.json');step=next(x for x in route['steps'] if x['output_theorem']==TARGET)
    need(step['ast_unit_count']==14 and step['source_line_count']==185 and step['genuine_lazy_equation_CIs_without_standalone_AST']==EQUATIONS,'Original 14 AST/185-line route differs')
    graph={r['name']:r for r in map(json.loads,GRAPH.read_text(encoding='utf-8').splitlines())};provided=set(INTERPOLATION['names'])|set(rowdata.NAMES)|{parent.TARGET};closure=set();todo=[TARGET]
    while todo:
        n=todo.pop()
        if n in closure:continue
        need(n in graph,'Unknown source graph dependency: '+n);closure.add(n)
        if n not in provided and n not in EQUATIONS:todo+=graph[n]['typeDeps']+graph[n]['valueDeps']
    expected={PREFIXES[m]+n for m,ns in HELPER_NAMES.items() for n in ns}|{TARGET}
    need(closure-provided-set(EQUATIONS)==expected and len(expected)==11,'Exact eleven-theorem proof closure differs')
    ams={m['module']:m for m in read(AST)['modules']};sms={m['source']:m for m in read(SCOPES)['modules']};rows=[];commands={};pins={}
    for m,shorts in HELPER_NAMES.items():
        port=base.source_path(m);original=base.source_path(m,'source');raw=port.read_bytes();orig=original.read_bytes().replace(b'\r\n',b'\n');am=ams[m];sm=sms[m.replace('.','/')+'.lean']
        need(am['source_sha256']==sm['source_sha256']==sha(port),'Exact source inventory changed');pins.update({rel(p):sha(p) for p in [port,original]});selected=[]
        for short in shorts+([TARGET.rsplit('.',1)[1]] if m==TARGET_MODULE else []):
            n=PREFIXES[m]+short;u=next(u for u in am['units'] if n in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==n);a,b=u['start']['offset'],u['end']['offset'];command=raw[a:b]
            contexts=[raw[c['range']['start']['offset']:c['range']['end']['offset']].decode() for c in s['context_commands']]
            need(u['graph_names']==[n] and u['graph_kinds']==['theorem'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'] and s['namespace']==PREFIXES[m][:-1] and orig.count(command.replace(b'\r\n',b'\n'))==1,'Original theorem AST/proof differs: '+n)
            if m==rowdata.SOURCE_MODULE:
                need([c['kind'] for c in s['scope_stack']]==['namespace','namespace','namespace','section'] and s['scope_stack'][-1]['name']=='FiniteExpansion' and contexts==rowdata.authority()[2]['contexts'],'Original generic finite section context differs')
            else:need(all(c['kind']=='namespace' for c in s['scope_stack']) and contexts==['open scoped BigOperators'],'Original namespace context differs')
            selected.append((a,n,command));rows.append({'name':n,'module':m,'kind':'theorem','ast':u,'scope':s,'graph':graph[n],'source':rel(port),'source_sha256':sha(port),'original':rel(original),'original_sha256':sha(original),'start':a,'end':b,'command_sha256':sha_bytes(command),'original_port_command_equal_modulo_line_endings':True})
        commands[m]=selected
    for p in [rowdata.SELF,rowdata.STAGE/'preparation.json',rowdata.STAGE/rowdata.PROVIDER_FILE,child.SELF,child.STAGE/'preparation.json',child.STAGE/child.OUTPUT,child.PUBLISHED,INTERPOLATION['stage']/'preparation.json',INTERPOLATION['stage']/INTERPOLATION['provider_file'],INTERPOLATION['stage']/'actual-provider-validation.json',INTERPOLATION['stage']/'publication/publication.json',V/'ap12/arithmetic-route.json']:pins[rel(p)]=sha(p)
    pub=read(INTERPOLATION['stage']/'publication/publication.json');need(pub['target_readback']['body']['status']=='Definition' and pub['target_readback']['body']['definition'].encode()==(INTERPOLATION['stage']/INTERPOLATION['provider_file']).read_bytes(),'Actual Published Interpolation data body differs')
    return graph,closure,provided,rows,commands,pins

def equation_specs(side):
    return [(n.removesuffix('.eq_1'),rowdata.SOURCE_MODULE if n.startswith('OAI.PiExponent.RowTranslation.') else 'OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix',side+'-equation-'+str(i)+'.json') for i,n in enumerate(EQUATIONS,1)] if side=='source' else [(n.removesuffix('.eq_1'),rowdata.PLATFORM_MODULE if n.startswith('OAI.PiExponent.RowTranslation.') else INTERPOLATION['platform_module'],side+'-equation-'+str(i)+'.json') for i,n in enumerate(EQUATIONS,1)]

def snapshot(side,names,boundary):
    module=TARGET_MODULE if side=='source' else SOLUTION_MODULE;ownerlist=list(HELPER_NAMES)+['SourceSnapshot'] if side=='source' else [SOLUTION_MODULE,INTERPOLATION['platform_module'],rowdata.PLATFORM_MODULE,'GeneratedSnapshot']
    typeout=SOURCE_TYPE_JSON if side=='source' else GENERATED_TYPE_JSON;refsout=SOURCE_REFS_JSON if side=='source' else GENERATED_REFS_JSON
    ns='#['+', '.join('`'+n for n in names)+']'
    init=''
    for primary,owner,out in equation_specs(side):init+='  PiExponentEquationProvenanceProbe.exportEquationSnapshot `'+primary+' '+json.dumps(owner)+' '+json.dumps(workspace_rel(STAGE/out))+' '+json.dumps(side)+'\n'
    return ('import Lean\nimport '+module+'\n\n'+SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n'+base.ap8.PROBE+'\n'+PROBE+'\n'+equation.PROBE+'\nrun_meta do\n'+init+'  PiExponentInterfaceSnapshot.exportSnapshot '+ns+' '+json.dumps(workspace_rel(STAGE/typeout))+'\n  EntryGaussianProofSnapshot.exportBundle '+json.dumps(side)+' '+json.dumps(workspace_rel(STAGE/refsout))+' '+ns+' #['+', '.join(json.dumps(x) for x in ownerlist)+'] #['+', '.join(json.dumps(x) for x in sorted(boundary))+']\n#print axioms '+names[-4]+'\n').encode()

def metadata():
    return {'title':'Gaussian integrality of cleared truncated-logarithm interpolation entries','statement':r'Fix $m$ coordinates and natural vectors $T,q,e$, integer numerators $p$, and assume $q_i\ne0$. Let $j,s,h$ be natural numbers and let $\alpha,\beta\in\mathbb N^m$ satisfy $\alpha_i\le e_i$. Set $r_i=2\mathrm i p_i/q_i$, $G_i=\ell_{T_i}(X)$, and $L_i=\operatorname{lcm}(1,\ldots,T_i)$, where $\ell_T$ is the polynomial truncation of $\log(1+X)$. The original interpolation entry $A_{j,s,\beta;h,\alpha}$ then satisfies'+'\n\n'+r'$$\left(\prod_iL_i^{e_i}\right)\frac{\prod_iq_i^{\alpha_i}}{\prod_iq_i^{\beta_i}}A_{j,s,\beta;h,\alpha}\in\mathbb Z[\mathrm i]\subset\mathbb C.$$'+'\n\n'+'This clears the denominators of the logarithmic interpolation matrix at Gaussian rational centers.','explanation':'Expand translated monomials using binomial coefficients and apply the Gaussian coefficient-integrality theorem to the shifted truncated logarithm factors.','tags':['number-theory','polynomial','linear-algebra','openai-pi-exponent-017'],'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L74-L126'}

def stage_files():
    graph,closure,provided,rows,commands,pins=authority();t=rows[-1];u=t['ast'];command=commands[TARGET_MODULE][-1][2];a=t['start'];need([a,t['end']]==[3245,5875],'Pinned target AST differs');ns,ne=u['nameRange']['start']['offset']-a,u['nameRange']['end']['offset']-a;vs=u['valueStart']['offset']-a;need(command[vs:vs+5]==b':= by','Target proof delimiter differs')
    preamble=(''.join('import '+m+'\n' for m in IMPORTS)+'\nopen OAI.PiExponent OAI.PiExponent.InterpolationMatrix\nopen scoped BigOperators\n\n').encode();formal=command[:ns]+PLATFORM_NAME.encode()+command[ne:vs]+b':= by\n  sorry\n';target=preamble+formal
    parts=[(''.join('import '+m+'\n' for m in IMPORTS)+'\n').encode()]
    for m,selected in commands.items():
        nsname=PREFIXES[m][:-1];header='namespace '+nsname+'\n\nopen scoped BigOperators\n'
        if m==rowdata.SOURCE_MODULE:header+='open MvPolynomial\n\nsection FiniteExpansion\n'+rowdata.authority()[2]['contexts'][-1]+'\n'
        parts.append((header+'\n').encode());parts.extend(c+b'\n\n' for _,n,c in selected if n!=TARGET)
        if m==rowdata.SOURCE_MODULE:parts.append(b'end FiniteExpansion\n\n')
        parts.append(('end '+nsname+'\n\n').encode())
    renamed=command[:ns]+b'solution'+command[ne:];need(renamed[renamed.index(b':= by'):]==command[vs:],'Literal target port proof changed')
    parts+=[b'open OAI.PiExponent OAI.PiExponent.InterpolationMatrix\nopen scoped BigOperators\n\n',renamed+b'\n']
    helpernames=[r['name'] for r in rows[:-1]];boundary=provided&closure;source_names=helpernames+[TARGET]+EQUATIONS;generated_names=helpernames+['solution']+EQUATIONS
    generated={TARGET_OUTPUT:target,SOLUTION_OUTPUT:b''.join(parts),SOURCE_SNAPSHOT:snapshot('source',source_names,boundary),GENERATED_SNAPSHOT:snapshot('generated',generated_names,boundary),'wire-theorem-source.lean':target,'original-target-command.lean.txt':command,'academic-metadata.json':encode(metadata())}
    for m,selected in commands.items():
        for _,n,c in selected:generated['source-units/'+n.replace('.','_')+'.port.lean.txt']=c
    inputs={rel(p):sha(p) for p in [SELF,Path(mean.__file__),Path(base.__file__),AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE,Path(base.ap8.__file__),Path(base.runner.__file__),Path(equation.__file__)]};inputs.update(pins);files={};compile_commands=[]
    for f,mode,mf,imports in zip(FILES,MODES,MANIFESTS,[IMPORTS,IMPORTS,['Lean',TARGET_MODULE],['Lean',SOLUTION_MODULE]],strict=True):
        files[f]={'sha256':sha_bytes(generated[f]),'mode':mode,'emit_olean':mode=='emit-olean','manifest':mf,'imports':imports};generated[mf]=encode({'schema_version':1,'artifact_kind':'ap14-entry-gaussian-bounded-compiler-manifest','output':workspace_rel(STAGE/f),'output_sha256':sha_bytes(generated[f]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        compile_commands.append('python scripts/preflight_staged_module.py '+verification_rel(STAGE/f)+' --root ap14/entry-gaussian --imports-manifest '+verification_rel(STAGE/mf)+' --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    generated['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap14-entry-gaussian-node-preparation','source_name':TARGET,'platform_name':PLATFORM_NAME,'source_module':TARGET_MODULE,'source_commit':COMMIT,'target_ast':u,'target_source_command_sha256':sha_bytes(command),'target_proof_suffix_sha256':sha_bytes(command[vs:]),'target_original_command_equal_modulo_line_endings':True,'global_solution_preserves_literal_source_proof':True,'all_helper_proofs_literal_original':True,'existing_port_adaptations':[],'preamble':preamble.decode(),'formal_statement':formal.decode(),'graph_closure_names':sorted(closure),'provider_subtracted_names':sorted(boundary),'inline_helper_names':helpernames,'inline_exact_source_units':rows[:-1],'target_exact_source_unit':t,'source_type_only_names':source_names,'generated_type_only_names':generated_names,'source_theorem_values_null':True,'generated_theorem_values_null':True,'original_route_AST_units':14,'original_route_source_lines':185,'proof_AST_units_after_data_provider':11,'proof_source_lines_after_data_provider':sum(r['ast']['end']['line']-r['ast']['start']['line']+1 for r in rows),'genuine_lazy_equation_CIs':EQUATIONS,'official_equation_API':'Lean.Meta.getEqnsFor? / Lean.Meta.isEqnThm? with full primary Def values and closed equation type/Std3','input_hashes':inputs,'files':files,'compile_commands':compile_commands,'metadata':metadata(),'exactName_lookup_required_by_root':TARGET,'local_closed_AP13_child_mirror':rel(child.STAGE/'preparation.json'),'required_local_child_certificate':rel(child.STAGE/child.CERTIFICATE),'required_rowdata_certificate':rel(rowdata.STAGE/'actual-provider-validation.json'),'blanket_Mathlib_import':False,'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False,'proposal_status':'Draft'})
    generated['compile-commands.txt']=('\n'.join(compile_commands)+'\n').encode();return generated

def check_only():
    generated=stage_files()
    for f,raw in generated.items():need((STAGE/f).is_file() and (STAGE/f).read_bytes()==raw,'Immutable stage differs: '+f)
    for f,mf in zip(FILES,MANIFESTS,strict=True):m=read(STAGE/mf);base.runner.verify_manifest_inputs(m);base.runner.verify_source_certificate(STAGE/f,m)
    return {'checked_files':len(generated),'source_AST_units':11,'inline_helpers':10,'genuine_equations':3,'all_original_port_proofs_equal_modulo_line_endings':True,'all_hashes_match':True,'Lean_started':False,'API_used':False,'validated':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--prepare',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for f,raw in stage_files().items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()

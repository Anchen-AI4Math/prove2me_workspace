"""Small-memory generation of server-verifiable pieces; never invokes Lean."""
import hashlib
import json
import re
from pathlib import Path
import generate_milestone_certificate as gen

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PLATFORM=HERE/'platform'
ACTUAL=ROOT/'Solutions'/'SnakyMilestones'
SOURCE='https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean'
NS='OAI.SnakyCertificate.MilestoneChecks'
OPTIONS='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\n'

def module(name):
    return 'Theorems.Thm_'+name.replace('.','_')

def projection(name,pos):
    return name+'.2'*pos+'.1'

def spec(slug,name,title,statement,preamble,body,description,explanation):
    path=PLATFORM/(slug+'-proof.lean')
    path.write_text(body,encoding='utf-8')
    obj={'theorem_name':name,'theorem_title':title,'formal_statement':statement,
         'preamble':preamble,'natural_language_statement':description,'source':SOURCE,
         'proof_file':path.relative_to(ROOT).as_posix(),'explanation':explanation}
    (PLATFORM/(slug+'.json')).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return slug

def main():
    journal=HERE/'platform'/'journal.json'
    if journal.exists() and any(k.startswith('definition:Snaky35') for k in json.loads(journal.read_text(encoding='utf-8'))):
        raise RuntimeError('Reuse the generated milestone35 manifest; published module sources must not be regenerated.')
    gen.main()
    original=ACTUAL/'Certificate35.lean'
    full=original.read_text(encoding='utf-8')
    (PLATFORM/'milestone-certificate-monolithic.lean').write_text(full,encoding='utf-8')
    matches=list(re.finditer(r'^def data_(\d+) : RowData := .+\n',full,re.M))
    assert len(matches)==616
    literals={int(m[1]):m[0] for m in matches}
    tail_start=full.index('def indices : List')
    bodies={int(m[1]):full[m.end():matches[k+1].start() if k+1<len(matches) else tail_start]
            for k,m in enumerate(matches)}
    lookup_start=full.index('theorem chunk_size_0')
    core=full[full.index('theorem row_ext'):lookup_start]
    lookups=full[lookup_start:matches[0].start()]
    prefix='namespace '+NS+'\nopen OAI.SnakyCertificate\n'
    corepath=ROOT/'Definitions'/'Def_Snaky35Core.lean'
    corepath.write_text('import Definitions.Def_SnakyCertificate\n'+prefix+core+'\nend '+NS+'\n',encoding='utf-8')
    definitions=[{'file':corepath.relative_to(ROOT).as_posix(),
                  'description':'Auxiliary predicates for the original 35-move finite certificate: row subset/origin/height conditions and table-entry index/nonempty/backward-reference conditions, with the structural three-field extensionality lemma for RowData. No certificate correctness or game-winning result is assumed.'}]
    lookup_name=NS+'.chunk_lookups'
    clauses=[f'(∀ j : ℕ, j < {20 if n<30 else 10} → entryAt ({20*n+6} + j) = tableChunk_{n}[j]?.getD emptyEntry)' for n in range(31)]
    lookup_type=' ∧ '.join(clauses+['True'])
    lookup_pre='import Definitions.Def_Snaky35Core\nopen '+NS+' OAI.SnakyCertificate\n'
    lookup_body='import Definitions.Def_Snaky35Core\n'+OPTIONS+prefix+lookups
    lookup_body+='theorem chunk_lookups : '+lookup_type+' := by\n  exact ⟨'+', '.join(f'entry_chunk_{n}' for n in range(31))+', trivial⟩\nend '+NS+'\n'
    (ACTUAL/'Lookup35.lean').write_text(lookup_body,encoding='utf-8')
    lookup_upload=lookup_body+'open '+NS+' OAI.SnakyCertificate\ntheorem solution : '+lookup_type+' := chunk_lookups\n'
    lookup_slug=spec('milestone35-lookups',lookup_name,'35-move certificate: exact lookup in all 31 table chunks',
        'theorem '+lookup_name+' : '+lookup_type+' := by sorry',lookup_pre,lookup_upload,
        'Each of the 31 printed table chunks occupies its exact consecutive position in the original 610-entry certificate array, uniformly over the indices within that chunk.',
        'The chunk sizes are checked by kernel reduction. Array append lookup lemmas follow the balanced table expression; arithmetic identifies the local index. This proves uniform chunk lookup, so later row checks need evaluate only a chunk of at most 20 entries. These lookup proofs were included in the successful local 12-row probe before local compilation was disabled after the computer freeze.')
    groups=[]
    lo=0
    while lo<616:
        hi=lo
        size=0
        while hi<616 and hi-lo<32 and (size+len(literals[hi].encode('utf-8'))<=25000 or hi==lo):
            size+=len(literals[hi].encode('utf-8')); hi+=1
        groups.append((lo,hi));lo=hi
    owner={i:n for n,(lo,hi) in enumerate(groups) for i in range(lo,hi)}
    parts=[]
    aliases='\n'.join(f'theorem entry_chunk_{n} (j : ℕ) (hj : j < {20 if n<30 else 10}) : entryAt ({20*n+6} + j) = tableChunk_{n}[j]?.getD emptyEntry := ({projection("chunk_lookups",n)}) j hj' for n in range(31))+'\n'
    names=[NS+f'.block{n:02}_correct' for n in range(len(groups))]
    for n,(lo,hi) in enumerate(groups):
        cache='Snaky35Cache'+f'{n:02}'
        cachepath=ROOT/'Definitions'/('Def_'+cache+'.lean')
        cache_import='import Definitions.Def_Snaky35Core\n' if n==0 else f'import Definitions.Def_Snaky35Cache{n-1:02}\n'
        cachepath.write_text(cache_import+prefix+'\n'.join(literals[i] for i in range(lo,hi))+'end '+NS+'\n',encoding='utf-8')
        definitions.append({'file':cachepath.relative_to(ROOT).as_posix(),
          'description':f'Candidate literal RowData values for original 35-move certificate rows {lo} through {hi-1}, consisting only of the required cells, the envelope cells, and height. Their equality to the original rowAt recursion is established by separate support theorems; these literals alone do not assert correctness.'})
        typ=' ∧ '.join(f'(rowAt {i} = data_{i} ∧ Good (rowAt {i}) ∧ '+(f'EntryGood {i}' if i>=6 else 'True')+')' for i in range(lo,hi))+' ∧ True'
        body=''.join(bodies[i] for i in range(lo,hi))
        name=names[n]
        tuple_proof='⟨'+', '.join(f'⟨row_{i}, good_{i}, '+(f'entry_good_{i}' if i>=6 else 'trivial')+'⟩' for i in range(lo,hi))+', trivial⟩'
        actual_import=f'import Definitions.Def_{cache}\nimport Solutions.SnakyMilestones.'+('Lookup35' if n==0 else f'Certificate35Part{n-1:02}')+'\n'
        actual=actual_import+OPTIONS+prefix+body+f'theorem block{n:02}_correct : {typ} := by\n  exact {tuple_proof}\nend '+NS+'\n'
        (ACTUAL/f'Certificate35Part{n:02}.lean').write_text(actual,encoding='utf-8')
        earlier=sorted({int(c) for c in re.findall(r'row_(\d+)',body) if int(c)<lo})
        imports=f'import Definitions.Def_{cache}\nimport '+module(lookup_name)+'\n'
        imports+=''.join('import '+module(names[k])+'\n' for k in sorted({owner[i] for i in earlier}))
        projected=''.join(f'theorem row_{i} : rowAt {i} = data_{i} := ({projection(names[owner[i]],i-groups[owner[i]][0])}).1\n' for i in earlier)
        upload=imports+OPTIONS+prefix+aliases+projected+body+'end '+NS+'\nopen '+NS+' OAI.SnakyCertificate\n'
        upload+=f'theorem solution : {typ} := by\n  exact {tuple_proof}\n'
        parts.append(spec(f'milestone35-block{n:02}',name,f'35-move certificate: exact rows {lo}–{hi-1}',
            'theorem '+name+' : '+typ+' := by sorry',f'import Definitions.Def_{cache}\nopen '+NS+' OAI.SnakyCertificate\n',upload,
            f'Original certificate rows {lo} through {hi-1} equal the explicit candidate required set, envelope and height; each row has the required subset/origin/height invariants. The nonbase entries have their exact indices, nonempty placement lists and strictly backward references.',
            'Unfold rowAt once, use the proved chunk lookup, and replace strictly earlier children by their proved row equalities. The three fields of the finite fork and placement computation are checked separately by decide +kernel. The row and entry predicates are also checked by the kernel. This is a bounded piece of the original 35-move certificate, generated without starting local Lean after the resource incident; the platform verifier checks the complete proof.'))
    root_tail=full[tail_start:]
    actual_root=f'import Solutions.SnakyMilestones.Certificate35Part{len(groups)-1:02}\n'+OPTIONS+prefix+root_tail
    original.write_text(actual_root,encoding='utf-8')
    rootimports=''.join('import '+module(name)+'\n' for name in names)
    projected=[]
    for i in range(616):
        ref=projection(names[owner[i]],i-groups[owner[i]][0])
        projected.extend([f'theorem row_{i} : rowAt {i} = data_{i} := ({ref}).1',
                          f'theorem good_{i} : Good (rowAt {i}) := ({ref}).2.1'])
        if i>=6:
            projected.append(f'theorem entry_good_{i} : EntryGood {i} := ({ref}).2.2')
    (PLATFORM/'milestone-certificate-proof.lean').write_text(rootimports+OPTIONS+prefix+'\n'.join(projected)+'\n'+root_tail,encoding='utf-8')
    manifest={'definitions':definitions,'lookup':lookup_slug,'parts':parts,'groups':groups,
              'literal_sha256':{str(i):hashlib.sha256(literals[i].encode('utf-8')).hexdigest() for i in range(616)},
              'no_local_lean':True,'root_proof':'missions/snaky-21/platform/milestone-certificate-proof.lean'}
    (PLATFORM/'milestone35-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    scopepath=HERE/'scope.json';scope=json.loads(scopepath.read_text(encoding='utf-8'))
    if 'Definitions/Def_Snaky35*.lean' not in scope['sources']:
        scope['sources'].append('Definitions/Def_Snaky35*.lean')
    scopepath.write_text(json.dumps(scope,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('REMOTE SOURCE READY:',len(groups),'row groups; no Lean invoked.',flush=True)

if __name__=='__main__':
    main()

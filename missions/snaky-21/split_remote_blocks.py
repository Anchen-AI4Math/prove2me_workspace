"""Split each row proof into groups of eight; no local Lean invocation."""
import json
import re
from pathlib import Path
from prepare_remote_milestone import HERE,ROOT,PLATFORM,ACTUAL,NS,OPTIONS,SOURCE,module,projection,spec

m=json.loads((PLATFORM/'milestone35-manifest.json').read_text(encoding='utf-8'))
assert 'subparts' not in m
groups=m['groups']
owner={i:n for n,(lo,hi) in enumerate(groups) for i in range(lo,hi)}
parent_names=[NS+f'.block{n:02}_correct' for n in range(len(groups))]
lookup_name=NS+'.chunk_lookups'
prefix='namespace '+NS+'\nopen OAI.SnakyCertificate\n'
subparts={}
for n,(begin,end) in enumerate(groups):
    actual_path=ACTUAL/f'Certificate35Part{n:02}.lean'
    text=actual_path.read_text(encoding='utf-8')
    parent_at=text.index(f'theorem block{n:02}_correct')
    starts={}
    for match in re.finditer(r'^theorem (?:entry_(\d+)_checked|row_(\d+))',text[:parent_at],re.M):
        i=int(match[1] or match[2])
        starts.setdefault(i,match.start())
    assert sorted(starts)==list(range(begin,end))
    bodies={i:text[starts[i]:starts[i+1] if i+1<end else parent_at] for i in range(begin,end)}
    ranges=[(lo,min(lo+8,end)) for lo in range(begin,end,8)]
    group_names=[NS+f'.block{n:02}_group{g:02}_correct' for g in range(len(ranges))]
    group_owner={i:g for g,(lo,hi) in enumerate(ranges) for i in range(lo,hi)}
    slugs=[]
    for g,(lo,hi) in enumerate(ranges):
        code=''.join(bodies[i] for i in range(lo,hi))
        typ=' ∧ '.join(f'(rowAt {i} = data_{i} ∧ Good (rowAt {i}) ∧ '+(f'EntryGood {i}' if i>=6 else 'True')+')' for i in range(lo,hi))+' ∧ True'
        tuple_proof='⟨'+', '.join(f'⟨row_{i}, good_{i}, '+(f'entry_good_{i}' if i>=6 else 'trivial')+'⟩' for i in range(lo,hi))+', trivial⟩'
        cache=f'Definitions.Def_Snaky35Cache{n:02}'
        previous_actual=f'Certificate35Block{n:02}Group{g-1:02}' if g else (f'Certificate35Part{n-1:02}' if n else 'Lookup35')
        actual='import '+cache+'\nimport Solutions.SnakyMilestones.'+previous_actual+'\n'+OPTIONS+prefix
        actual+='attribute [local irreducible] rowAt\n'+code+f'theorem block{n:02}_group{g:02}_correct : {typ} := by\n  exact {tuple_proof}\nend '+NS+'\n'
        (ACTUAL/f'Certificate35Block{n:02}Group{g:02}.lean').write_text(actual,encoding='utf-8')
        earlier=sorted({int(i) for i in re.findall(r'row_(\d+)',code) if int(i)<lo})
        refs={}
        for i in earlier:
            refs[i]=projection(parent_names[owner[i]],i-groups[owner[i]][0]) if i<begin else projection(group_names[group_owner[i]],i-ranges[group_owner[i]][0])
        imported=sorted({parent_names[owner[i]] if i<begin else group_names[group_owner[i]] for i in earlier})
        imports='import '+cache+'\nimport '+module(lookup_name)+'\n'+''.join('import '+module(name)+'\n' for name in imported)
        needed=sorted({int(k) for k in re.findall(r'entry_chunk_(\d+)',code)})
        aliases=''.join(f'theorem entry_chunk_{k} (j : ℕ) (hj : j < {20 if k<30 else 10}) : entryAt ({20*k+6} + j) = tableChunk_{k}[j]?.getD emptyEntry := ({projection("chunk_lookups",k)}) j hj\n' for k in needed)
        previous_rows=''.join(f'theorem row_{i} : rowAt {i} = data_{i} := ({refs[i]}).1\n' for i in earlier)
        upload=imports+OPTIONS+prefix+'attribute [local irreducible] rowAt\n'+aliases+previous_rows+code+'end '+NS+'\nopen '+NS+' OAI.SnakyCertificate\n'
        upload+=f'theorem solution : {typ} := by\n  exact {tuple_proof}\n'
        slug=f'milestone35-block{n:02}-group{g:02}'
        slugs.append(spec(slug,group_names[g],f'35-move certificate: exact rows {lo}–{hi-1}',
          'theorem '+group_names[g]+' : '+typ+' := by sorry',
          'import '+cache+'\nopen '+NS+' OAI.SnakyCertificate\n',upload,
          f'The original certificate rows {lo} through {hi-1} have their exact required sets, envelopes and heights and the specified subset/origin/height invariants. Nonbase entries have correct indices, nonempty term lists and backward references.',
          'Use the proved chunk lookup and exact earlier child rows, then check the three fields separately with decide +kernel. Each row and entry predicate is also checked by the kernel. This group has at most eight rows to fit the platform compiler budget. The recursive rowAt definition is locally marked irreducible to prevent incidental eager unfolding; its defining equation is explicitly used once for each row. No local Lean process is started on the user\'s computer.'))
    parent_slug=m['parts'][n]
    parent_spec_path=PLATFORM/(parent_slug+'.json')
    parent_spec=json.loads(parent_spec_path.read_text(encoding='utf-8'))
    typ=parent_spec['formal_statement'].split(' : ',1)[1].rsplit(' := by sorry',1)[0]
    parent_tuple='⟨'+', '.join(projection(group_names[group_owner[i]],i-ranges[group_owner[i]][0]) for i in range(begin,end))+', trivial⟩'
    public=''.join('import '+module(name)+'\n' for name in group_names)+OPTIONS+'open '+NS+' OAI.SnakyCertificate\n'
    public+=f'theorem solution : {typ} := by\n  exact {parent_tuple}\n'
    (ROOT/parent_spec['proof_file']).write_text(public,encoding='utf-8')
    parent_spec['explanation']='Assemble the exact row, invariant and entry facts from the proved groups of at most eight rows. The statement and all candidate data are unchanged; this is a projection-only reduction that fits the server budget.'
    parent_spec_path.write_text(json.dumps(parent_spec,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    actual='import Solutions.SnakyMilestones.'+f'Certificate35Block{n:02}Group{len(ranges)-1:02}'+'\n'+OPTIONS+prefix
    # Actual group modules expose each real row proof directly.
    actual_tuple='⟨'+', '.join(f'⟨row_{i}, good_{i}, '+(f'entry_good_{i}' if i>=6 else 'trivial')+'⟩' for i in range(begin,end))+', trivial⟩'
    actual+=f'theorem block{n:02}_correct : {typ} := by\n  exact {actual_tuple}\nend '+NS+'\n'
    actual_path.write_text(actual,encoding='utf-8')
    subparts[parent_slug]=slugs
m['subparts']=subparts
(PLATFORM/'milestone35-manifest.json').write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
print('Prepared',sum(map(len,subparts.values())),'small groups; no Lean invoked.')

"""Rebuild the captain's 35-move table, then emit incremental kernel checks."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / 'Definitions' / 'Def_SnakyCertificate.lean'

def orient(r, p):
    x,y=p
    return [(x,y),(y,x),(x,-y),(-y,x),(-x,y),(y,-x),(-x,-y),(-y,-x)][r]

def place(s, r, x, y):
    return {(a+x,b+y) for a,b in (orient(r,p) for p in s)}

def cells(s):
    if not s:
        return '∅'
    return '{'+', '.join(f'({x}, {y})' for x,y in sorted(s))+'}'

def parse_table(expr):
    expr=expr.strip()
    while expr.startswith('('):
        depth=0
        for k,ch in enumerate(expr):
            depth+=(ch=='(')-(ch==')')
            if depth==0:
                break
        if k!=len(expr)-1:
            break
        expr=expr[1:-1].strip()
    if re.fullmatch(r'tableChunk_\d+',expr):
        return int(expr.split('_')[-1])
    depth=0
    for k,ch in enumerate(expr):
        depth+=(ch=='(')-(ch==')')
        if not depth and expr[k:k+2]=='++':
            return (parse_table(expr[:k]),parse_table(expr[k+2:]))
    raise ValueError('Unexpected table expression: '+expr)

def chunk_leaves(tree):
    return [tree] if isinstance(tree,int) else chunk_leaves(tree[0])+chunk_leaves(tree[1])

def tree_text(tree):
    return f'tableChunk_{tree}' if isinstance(tree,int) else f'({tree_text(tree[0])} ++ {tree_text(tree[1])})'

def lookup_proofs(source):
    tree=parse_table(re.search(r'def table : Array Entry := (.*)',source).group(1))
    sizes=', '.join(f'chunk_size_{j}' for j in range(31))
    code=[]
    for n in range(31):
        code.append(f'theorem chunk_size_{n} : tableChunk_{n}.size = {20 if n<30 else 10} := by decide +kernel')
    for n in range(31):
        size=20 if n<30 else 10
        offset=20*n
        code.extend([f'theorem entry_chunk_{n} (j : ℕ) (hj : j < {size}) :',
                     f'    entryAt ({offset+6} + j) = tableChunk_{n}[j]?.getD emptyEntry := by',
                     '  unfold entryAt',
                     f'  have hstart : {offset+6} + j - 6 = {offset} + j := by omega',
                     '  rw [hstart, table]'])
        node=tree
        while not isinstance(node,int):
            left,right=node
            count=sum(20 if i<30 else 10 for i in chunk_leaves(left))
            isleft=n in chunk_leaves(left)
            direction='left' if isleft else 'right'
            cmp=f'{offset} + j < {count}' if isleft else f'{count} ≤ {offset} + j'
            code.extend([f'  rw [Array.getElem?_append_{direction} (xs := {tree_text(left)})',
                         f'    (ys := {tree_text(right)}) (i := {offset} + j) (by',
                         f'      have hn : {cmp} := by omega',
                         f'      simpa only [Array.size_append, {sizes}, Nat.reduceAdd] using hn)]'])
            if isleft:
                node=left
            else:
                code.extend([f'  simp only [Array.size_append, {sizes}, Nat.reduceAdd]',
                             f'  have hsub : {offset} + j - {count} = {offset-count} + j := by omega',
                             '  try rw [hsub]'])
                node=right
                offset-=count
        code.append('  try simp only [Nat.zero_add]')
        code.append('  try rfl')
        code.append('')
    return code

def main(limit=616):
    source=SOURCE.read_text(encoding='utf-8')
    entries={int(i):[tuple(map(int,t)) for t in re.findall(r'⟨(\d+), (\d+), (\d+), (\d+)⟩',body)]
             for i,body in re.findall(r'def entry_(\d+) : Entry := ⟨\d+, \[(.*?)\]⟩',source)}
    assert sorted(entries)==list(range(6,616))
    assert sum(map(len,entries.values()))==1837
    points=[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
    rows=[]
    for x,y in points:
        h={(a-x,b-y) for a,b in points}
        rows.append((h-{(0,0)},h,1))
    for i,terms in entries.items():
        assert terms and all(c<i and r<8 and x<10 and y<10 for c,r,x,y in terms)
        children=[(place(rows[c][0],r,x-4,y-4),place(rows[c][1],r,x-4,y-4),rows[c][2])
                  for c,r,x,y in terms]
        a=set().union(*(d[0] for d in children)) | set.intersection(*(d[1] for d in children))
        h=set().union(*(d[1] for d in children)) | {(0,0)}
        rows.append((a-{(0,0)},h,1+max(d[2] for d in children)))
    assert all(a<h and (0,0) in h-a and v<=34 for a,h,v in rows)
    for i,p,n,v,bad in [(557,(-1,0),118,19,lambda x,y:x<=-3 and y<=-2),
                       (595,(-1,0),222,27,lambda x,y:x==-2 and y<=-2),
                       (603,(-1,0),275,27,lambda x,y:x<=-3 and y==0),
                       (615,(1,0),686,34,lambda x,y:(x,y)==(1,-1))]:
        a,h,z=rows[i]
        assert a=={p} and len(h)==n and z==v and not any(bad(x,y) for x,y in h)
    code=['import Definitions.Def_SnakyCertificate',
          'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
          'set_option linter.unusedSimpArgs false',
          'namespace OAI.SnakyCertificate.MilestoneChecks',
          'open OAI.SnakyCertificate','',
          'theorem row_ext {c d : RowData} (hA : c.A = d.A)',
          '    (hH : c.H = d.H) (hh : c.height = d.height) : c = d := by',
          '  cases c; cases d; cases hA; cases hH; cases hh; rfl','',
          'def Good (d : RowData) : Prop :=',
          '  d.A ⊆ d.H ∧ origin ∈ d.H ∧ origin ∉ d.A ∧ d.height ≤ 34','',
          'def EntryGood (i : ℕ) : Prop :=',
          '  let e := entryAt i',
          '  e.index = i ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < i','']
    code.extend(lookup_proofs(source))
    for i,(a,h,v) in enumerate(rows[:limit]):
        code.append(f'def data_{i} : RowData := ⟨{cells(a)}, {cells(h)}, {v}⟩')
        if i<6:
            code.append(f'theorem row_{i} : rowAt {i} = data_{i} := by apply row_ext <;> decide +kernel')
        else:
            terms=entries[i]
            code.extend([f'theorem entry_{i}_checked : entryAt {i} = entry_{i} := by',
                         f'  rw [entry_chunk_{(i-6)//20} {(i-6)%20} (by decide)]',
                         '  decide +kernel'])
            rhs=', '.join(f'placeRow ⟨{c}, {r}, {x}, {y}⟩ (rowAt {c})' for c,r,x,y in terms)
            code.extend([f'theorem row_{i} : rowAt {i} = data_{i} := by',
                         f'  rw [rowAt, dif_neg (by decide : ¬ {i} < 6), entry_{i}_checked]',
                         f'  change forkRow [{rhs}] = data_{i}',
                         '  rw ['+', '.join(f'row_{c}' for c in dict.fromkeys(t[0] for t in terms))+']',
                         '  apply row_ext <;> decide +kernel'])
            code.extend([f'theorem entry_good_{i} : EntryGood {i} := by',
                         '  unfold EntryGood',f'  rw [entry_{i}_checked]',
                         '  decide +kernel'])
        code.extend([f'theorem good_{i} : Good (rowAt {i}) := by',
                     f'  rw [row_{i}]','  unfold Good','  decide +kernel'])
        code.append('')
        if i % 32 == 31 or i==limit-1:
            code.append(f'#check row_{i}')
    if limit==616:
        indices='['+', '.join(map(str,range(616)))+']'
        code.extend([f'def indices : List ℕ := {indices}',
                     'theorem all_good : ∀ i ∈ indices, Good (rowAt i) := by',
                     '  simp only [indices, List.forall_mem_cons]',
                     '  exact ⟨'+', '.join(f'good_{i}' for i in range(616))+', by simp⟩','',
                     'theorem all_rows : AllRows := by',
                     '  intro i hi',
                     '  apply all_good i',
                     '  change i ∈ List.range 616',
                     '  exact List.mem_range.mpr hi','',
                     'def entryIndices : List ℕ := ['+', '.join(map(str,range(6,616)))+']',
                     'theorem all_entry_good : ∀ i ∈ entryIndices, EntryGood i := by',
                     '  simp only [entryIndices, List.forall_mem_cons]',
                     '  exact ⟨'+', '.join(f'entry_good_{i}' for i in range(6,616))+', by simp⟩','',
                     'theorem table_size : table.size = 610 := by decide +kernel',
                     'theorem table_valid : TableValid := by',
                     '  refine ⟨table_size, ?_⟩',
                     '  intro k hk',
                     '  have hk610 : k < 610 := by simpa only [table_size] using hk',
                     '  have he := all_entry_good (k + 6) (by',
                     '    change k + 6 ∈ (List.range 610).map (fun j => j + 6)',
                     '    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk610, rfl⟩)',
                     '  unfold EntryGood at he',
                     '  simp only [entryAt, Nat.add_sub_cancel] at he',
                     '  refine ⟨he.1, he.2.1, ?_⟩',
                     '  intro t ht',
                     '  rw [he.1]',
                     '  exact he.2.2 t ht',''])
        for i,p,n,v,omitted,bad in [
            (557,'(-1, 0)',118,19,'{p | p.1 ≤ -3 ∧ p.2 ≤ -2}','q.1 ≤ -3 ∧ q.2 ≤ -2'),
            (595,'(-1, 0)',222,27,'{p | p.1 = -2 ∧ p.2 ≤ -2}','q.1 = -2 ∧ q.2 ≤ -2'),
            (603,'(-1, 0)',275,27,'{p | p.1 ≤ -3 ∧ p.2 = 0}','q.1 ≤ -3 ∧ q.2 = 0'),
            (615,'(1, 0)',686,34,'{(1, -1)}','q = (1, -1)')]:
            code.extend([f'theorem output_{i} : Output {i} {p} {n} {v} {omitted} := by',
                         '  unfold Output',f'  rw [row_{i}]',
                         '  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩',
                         '  apply Set.disjoint_left.mpr',
                         '  intro p hp ho',
                         f'  have safe : ∀ q ∈ data_{i}.H, ¬ ({bad}) := by decide +kernel',
                         '  exact safe p hp ho',''])
        code.extend(['theorem certificate_complete :',
                     '    TableValid ∧ placementCount = 1837 ∧',
                     '    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧',
                     '    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧',
                     '    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧',
                     '    Output 615 (1, 0) 686 34 {(1, -1)} ∧ AllRows := by',
                     '  exact ⟨table_valid, by decide +kernel, output_557, output_595,',
                     '    output_603, output_615, all_rows⟩',''])
    code.append('end OAI.SnakyCertificate.MilestoneChecks')
    if limit==616:
        code.extend(['open OAI.SnakyCertificate',
                     'theorem solution :',
                     '    TableValid ∧ placementCount = 1837 ∧',
                     '    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧',
                     '    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧',
                     '    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧',
                     '    Output 615 (1, 0) 686 34 {(1, -1)} ∧ AllRows := by',
                     '  exact OAI.SnakyCertificate.MilestoneChecks.certificate_complete',''])
        code.append('#print axioms OAI.SnakyCertificate.MilestoneChecks.certificate_complete')
    folder=ROOT/'Solutions'/'SnakyMilestones'
    folder.mkdir(exist_ok=True)
    path=folder/('Certificate35.lean' if limit==616 else 'CertificateProbe.lean')
    path.write_text('\n'.join(code)+'\n',encoding='utf-8')
    report={'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'numbered_rows':len(rows),'placements':sum(map(len,entries.values())),
            'generated_rows':limit,'generated_bytes':path.stat().st_size,
            'endpoints':{str(i):{'A':sorted(rows[i][0]),'envelope':len(rows[i][1]),'height':rows[i][2]}
                         for i in [557,595,603,615]}}
    (HERE/'verification'/'milestone-certificate-rebuild.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report),flush=True)

if __name__=='__main__':
    import sys
    main(int(sys.argv[1]) if len(sys.argv)>1 else 616)

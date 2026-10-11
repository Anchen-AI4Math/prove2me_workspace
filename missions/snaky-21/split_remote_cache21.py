"""Split the failed five-row definition without changing any row declaration."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
j=json.loads((HERE/'platform'/'journal.json').read_text(encoding='utf-8'))
assert j['definition:Snaky35Cache21']['status']=='FAILED'
p=ROOT/'Definitions'/'Def_Snaky35Cache21.lean'
old=p.read_text(encoding='utf-8')
rows=re.findall(r'^(def data_(\d+) : RowData := .+)$',old,re.M)
assert len(rows)==5
m=json.loads((HERE/'platform'/'milestone35-manifest.json').read_text(encoding='utf-8'))
fragments=[]
names=[]
for decl,i in rows:
    name='Snaky35Cache21Row'+i
    names.append(name)
    file=ROOT/'Definitions'/('Def_'+name+'.lean')
    code='import Definitions.Def_Snaky35Core\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace OAI.SnakyCertificate.MilestoneChecks\nopen OAI.SnakyCertificate\n'+decl+'\nend OAI.SnakyCertificate.MilestoneChecks\n'
    file.write_text(code,encoding='utf-8')
    fragments.append({'file':file.relative_to(ROOT).as_posix(),
      'description':'Candidate literal required cells, envelope cells and height for original 35-move certificate row '+i+'. A separate row equality theorem verifies these values against the original recursive rowAt; the definition alone does not assert correctness.'})
wrapper=''.join('import Definitions.Def_'+name+'\n' for name in names)
wrapper+='namespace OAI.SnakyCertificate.MilestoneChecks\ndef cache21Rows : List ℕ := ['+', '.join(i for decl,i in rows)+']\nend OAI.SnakyCertificate.MilestoneChecks\n'
p.write_text(wrapper,encoding='utf-8')
index=next(k for k,v in enumerate(m['definitions']) if v['file'].endswith('Def_Snaky35Cache21.lean'))
m['definitions'][index]['requires']=names
m['definitions'][index:index]=fragments
m['cache21_split']={'rows':[int(i) for decl,i in rows],'row_declarations_preserved':True,
  'previous_source_sha256':hashlib.sha256(old.encode()).hexdigest(),
  'wrapper_sha256':hashlib.sha256(wrapper.encode()).hexdigest()}
(HERE/'platform'/'milestone35-manifest.json').write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
print('Prepared five exact row fragments; no Lean invoked.')

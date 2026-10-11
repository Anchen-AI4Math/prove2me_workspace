"""Bound server-only source chunks without altering the actual audited sources."""
import hashlib
import json
import re
from pathlib import Path
import publish

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'

def main():
    manifest={}
    journal=publish.read_journal()
    for part in range(12):
        original=ROOT/'Definitions'/f'Def_Snaky21Calc11Part{part:02}.lean'
        text=original.read_text(encoding='utf-8')
        if journal.get('definition:'+original.stem.removeprefix('Def_'),{}).get('status')=='PUBLISHED':
            continue
        declarations=re.findall(r'^def calc11_[^\n]+',text,re.M)
        chunks=[[]]
        for decl in declarations:
            if chunks[-1] and sum(len(x.encode())+2 for x in chunks[-1])+len(decl.encode())>30000:
                chunks.append([])
            chunks[-1].append(decl)
        # These are literal constants: they do not reference any other cache.
        # Importing only Data11 avoids materializing a long irrelevant chain.
        dependency='Definitions.Def_Snaky21Data11'
        paths=[]
        for i,chunk in enumerate(chunks):
            name=f'Snaky21CachePart{part:02}Fragment{i:02}'
            path=OUT/('Def_'+name+'.lean')
            payload='import '+dependency+'\n\nnamespace OAI.Snaky21.Certificate\n\n'+'\n\n'.join(chunk)+'\n\nend OAI.Snaky21.Certificate\n'
            path.write_text(payload,encoding='utf-8')
            paths.append(str(path.relative_to(ROOT)))
        if [x for chunk in chunks for x in chunk]!=declarations:
            raise RuntimeError('Server literal declarations changed')
        wrapper=OUT/f'Def_Snaky21Calc11Part{part:02}.lean'
        first=re.search(r'^def (calc11_\S+) : ([^\n]+?) :=',text,re.M)
        own_api=f'abbrev OAI.Snaky21.Certificate.cache_part_{part:02}_first : {first.group(2)} := OAI.Snaky21.Certificate.{first.group(1)}\n'
        wrapper.write_text('-- Same ordered literal declarations as the actual local module.\n'+''.join('import Definitions.'+Path(p).stem+'\n' for p in paths)+'\n'+own_api,encoding='utf-8')
        manifest[str(part)]={'actual_file':str(original.relative_to(ROOT)),'actual_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
            'fragments':paths,'wrapper':str(wrapper.relative_to(ROOT)),'declarations_identical_and_ordered':True,'structural_api':own_api.strip()}
    (OUT/'server-cache-fragments.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print('Prepared server fragments for',list(manifest),'with identical literal declarations; actual sources unchanged.')

if __name__=='__main__':
    main()

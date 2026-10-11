"""Fetch pinned public sources and perform a limited lexical audit; never run them."""
from pathlib import Path
import urllib.request, json, hashlib, io, zipfile, re

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/public-zeta5-audit-2026-09-29'
SHA='fc2fefa77076e22e7e80b4c101ded5a98d53e14d'
def get(url):
    return urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'zeta9-source-audit'}),timeout=90).read()
def strip_comments_strings(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':string=True;i+=1
        else:out.append(s[i]);i+=1
    return ''.join(out)
def main():
    OUT.mkdir(exist_ok=True)
    url=f'https://codeload.github.com/danromik/zeta5-irrationality/zip/{SHA}'
    archive=get(url); z=zipfile.ZipFile(io.BytesIO(archive)); files={}
    for n in z.namelist():
        if not n.endswith('/'):
            files[n.split('/',1)[1]]=z.read(n)
    hashes={n:hashlib.sha256(b).hexdigest() for n,b in files.items()}
    hits={k:[] for k in ['sorry','admit','axiom','unsafe','native_decide','implemented_by','extern']}
    lean={n:b for n,b in files.items() if n.endswith('.lean')}
    for n,b in lean.items():
        text=strip_comments_strings(b.decode())
        for k in hits:
            for m in re.finditer(r'\b'+k+r'\b',text):
                hits[k].append({'file':n,'line':text[:m.start()].count('\n')+1})
    selected=['README.md','lean-toolchain','lakefile.toml','lake-manifest.json','cert/Check.lean',
              'docs/CERTIFICATION.md','docs/STATUS.md','Zeta5/Axioms.lean','Zeta5/Basic.lean',
              'Zeta5/Interface.lean','Zeta5/Skeleton.lean','Zeta5/Functional.lean','Zeta5/Positivity.lean']
    for n in selected:
        if n in files:
            target=OUT/'sources'/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(files[n])
    pdf_url='https://zenodo.org/api/records/22826419/files/ZETA5_IS_IRRATIONAL.pdf/content'
    pdf=get(pdf_url);(OUT/'Fauzan-zeta5-v1.pdf').write_bytes(pdf)
    try:
        import pymupdf
        doc=pymupdf.open(stream=pdf,filetype='pdf')
        (OUT/'Fauzan-zeta5-v1.txt').write_text('\n\n'.join(f'PAGE {i+1}\n'+p.get_text() for i,p in enumerate(doc)),encoding='utf-8')
    except ImportError:
        import pypdf
        doc=pypdf.PdfReader(io.BytesIO(pdf))
        (OUT/'Fauzan-zeta5-v1.txt').write_text('\n\n'.join(f'PAGE {i+1}\n'+p.extract_text() for i,p in enumerate(doc.pages)),encoding='utf-8')
    result={'status':'source-audit-only','repo':'https://github.com/danromik/zeta5-irrationality',
            'commit':SHA,'archive_sha256':hashlib.sha256(archive).hexdigest(),
            'lean_files':len(lean),'lexical_hits':hits,'source_sha256':hashes,
            'pdf_url':pdf_url,'pdf_sha256':hashlib.sha256(pdf).hexdigest(),
            'build_rerun':False,'kernel_replay_rerun':False,
            'scope':'Lexical scan, not proof checking; comments and strings stripped. Public code not executed.',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    comparison=json.loads(get('https://api.github.com/repos/danromik/zeta5-irrationality/compare/a87234f...'+SHA))
    result['reported_kernel_checked_commit']='a87234f'
    result['comparison_to_reported_check']={'ahead_by':comparison['ahead_by'],
        'files':[{'path':f['filename'],'status':f['status']} for f in comparison['files']]}
    result['lean_toolchain']=files['lean-toolchain'].decode().strip()
    result['mathlib']=[p for p in json.loads(files['lake-manifest.json'])['packages'] if p['name']=='mathlib'][0]
    (OUT/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'commit':SHA,'lean_files':len(lean),'lexical_hits':hits,'pdf_bytes':len(pdf)},indent=2))
if __name__=='__main__':main()

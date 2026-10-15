"""Download a fixed public source archive; extract regular files safely inside this task."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import urllib.request

HERE=Path(__file__).resolve().parent
PIN='2b639655e07421b9ac743de9090459bab473a7c0'
URL='https://codeload.github.com/c0ldzy17/three-sum-lean/tar.gz/'+PIN
OUT=HERE/'verification/upstream'
if not (HERE/'verification/upstream-source.json').exists():
    opener=urllib.request.build_opener(urllib.request.ProxyHandler({'https':'http://127.0.0.1:65532'}))
    with opener.open(URL,timeout=60) as response:
        raw=response.read()
    OUT.mkdir(exist_ok=True)
    count=0
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as tar:
        for member in tar.getmembers():
            if not member.isfile():
                continue
            parts=Path(member.name).parts[1:]
            dest=OUT.joinpath(*parts).resolve()
            if not dest.is_relative_to(OUT.resolve()):
                raise ValueError('Archive path escapes task')
            dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes(tar.extractfile(member).read())
            count+=1
    record={'url':URL,'commit':PIN,'archive_sha256':hashlib.sha256(raw).hexdigest(),'regular_files':count}
    (HERE/'verification/upstream-source.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))
else:
    print('Fixed upstream source already present')

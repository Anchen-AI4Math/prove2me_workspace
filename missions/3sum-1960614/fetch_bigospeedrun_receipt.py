"""Retain the official immutable-run receipt and logs without executing contents."""
import hashlib
import io
import json
import os
from pathlib import Path,PurePosixPath
import stat
import subprocess
import zipfile

VER=Path(__file__).resolve().parent/'verification'
OUT=VER/'bigospeedrun-official-final'
OUT.mkdir(exist_ok=True)
ARTIFACT=11904143134
RUN=38567645711
env=os.environ.copy();env.update(HTTPS_PROXY='http://127.0.0.1:65532',HTTP_PROXY='http://127.0.0.1:65532')

def gh(path):
    result=subprocess.run(['gh','api',path],env=env,capture_output=True,check=True)
    return result.stdout

base='repos/bigospeedrun/verifier/actions/'
metadata=json.loads(gh(base+'artifacts/'+str(ARTIFACT)))
assert metadata['expired'] is False
assert metadata['workflow_run']['id']==RUN
assert metadata['workflow_run']['head_sha']=='51489ee2ac82596a41375e92ea8108814f931242'
data=gh(base+'artifacts/'+str(ARTIFACT)+'/zip')
archive_hash=hashlib.sha256(data).hexdigest()
if metadata.get('digest'):
    assert metadata['digest']=='sha256:'+archive_hash, 'Archive digest mismatch'
(OUT/'artifact.zip').write_bytes(data)
(OUT/'artifact-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n',encoding='utf-8')
files=[]
with zipfile.ZipFile(io.BytesIO(data)) as archive:
    assert sum(i.file_size for i in archive.infolist())<=300_000_000
    for info in archive.infolist():
        relative=PurePosixPath(info.filename)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert not stat.S_ISLNK(info.external_attr>>16)
        target=OUT.joinpath(*relative.parts).resolve()
        assert target.is_relative_to(OUT.resolve())
        if info.is_dir():continue
        payload=archive.read(info)
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(payload)
        files.append({'path':relative.as_posix(),'bytes':len(payload),
                      'sha256':hashlib.sha256(payload).hexdigest()})
summary={'artifact_id':ARTIFACT,'run_id':RUN,'archive_sha256':archive_hash,'files':files,
         'official_receipt_fields_not_yet_audited':True}
(OUT/'download-receipt.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print('Retained official artifact:',len(files),'files; archive SHA256',archive_hash)
for f in files:
    if f['path'].endswith('.json'):print('JSON evidence:',f['path'],f['bytes'],'bytes')

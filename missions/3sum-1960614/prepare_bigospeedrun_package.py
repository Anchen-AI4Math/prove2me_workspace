"""Stage the verified exact machine theorem in the official submission layout.

This does not create a Git repository, publish sources, or submit an issue.
It refuses to stage a package before the complete scoped proof and axiom gate.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
SRC=HERE/'machine/lean'
DST=HERE/'submission-bigospeedrun'
assert len(sys.argv)==2,'Supply the successful full scoped build log filename'
logpath=VER/sys.argv[1]
assert logpath.resolve().is_relative_to(VER.resolve())
log=logpath.read_text(encoding='utf-8')
assert 'Build completed successfully' in log,'The complete scoped build has not passed'
standard="'solution' depends on axioms: [propext, Classical.choice, Quot.sound]"
for name in ('complete_machine_goal','machine_cost_bridge'):
    assert any('Sol_ThreeSum1960614_'+name+'.lean:' in line and standard in line
               for line in log.splitlines()),'Missing exact full-goal axiom audit: '+name
frozen=VER/'bigospeedrun-EndStatement.lean'
assert frozen.read_bytes()==(SRC/'Submission/EndStatement.lean').read_bytes(), 'Frozen statement mismatch'
official=json.loads((VER/'bigospeedrun-anthropic-manifest.json').read_text(encoding='utf-8'))
local=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
def pin(manifest): return next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
assert pin(official)==pin(local)=='0df444a360eaa60ab8c11dca51a86af692955474'
assert (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip()=='leanprover/lean4:v4.33.1'

sources={}
outputs={}
for prefix in ('Submission','Closed3Sum'):
    for source in sorted((SRC/prefix).rglob('*.lean')):
        assert source.is_file() and not source.is_symlink()
        assert source.resolve().is_relative_to(SRC.resolve())
        relative=source.relative_to(SRC)
        if prefix=='Closed3Sum': relative=Path('Submission')/relative
        code=source.read_text(encoding='utf-8')
        # Only module import paths change. Declaration names and bodies retain their namespaces.
        code=re.sub(r'(?m)^(?:public\s+)?import\s+[^\r\n]+',
            lambda match:match.group(0).replace('Closed3Sum.','Submission.Closed3Sum.'),code)
        outputs[relative.as_posix()]=code.encode('utf-8')
        sources[source.relative_to(ROOT).as_posix()]=hashlib.sha256(source.read_bytes()).hexdigest()
outputs['Submission.lean']=b'''import Submission.EndStatement
import Submission.ThreeSum.FinalSolver

theorem Race.bound : EndStatement.ThreeSum.SolvedInTime ((980307 : Rat)/500000) :=
  ThreeSum.solvedInTime_980307_500000

#print axioms Race.bound
'''
outputs['manifest.json']=b'{"problem":"3sum","bound":"980307/500000"}\n'
for name in ('LICENSE','NOTICE'):
    outputs[name]=(HERE/'machine'/name).read_bytes()
outputs['README.md']=b'''# Deterministic word-RAM 3SUM at exponent 1.960614

The entry point is `Race.bound` in `Submission.lean`, with exact rational bound
980307/500000 and the unchanged official `EndStatement.ThreeSum` specification.
The official verifier supplies Lean 4.33.1 and its pinned Mathlib environment.

The machine proof extends c0ldzy17/three-sum-lean at commit
2b639655e07421b9ac743de9090459bab473a7c0 with expansion 232, the author-supplied
3sum_certificate_1p960614_v3 quartic and parameters, exact integer schedules,
and changed execution, cost and resource proofs. Codex assisted the extension.
Inherited Anthropic and other source credits, license headers and notices are
retained. See LICENSE and NOTICE. The independent fixed-model lower bound is
not used as an algorithmic premise.

Package preparation and a local Lean build do not establish site acceptance.
Comparator must independently compare the full theorem and definitions with
the official frozen statement, and the allowed-axiom audit must pass.
'''
assert not DST.exists() or not any(DST.iterdir()),'Review an existing package before replacing it'
for relative,content in outputs.items():
    dest=DST/relative
    assert dest.resolve().is_relative_to(DST.resolve())
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(content)
receipt={'build_log':logpath.relative_to(ROOT).as_posix(),'source_hashes':sources,
    'package_hashes':{k:hashlib.sha256(v).hexdigest() for k,v in outputs.items()},
    'frozen_statement_sha256':hashlib.sha256(frozen.read_bytes()).hexdigest(),
    'official_verifier_commit':'51489ee2ac82596a41375e92ea8108814f931242',
    'bound':'980307/500000','package_staged':True,'standalone_build_passed':False,
    'comparator_passed':False,'submitted':False}
(VER/'bigospeedrun-package-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print('Staged',len(outputs),'regular source/credit files. Independent verification remains required.')

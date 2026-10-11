"""Typed f4 evidence inventory after one complete readonly kernel review."""
from pathlib import Path
import formal_log_successor_security_pins as frozen

TASK,ROOT,V=frozen.TASK,frozen.ROOT,frozen.V
SELF=Path(__file__).resolve()
FROZEN_SUCCESSOR_SHA='198dc1620322fd0ec87db635f4dd761f0aedc8f77b3947ceb8b107679b32ff57'
FROZEN_BASE_SHA='8adf3e87f2dc8f7b219cfd55364e3cca391307ffacd46fc6e8d3b12773da7a4f'
sha,read,fail=frozen.sha,frozen.read,frozen.fail


class Inventory(frozen.Inventory):
    def certificate(self,d):
        super().certificate(d)
        for key in ['source_preflight','snapshot_preflight','generated_probe_preflight']:
            if isinstance(d.get(key),dict):self.wrapper(d[key])
        self.ref(d,'snapshot_preparation',role='child-preparation')
        self.ref(d,'provider_certificate',role='certificate')
        for key in ['source_output','generated_output']:self.ref(d,key)
        if isinstance(d.get('equation_certificate'),dict):self.ref(d['equation_certificate'],'path','sha256',role='certificate')
        for row in d.get('auxiliary_ci_certificates',[]):
            fail(row.get('evidence_role') not in ['formal-equation','extra-ci'],'Unknown bounded auxiliary evidence role')
            self.ref(row,'path','sha256',role='certificate')

    def certificate_at(self,path,d):
        super().certificate_at(path,d)
        if d.get('artifact_kind')=='formal-log-final-proof-node-kernel-certificate':
            stage=path.parent
            fail(stage!=(V/'flp3/f4').resolve(),'Only exact final-node stage supported')
            m=read(stage/'manifest.json')
            for name,h in m['outputs_sha256'].items():self.pin(stage/name,h)
            for name in ['c1.json','c2.json','c3.json','c4.json','certified-inputs.json']:
                self.pin(stage/name,sha(stage/name),'manifest')
            self.pin(stage/'preparation.json',sha(stage/'preparation.json'),'preparation')


def reviewed_security_pins(evidence):
    fail(sha(Path(frozen.__file__))!=FROZEN_SUCCESSOR_SHA or sha(Path(frozen.frozen.__file__))!=FROZEN_BASE_SHA,
         'Frozen typed Inventory implementations changed')
    fail(evidence.get('validated') is not True or Path(evidence['stage']).resolve()!=(V/'flp3/f4').resolve(),
         'Expected one fully reviewed f4 view')
    i=Inventory();c=evidence['certificate'];cp=i.path(c['path'])
    fail(read(cp)!=c['data'],'Trusted f4 certificate differs from current bytes')
    i.pin(cp,c['sha256'],'certificate');i.pin(SELF,sha(SELF));i.pin(Path(frozen.__file__),FROZEN_SUCCESSOR_SHA)
    i.pin(Path(frozen.frozen.__file__),FROZEN_BASE_SHA)
    i.pin(frozen.frozen.RUNTIME,evidence['manifest_data']['runtime_sha256'])
    i.pin(Path(i.runtime['executable']),i.runtime['executable_sha256'])
    for name,h in i.runtime['project_hashes'].items():i.pin(ROOT/name,h)
    return i.finish()


assert_security_pins=frozen.assert_security_pins

"""Check an ordinary decide proof as a possible compilation optimization."""
import time
import pipeline

if __name__=='__main__':
    source=pipeline.ROOT/'Solutions'/'Snaky21'/'Certificate11Part00.lean'
    candidate=pipeline.HERE/'verification'/'plain-decide-00.lean'
    candidate.write_text(source.read_text(encoding='utf-8').replace('decide +kernel','decide')+'\n#print axioms OAI.Snaky21.Certificate.valid_704\n',encoding='utf-8')
    started=time.monotonic()
    pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],'plain-decide-00')
    print('Elapsed seconds:',round(time.monotonic()-started,2))

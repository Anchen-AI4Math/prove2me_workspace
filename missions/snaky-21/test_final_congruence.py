"""Check the final submission variant with actual previously proved modules."""
import time
import pipeline

if __name__=='__main__':
    started=time.monotonic()
    pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(pipeline.HERE/'verification'/'final-congruence.lean')],'final-congruence')
    print('Elapsed seconds:',round(time.monotonic()-started,2))

"""Measure final equation composition independently of numerical computation."""
import re
import time
import pipeline

if __name__=='__main__':
    source=(pipeline.HERE/'verification'/'final-congruence.lean').read_text(encoding='utf-8')
    equation=re.search(r'^theorem eq_card_727 : .*?\n(?=theorem valid_727 :)',source,re.M|re.S).group(0)
    equation=equation.replace('theorem eq_card_727 :','theorem checked_final_congruence :',1)
    candidate=pipeline.HERE/'verification'/'final-equation-only.lean'
    candidate.write_text('import Solutions.Snaky21.Certificate11Part23\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace OAI.Snaky21.Certificate\nopen OAI.Snaky21 OAI.SnakyPrototype\n'+equation+'\nend OAI.Snaky21.Certificate\n#print axioms OAI.Snaky21.Certificate.checked_final_congruence\n',encoding='utf-8')
    started=time.monotonic()
    pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],'final-equation-only')
    print('Elapsed seconds:',round(time.monotonic()-started,2))

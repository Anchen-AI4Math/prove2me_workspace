"""Reuse the frozen source-span gate algorithm, with new independently executed evidence."""
from pathlib import Path
OUT=Path(__file__).resolve().parent;PARENT=OUT.parent
code=(PARENT/'freeze_author_actual.py').read_text(encoding='utf-8-sig')
code=code.replace('import author_driver as d','import review_driver as d')
code=code.replace("'.rt/ca1/b'","'.rt/ct1/b'")
code=code.replace("'author-execution-plan.json'","'own-execution-plan.json'")
code=code.replace('len(latest)==37','len(latest)==44')
code=code[:code.index("    limits=['Only the original")]
code+='''    from final_gate import finish
    finish(d,checks,receipt,plan,prov,kernel,rfl,comparisons,rawdiff,proofrecords,boundarycomparisons,artifacts,targets)

if __name__=='__main__':main()
'''
(OUT/'freeze_review.py').write_text(code,encoding='utf-8')
print('Pure independent gate assembled; no Lean called')

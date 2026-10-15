from pathlib import Path
root=Path(__file__).resolve().parent
header='import Definitions.Def_ThreeSum1960614_Machine_Bundle023\nimport Lean\n'
for label,count,priority in [('ambiguous',14,''),('priority',50,' (priority := high)')]:
    notation=(f'local infixr:30{priority} " ;; " => ThreeSum1960614.Machine.Light.Stmt.seq\n' if priority else '')
    body=' ;;\n'.join(['ThreeSum1960614.Machine.Light.Stmt.skip']*count)
    code=header+notation+'\nset_option profiler true in\ndef probe : ThreeSum1960614.Machine.Light.Stmt :=\n'+body+'\n'
    (root/f'probe_notation_{label}.lean').write_text(code,encoding='utf-8')
raw=(root.parents[2]/'Definitions/Def_ThreeSum1960614_Machine_Bundle024.lean').read_text(encoding='utf-8')
new='ThreeSum1960614.Machine.Light.'
operators=[('infixl',65,"+'",new+'Expr.op Light.Op.add'),('infixl',65,"-'",new+'Expr.op Light.Op.sub'),('infixl',70,"*'",new+'Expr.op Light.Op.mul'),('infix',50,"<'",new+'Cond.lt'),('infix',50,"='",new+'Cond.eq'),('infixr',30,';;',new+'Stmt.seq'),('infix',50,"≤'",new+'Cond.le')]
notation='\n'.join(f'local {kind}:{prec} (priority := high) " {op} " => {rhs}' for kind,prec,op,rhs in operators)+'\n'
offset=raw.index('\n\n')+2
(root/'probe_bundle024_priority.lean').write_text(raw[:offset]+notation+raw[offset:],encoding='utf-8')
for label,priority in [('bare_ambiguous',''),('bare_priority',' (priority := high)')]:
    code='import Lean\nnamespace A\ndef seq := Nat.add\nend A\nnamespace B\ndef seq := Nat.add\nend B\n'
    code+='infixr:30 " ;; " => A.seq\n'
    code+=f'infixr:30{priority} " ;; " => B.seq\n'
    code+='set_option profiler true in\ndef probe : Nat := '+(' ;; '.join(['1']*30))+'\n'
    (root/f'probe_notation_{label}.lean').write_text(code,encoding='utf-8')

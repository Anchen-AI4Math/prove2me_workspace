"""Additional requested whole-function rfl; serial, own SOURCE, actual receipts."""
import execute_native_author as e
import resume_author_v2

def main():
 resume_author_v2.install_gate()
 e.gate()
 before=e.load(e.OUT/'compile-receipt.json')
 latest={r['label']:r for r in before['rows']}
 assert len(latest)==29 and all(r['exit_code']==0 for r in latest.values())
 module='ParameterSummationWholeFunctionRflAudit'
 source=e.OUT/(module+'.lean');target=e.PROJECT/(module+'.lean')
 e.write(target,source.read_bytes())
 state=e.gate();mods=[r['module'] for r in state['sources']+state['controls']]+[module]
 code='import Lean\nopen Lean\nrun_meta do\n  initSearchPath (← findSysroot)\n'
 code+='  for name in ['+', '.join('`'+n for n in mods)+'] do\n'
 code+='    let path ← findOLean name\n    IO.println (Json.mkObj [("module",Json.str name.toString),("olean",Json.str path.toString)]).compress\n'
 e.write(e.PROJECT/'additional_resolver.lean',code)
 runner=e.recorder()
 runner.run('control-'+module,['-o','b/lib/lean/'+module+'.olean',module+'.lean'])
 runner.run('additional-own-object-resolution',['additional_resolver.lean'])
 resolved=[]
 for row in runner.rows(e.OUT/'additional-own-object-resolution.log'):
  raw=e.Path(row['olean']);actual=raw.resolve() if raw.is_absolute() else (e.PROJECT/raw).resolve()
  expected=(e.PROJECT/'b/lib/lean'/(row['module'].replace('.','/')+'.olean')).resolve()
  assert actual==expected
  resolved.append(dict(**row,resolved_absolute=str(actual),actual_execution_cwd=str(e.PROJECT),own_object_resolution_passed=True))
 assert len(resolved)==28
 receipt=e.load(e.OUT/'compile-receipt.json')
 e.dump(e.OUT/'additional-actual-own-object-resolution.json',resolved)
 e.dump(e.OUT/'additional-terminal-runtime-state.json',dict(actual_rows=len(receipt['rows']),
  actual_successes=sum(r['exit_code']==0 for r in receipt['rows']),actual_failures=sum(r['exit_code']!=0 for r in receipt['rows']),
  original_planned_final_calls=29,additional_rfl_and_resolver_calls=2,final_own_objects=28,whole_function_rfl_reached=True,
  author_freeze_still_required=True,independent_review_still_required=True))
 print('Additional whole-function rfl and all 28 own object resolutions terminal.',flush=True)

if __name__=='__main__':main()

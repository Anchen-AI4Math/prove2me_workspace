"""Pure private control-header completion after retained actual inferDefType failure."""
import execute_native_author as e

def main():
 receipt=e.load(e.OUT/'compile-receipt.json')
 failure=[r for r in receipt['rows'] if r['label']=='control-ParameterSummationBoundaryAudit' and r['exit_code']!=0]
 assert len(failure)==1 and failure[0]['failure_retained']
 initial=e.PREP/'controls/ParameterSummationBoundaryAudit.lean'
 raw=initial.read_bytes().decode('utf-8')
 prefix=raw.split('\nnamespace ParameterSummationAuthorBoundary\n',1)[0]
 tail=raw.split('end ParameterSummationAuthorBoundary',1)[1]
 blocks=[]
 r0='(0 : Fin 5)';r4='(4 : Fin 5)'
 blocks.append('theorem n1_exact_r0 :\n    exactL (1 + 2) (X ^ '+r0+'.val) = exactL 1 (connectionP 1 '+r0+') :=\n  actual_chosen_exactL_transport 1 (by decide) '+r0)
 for suffix,r in [('r0',r0),('r4',r4)]:
  W='(X ^ '+r+'.val)';P='(connectionP 2 '+r+')'
  typ=('HasSum (actualSeries (2 + 2) '+W+') (exactL 2 '+P+') ∧\n'
       '      HasSum (actualSeries 2 '+P+') (exactL 2 '+P+') ∧\n'
       '      Summable (fun t : ℕ => ‖actualSeries (2 + 2) '+W+' t‖) ∧\n'
       '      Summable (fun t : ℕ => ‖actualSeries 2 '+P+' t‖)')
  blocks.append('theorem n2_HasSum_'+suffix+' :\n    '+typ+' :=\n  actual_chosen_HasSum_transport 2 (by decide) (by decide) '+r)
 blocks.append('theorem n2_tsum_r4 :\n    (∑\' t : ℕ, actualSeries (2 + 2) (X ^ '+r4+'.val) t) =\n      ∑\' t : ℕ, actualSeries 2 (connectionP 2 '+r4+') t :=\n  actual_chosen_tsum_transport 2 (by decide) (by decide) '+r4)
 for suffix,r in [('r0',r0),('r4',r4)]:
  blocks.append('theorem n2_transfer_'+suffix+' :\n    transferMultiplier 2 (X ^ '+r+'.val) = connectionP 2 '+r+' :=\n  chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) '+r)
 for suffix,b,a in [('B',1,0),('A',0,1)]:
  W='(selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) '+str(b)+' '+str(a)+')'
  V='(selectedIntegerMultiplier 2 (by decide) (by decide) '+str(b)+' '+str(a)+')'
  L='((('+str(b)+') : ℝ) + (('+str(a)+') : ℝ) * zetaReal 9)'
  typ=('HasSum (actualSeries (2 + 2) '+W+') '+L+' ∧\n'
       '      HasSum (actualSeries 2 '+V+') '+L+' ∧\n'
       '      Summable (fun t : ℕ => ‖actualSeries (2 + 2) '+W+' t‖) ∧\n'
       '      Summable (fun t : ℕ => ‖actualSeries 2 '+V+' t‖)')
  blocks.append('theorem n2_selected_'+suffix+' :\n    '+typ+' :=\n  selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) '+str(b)+' '+str(a))
 W='(selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 1 1)'
 V='(selectedIntegerMultiplier 2 (by decide) (by decide) 1 1)'
 blocks.append('theorem n2_selected_tsum :\n    (∑\' t : ℕ, actualSeries (2 + 2) '+W+' t) =\n      ∑\' t : ℕ, actualSeries 2 '+V+' t :=\n  selectedIntegerMultiplier_parameter_tsum 2 (by decide) (by decide) 1 1')
 control=prefix+'\nnamespace ParameterSummationAuthorBoundary\n\n'+'\n\n'.join(blocks)+'\n\nend ParameterSummationAuthorBoundary'+tail
 target=e.PROJECT/'ParameterSummationBoundaryAudit.lean'
 assert target.read_bytes()==initial.read_bytes()
 e.write(e.OUT/'versions/v2/ParameterSummationBoundaryAudit.lean',control)
 e.write(target,control)
 private=e.PROJECT/(e.NATIVE.replace('.','/')+'.lean')
 assert e.sha(private)==e.SOURCE_SHA and e.headers(private.read_bytes())==e.headers(e.SOURCE.read_bytes())
 assert target.read_bytes().split(b'\nopen Lean Meta\n',1)[1]==initial.read_bytes().split(b'\nopen Lean Meta\n',1)[1]
 e.dump(e.OUT/'private-proof-repairs.json',dict(
  reason='Actual Lean inferDefTypeFailed on all 9 theorem header holes; theorem types must be explicit before proof elaboration',
  real_failed_row=dict(label=failure[0]['label'],attempt=failure[0]['attempt'],actual_exit=failure[0]['exit_code'],log=failure[0]['log']),
  original_source_headers_and_definition_preserved=True,frozen_origins_snapshots_and_preparation_unchanged=True,
  source_repair_performed=False,original_candidate_sha256=e.SOURCE_SHA,
  control_repair='Replace nine : _ closed headers with explicit complete instantiated types; same theorem endpoints/proofs/names and identical Meta audit code',
  nine_closed_boundary_names_preserved=[r['name'] for r in e.headers(initial.read_bytes())]==[r['name'] for r in e.headers(target.read_bytes())],
  allowed_current_source_bindings=[e.binding(target)],explicit_boundary_control_version=e.binding(e.OUT/'versions/v2/ParameterSummationBoundaryAudit.lean')))
 print('Retained actual boundary failure repaired only in private v2 control; candidate bf215 unchanged.')

if __name__=='__main__':main()

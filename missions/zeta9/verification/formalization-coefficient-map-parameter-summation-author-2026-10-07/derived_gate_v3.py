def gate():
 grant=load(GRANT)
 assert grant['owner']=='outputs_author_resume_1007' and grant['private_project']=='.rt/ost1'
 assert grant['source_sha256']==SOURCE_SHA and grant['required_serial_threads']==1
 assert grant['native_SOURCE_only_no_foreign_proof_objects'] and not grant['scope_helper_or_API_writes_permitted']
 assert sha(SOURCE)==SOURCE_SHA
 inputs=load(PREP/'source-inputs.json')
 ledger=load(OUT/'private-proof-repairs.json') if (OUT/'private-proof-repairs.json').exists() else {}
 allowed={r['task_relative']:r for r in ledger.get('allowed_current_source_bindings',[])}
 actual_failed=(OUT/'compile-receipt.json').exists() and any(r['exit_code']!=0 for r in load(OUT/'compile-receipt.json')['rows'])
 for row in load(PREP/'preparation-bindings.json')['files']:
  path=TASK/row['task_relative']
  if path.is_file() and path.stat().st_size==row['bytes'] and sha(path)==row['sha256']:continue
  assert actual_failed and row['task_relative'] in allowed,'Frozen binding changed without retained actual failure'
  assert binding(path)==allowed[row['task_relative']]
  assert ledger['original_source_headers_and_definition_preserved'] and ledger['frozen_origins_snapshots_and_preparation_unchanged']
 for row in inputs['sources']:
  origin=Path(row['origin_absolute']);snapshot=TASK/row['immutable_snapshot']['task_relative']
  assert origin.stat().st_size==row['bytes'] and sha(origin)==row['sha256']
  assert snapshot.stat().st_size==row['bytes'] and sha(snapshot)==row['sha256']
  own=PROJECT/row['project_relative']
  if sha(own)!=row['sha256']:
   assert row['module']==NATIVE and actual_failed
   assert headers(own.read_bytes())==headers(snapshot.read_bytes())
   assert definition(own.read_bytes())==definition(snapshot.read_bytes())
 for row in inputs['controls']:
  immutable=TASK/row['immutable_source']['task_relative']
  assert binding(immutable)==row['immutable_source']
  own=PROJECT/row['project_relative']
  if sha(own)!=row['immutable_source']['sha256']:
   assert actual_failed and binding(own)==allowed[own.relative_to(TASK).as_posix()]
   if row['module']=='ParameterSummationBoundaryAudit':
    assert [r['name'] for r in headers(own.read_bytes())]==[r['name'] for r in headers(immutable.read_bytes())]
    assert own.read_bytes().split(b'\nopen Lean Meta\n',1)[1]==immutable.read_bytes().split(b'\nopen Lean Meta\n',1)[1]
    assert own.read_bytes()==(OUT/'versions/v3/ParameterSummationBoundaryAudit.lean').read_bytes()
   else:
    assert headers(own.read_bytes())==headers(immutable.read_bytes())
 assert len(inputs['sources'])==22 and len(inputs['controls'])==5
 assert headers(SOURCE.read_bytes())==load(PREP/'static-original-header-inventory.json')['records']
 assert next(r for r in inputs['sources'] if r['module'].endswith('.CoefficientMapFormalTransportOutputs'))['sha256']=='8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6'
 assert next(r for r in inputs['sources'] if r['module'].endswith('.CoefficientMapFormalTransportJets'))['sha256']=='ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
 return inputs

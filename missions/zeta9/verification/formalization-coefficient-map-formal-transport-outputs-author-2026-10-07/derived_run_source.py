def run(label, arguments, output=None):
    state = gate()
    receipt_path = OUT/'compile-receipt.json'
    receipt = p.load(receipt_path) if receipt_path.exists() else dict(
        role='Outputs native author, fresh source-only compilation; independent review required',
        source_sha256=p.SOURCE_SHA, project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        fresh_build_task_relative=(PROJECT/'b').relative_to(TASK).as_posix(),
        cache_objects_borrowed=False, Root_proof_fallback_permitted=False,
        Root_API_credentials_scope_modified=False, rows=[])
    inputs = [p.binding(PROJECT/name) for name in ['lakefile.lean', 'lean-toolchain',
                                                       'lake-manifest.json', 'lean_call.py']]
    inputs.extend([p.binding(Path(__file__)),p.binding(LEAF),p.binding(PREP/'execute.py'),p.binding(PREP/'Root-lane-grant.json')])
    for argument in arguments:
        candidate = PROJECT/argument
        if str(argument).endswith('.lean') and candidate.is_file(): inputs.append(p.binding(candidate))
    previous = next((r for r in reversed(receipt['rows']) if r['label'] == label and r['exit_code'] == 0 and r['input_bindings'] == inputs and all((TASK/b['task_relative']).exists() and p.sha(TASK/b['task_relative']) == b['sha256'] for b in r['output_bindings'])), None)
    if previous is not None:
        assert previous['input_bindings'] == inputs
        for row in previous['output_bindings']+[previous[k] for k in ['stdout','stderr','log','exit_file','selected_paths']]:
            path = TASK/row['task_relative']
            assert path.stat().st_size == row['bytes'] and p.sha(path) == row['sha256']
        print(label+': exact prior actual success retained', flush=True)
        return
    attempt = 1+sum(r['label'] == label for r in receipt['rows'])
    folder = OUT/'actual-runs'/(label+'-'+str(attempt).zfill(2))
    folder.mkdir(parents=True, exist_ok=False)
    environment = dict(os.environ)
    environment.pop('LEAN_PATH', None); environment.pop('LEAN_SRC_PATH', None)
    environment['JETS_RUN_LABEL'] = label
    environment['JETS_RUN_PATHS_RECEIPT'] = str(folder/'selected-paths.json')
    command = [str(LAKE),'env',str(PY312),str(LEAF),str(LEAN),'-j1']+list(arguments)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
    for name,data in [('stdout.log',result.stdout),('stderr.log',result.stderr),
                      ('combined.log',result.stdout+result.stderr),('exit.txt',str(result.returncode)+'\n')]:
        p.write(folder/name,data)
    if output is not None: p.write(OUT/output, result.stdout)
    output_paths = []
    if '-o' in arguments:
        obj = PROJECT/arguments[arguments.index('-o')+1]
        if obj.exists(): output_paths.extend(sorted(obj.parent.glob(obj.name+'*')))
    if label == 'stage1-extract' and (OUT/'decl_graph.jsonl').exists(): output_paths.append(OUT/'decl_graph.jsonl')
    if label.startswith('stage2-'):
        snapshot = OUT/(label.removeprefix('stage2-')+'-oracle-input.lean')
        if snapshot.exists(): output_paths.append(snapshot)
    if output is not None: output_paths.append(OUT/output)
    path_receipt = folder/'selected-paths.json'
    row = dict(label=label, attempt=attempt, command=command, cwd=str(PROJECT),
        exit_code=result.returncode, elapsed_seconds=round(time.monotonic()-start,3),
        input_bindings=inputs, output_bindings=[p.binding(path) for path in output_paths],
        stdout=p.binding(folder/'stdout.log'), stderr=p.binding(folder/'stderr.log'),
        log=p.binding(folder/'combined.log'), exit_file=p.binding(folder/'exit.txt'),
        selected_paths=p.binding(path_receipt) if path_receipt.exists() else None,
        failure_retained=result.returncode != 0)
    retain_actual_inputs.retain(row,folder)
    row['actual_executor_sha256']=p.sha(Path(__file__))
    receipt['rows'].append(row); p.dump(receipt_path, receipt)
    p.write(OUT/(label+'.log'),result.stdout+result.stderr)
    p.write(OUT/(label+'-exit.txt'),str(result.returncode)+'\n')
    print(label+': actual exit '+str(result.returncode), flush=True)
    if result.returncode:
        print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)
    assert result.returncode == 0, 'Actual failed attempt retained; no PASS or continuation claimed.'
    assert path_receipt.exists()
    selected = p.load(path_receipt)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        assert all(Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
            Path(raw).resolve().is_relative_to((ROOT/'.lake/packages').resolve())
            for raw in selected[key]['filtered'])
    gate()

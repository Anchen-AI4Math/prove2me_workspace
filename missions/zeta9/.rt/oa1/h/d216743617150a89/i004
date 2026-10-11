"""Two additional serial AUTHOR calls after the 27 required calls finished."""
from pathlib import Path
import json
import execute_native_author as e

def main():
    state=e.gate();terminal=e.load(e.OUT/'terminal-runtime-state.json')
    assert terminal['final_success_calls']==27
    source=e.OUT/'OutputsDefinitionsAudit.lean'
    target=e.PROJECT/'OutputsDefinitionsAudit.lean'
    if target.exists():assert target.read_bytes()==source.read_bytes()
    else:target.write_bytes(source.read_bytes())
    recorder=e.load_recorder();recorder.__file__=str(Path(__file__))
    recorder.run('control-OutputsDefinitionsAudit',['-o','b/lib/lean/OutputsDefinitionsAudit.olean',target.name])
    resolver=e.PROJECT/'definition_resolver.lean'
    content='''import OutputsDefinitionsAudit
import Lean
open Lean
run_meta do
  let path ← findOLean `OutputsDefinitionsAudit
  IO.println (Json.mkObj [("module",Json.str "OutputsDefinitionsAudit"),("olean",Json.str path.toString)]).compress
'''
    if resolver.exists():assert resolver.read_text(encoding='utf-8')==content
    else:resolver.write_text(content,encoding='utf-8')
    recorder.run('definition-own-object-resolution',[resolver.name])
    records=recorder.rows(e.OUT/'definition-own-object-resolution.log');assert len(records)==1
    raw=Path(records[0]['olean']);actual=raw.resolve() if raw.is_absolute() else (e.PROJECT/raw).resolve()
    expected=(e.PROJECT/'b/lib/lean/OutputsDefinitionsAudit.olean').resolve();assert actual==expected
    e.save(e.OUT/'additional-definition-audit-state.json',dict(actual_additional_successful_calls=2,
        complete_definition_kernel_comparisons=18,source_control=e.p.binding(target),
        actual_own_object_resolution=dict(**records[0],actual_execution_cwd=str(e.PROJECT),
            resolved_absolute=str(actual),expected_own_absolute=str(expected)),
        author_source_reuse_not_independent_audit=True,Root_or_foreign_objects_borrowed=False))
    print('Additional full-definition author control and own object resolver terminal.',flush=True)

if __name__=='__main__':main()

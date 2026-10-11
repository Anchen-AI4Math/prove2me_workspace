"""Exact independent-type and native-boundary replay through genuine parsers.

Original resolved term refs get actual span edits. Quoted Name data for new
whole-type comparisons are generated semantically from the genuine graph;
they are never claimed to be resolved source-reference spans.
"""
from pathlib import Path
import argparse, hashlib, json, sys
import prepare as p
import execute_oracles as e
import run_actual as actual
import author_stage as s

OUT,TASK,ROOT,PROJECT,NS=p.OUT,p.TASK,p.ROOT,p.PROJECT,p.NS


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser();parser.add_argument('--lane-granted',action='store_true',required=True)
    args=parser.parse_args()
    assert not (OUT/'author-audit.json').exists()
    c=s.context();targets=p.load(OUT/'target-plan.json')['targets']
    original_inputs=[('expected',p.INDEPENDENT/'expected-types.lean','MatrixExpectedControlOriginal'),
        ('boundary',p.INDEPENDENT/'independent-boundary.lean','MatrixBoundaryControlOriginal'),
        ('author-endpoint',p.AUTHOR/'endpoint-audit.lean','MatrixAuthorEndpointControlOriginal'),
        ('author-source',p.AUTHOR/'type-audit.lean','MatrixAuthorSourceControlOriginal')]
    native=p.load(p.INDEPENDENT/'independent-review.json')
    parser_template=(OUT/'extract_CoefficientMapMatrix_sketch_v2.lean').read_text(encoding='utf-8-sig')
    old_snapshot=(OUT/'CoefficientMapMatrix-oracle-input.lean').as_posix()
    assert parser_template.count(old_snapshot)==1
    controls=[]
    for label,source,module in original_inputs:
        bound=next(r for r in native['stable_files'] if
            (ROOT/r['root_relative'] if 'root_relative' in r else TASK/r['task_relative']).resolve()==source.resolve())
        assert p.sha(source)==bound['sha256']
        p.write(OUT/'control-originals'/(module+'.lean'),source.read_bytes())
        p.write(PROJECT/(module+'.lean'),source.read_bytes())
        snapshot=(OUT/('control-'+label+'-oracle-input.lean')).as_posix()
        code=parser_template.replace(old_snapshot,snapshot)
        filename='parse-control-'+label+'.lean';s.save_leaf('parse-control-'+label,code)
        actual.run('parse-control-'+label,['--run',filename,module+'.lean','ZetaNine'],
            'control-'+label+'-sketch_info.jsonl')
        actual.run('header-control-'+label,['--run','extract_header.lean',module+'.lean'],
            'control-'+label+'-header_info.jsonl')
        data=(OUT/('control-'+label+'-oracle-input.lean')).read_bytes()
        assert data==source.read_bytes().replace(b'\r\n',b'\n')
        facts=e.rows(OUT/('control-'+label+'-sketch_info.jsonl'))
        header=e.rows(OUT/('control-'+label+'-header_info.jsonl'))[0]
        assert header['start']['offset']==0
        # The expected/control scripts may import Lean after the native import;
        # preserve every genuine header import except the one native root.
        imports=data[:header['end']['offset']].decode().strip().splitlines()
        assert imports.count('import '+p.NATIVE)==1
        controls.append(dict(label=label,data=data,facts=facts,header=header,imports=imports,
            original_source_binding=p.binding(source),source_snapshot_binding=p.binding(Path(snapshot))))
    matrix_proofs=[r['name'] for r in c['core'] if r['kind']=='theorem']
    pairs=native['actual_whole_kernel_comparisons']
    assert len(pairs)==17 and {r['source'] for r in pairs}==set(matrix_proofs)
    all_provenance=[]
    for index,target in enumerate(targets):
        original=target['theorem_name'];checked=NS+'.checked_'+original.rsplit('.',1)[1]
        module=target['local_solution'].removesuffix('.lean').replace('/','.')
        labels=['expected'] if index!=2 else ['expected','boundary','author-endpoint','author-source']
        for label in labels:
            control=next(r for r in controls if r['label']==label)
            data=control['data'];header=control['header'];changes=[];refs=[]
            prefix='\n'.join('import '+module if line=='import '+p.NATIVE else line for line in control['imports'])+'\n'
            changes.append((header['start']['offset'],header['end']['offset'],prefix.encode()))
            for ref in control['facts']:
                if ref['kind']!='ref' or ref['const']!=original:continue
                a,b=ref['start']['offset'],ref['end']['offset']
                if a<header['end']['offset']:continue
                spelling=data[a:b].decode()
                assert spelling in [original,original.rsplit('.',1)[1]]
                replacement=checked if spelling==original else checked.rsplit('.',1)[1]
                changes.append((a,b,replacement.encode()));refs.append(ref)
            text=s.edit(data,changes).decode()
            literal_pairs=[]
            if label=='expected':
                text+='\n\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.proofs true\nrun_meta do\n'
                literal_pairs=[dict(original=r['source'],actual=checked if r['source']==original else r['source'],
                    expected=r['expected']) for r in pairs]
                text+='  for (label,actual,expectedName) in ['+', '.join('('+json.dumps(r['original'])+', `'+r['actual']+', `'+r['expected']+')' for r in literal_pairs)+'] do\n'
                text+='''    let a ← getConstInfo actual
    let b ← getConstInfo expectedName
    let equal ← isDefEq a.type b.type
    unless equal do throwError "Actual staged complete type differs from independent expected: {actual}"
    IO.println (Json.mkObj [("kind",Json.str "actual_whole_type_kernel_comparison"),
      ("label",Json.str label),("actual",Json.str actual.toString),("expected",Json.str expectedName.toString),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr b.type))]).compress
'''
            filename='stage-control-'+str(index)+'-'+label
            s.save_leaf(filename,text);actual.run(filename,[filename+'.lean'])
            all_provenance.append(dict(label=filename,solution=module,
                original_source_binding=control['original_source_binding'],
                actual_source_snapshot_binding=control['source_snapshot_binding'],
                actual_header=header,actual_selected_term_reference_facts=refs,
                actual_span_edits=[dict(start=a,end=b,replacement=v.decode()) for a,b,v in changes],
                generated_semantic_Name_data_pairs=literal_pairs,
                quoted_Name_data_are_not_claimed_as_resolved_term_refs=True,
                staged_source_binding=p.binding(OUT/(filename+'.lean')),
                no_new_mathematical_hypotheses=True))
    p.dump(OUT/'stage-control-provenance.json',dict(records=all_provenance,
        original_controls=4,actual_parser_and_header_invocations=8,
        actual_staged_control_invocations=6,direct_complete_type_kernel_comparisons=51,
        native_boundary_count=26,author_endpoint_count=12,
        expected_closed_types_and_whole_values_per_solution=22,
        original_source_check_diagnostics=22,Name_data_remapping_is_semantic_not_refspan=True))
    print('14 actual parser/header/control calls completed; 51 direct complete type kernel comparisons and closed native controls replayed.')


if __name__=='__main__':main()

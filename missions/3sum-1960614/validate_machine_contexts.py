"""Cross-check supplementary context envelopes against completed official facts."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
inputs=json.loads((VER/'machine-context-inputs.json').read_text(encoding='utf-8'))
contexts={c['module']:c for c in json.loads((VER/'machine-scope-contexts.json').read_text(encoding='utf-8'))}
assert len(contexts)==len(inputs) and all(c['parsePassed'] for c in contexts.values())
checked_modules=0
checked_declarations=0
for record in inputs:
    source=Path(record['path'])
    assert hashlib.sha256(source.read_bytes()).hexdigest()==record['source_sha256']
    assert hashlib.sha256(source.read_text(encoding='utf-8').encode()).hexdigest()==record['oracle_input_sha256']
    data=source.read_text(encoding='utf-8').encode()
    context=contexts[record['module']]
    for item in context['headerKeywordRanges']:
        assert data[item['startOffset']:item['endOffset']] in (b'module',b'prelude')
        assert item['endOffset']<=context['headerEndOffset']
    for command in context['commands']:
        if command['syntaxKind']=='Lean.Parser.Command.open':
            assert command['opens'] and all(o['variant']!='unsupported' for o in command['opens'])
        for wrapper in command['scopeWrappers']:
            assert command['startOffset']<=wrapper['startOffset']<wrapper['endOffset']<wrapper['afterInOffset']<=command['endOffset']
            assert data[wrapper['endOffset']:wrapper['afterInOffset']].strip()==b'in'
            if wrapper['syntaxKind']=='Lean.Parser.Command.open':
                assert wrapper['opens'] and all(o['variant']!='unsupported' for o in wrapper['opens'])
    stem=record['module'].replace('.','_')
    receipt_path=VER/'sketch-oracles'/(stem+'.receipt.json')
    if not receipt_path.exists():continue
    receipt=json.loads(receipt_path.read_text(encoding='utf-8'))
    if receipt.get('exit_code')!=0:continue
    assert receipt['source_sha256']==record['source_sha256']
    facts=[json.loads(line) for line in (VER/'sketch-oracles'/(stem+'.jsonl')).read_text(encoding='utf-8').splitlines() if line.strip()]
    commands=contexts[record['module']]['commands']
    for fact in facts:
        if fact['kind']!='decl':continue
        a,b=fact['declStart']['offset'],fact['declEnd']['offset']
        matches=[c for c in commands if c['startOffset']==a and c['endOffset']==b]
        assert len(matches)==1,(record['module'],a,b)
        checked_declarations+=1
    checked_modules+=1
result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),
        'all_context_modules_parsed':True,'context_module_count':len(contexts),
        'official_modules_cross_checked':checked_modules,
        'official_declarations_cross_checked':checked_declarations,
        'full_official_extraction_complete':checked_modules==len(contexts),
        'context_sha256':hashlib.sha256((VER/'machine-scope-contexts.json').read_bytes()).hexdigest()}
(VER/'machine-context-validation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Context parse passed for',len(contexts),'modules;',checked_declarations,
      'official declaration envelopes matched across',checked_modules,'completed modules.')

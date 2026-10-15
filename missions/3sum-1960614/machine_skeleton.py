"""Range-based source renderer shared by the main transplantation pipeline.

Declaration/proof/reference edits use only the official two-stage oracles.
Supplementary Lean syntax supplies import headers and non-declaration scopes.
This module performs no publication and contains no source-pattern scanner.
"""
from collections import defaultdict
from bisect import bisect_left
import hashlib
import json
from pathlib import Path
import unicodedata

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
COMMAND='Lean.Parser.Command.'
DIAGNOSTICS={COMMAND+k for k in ('printAxioms','print','check','eval','reduce','synth')}
GREEK=dict(zip('αβγδεζηθικλμνξοπρστυφχψω',
               'alpha beta gamma delta eps zeta eta theta iota kappa lambda mu nu xi omicron pi rho sigma tau upsilon phi chi psi omega'.split()))

def sha(data):return hashlib.sha256(data).hexdigest()

def ascii_component(name):
    out=[]
    for char in name:
        if char.isascii() and (char.isalnum() or char=='_'):out.append(char)
        elif char=="'":out.append('_prime')
        elif char.lower() in GREEK:
            value=GREEK[char.lower()]
            out.append(value.capitalize() if char.isupper() else value)
        elif char.isdigit():out.append(str(unicodedata.digit(char)))
        else:out.append('_u'+format(ord(char),'x'))
    return ''.join(out)

def edits(data,changes):
    ordered=sorted(changes,key=lambda e:(e[0],e[1]))
    previous=-1
    for a,b,_ in ordered:
        assert 0<=a<=b<=len(data),(a,b,len(data))
        assert a>=previous,('overlapping oracle edits',ordered)
        previous=b
    for a,b,value in reversed(ordered):data=data[:a]+value+data[b:]
    return data

class Renderer:
    def __init__(self,classification,prefix='ThreeSum1960614.Machine'):
        self.plan=classification
        self.units=classification['units']
        self.prefix=prefix
        self.sources={};self.facts={}
        self.contexts={c['module']:c for c in json.loads((VER/'machine-scope-contexts.json').read_text(encoding='utf-8'))}
        self.unit_by_name={name:uid for uid,u in self.units.items() for name in u['names']}
        self.unit_by_span={(u['module'],u['fact']['declStart']['offset'],u['fact']['declEnd']['offset']):uid
                           for uid,u in self.units.items()}
        graph=[json.loads(s) for s in (VER/'machine-decl-graph.jsonl').read_text(encoding='utf-8').splitlines()]
        self.rows={r['name']:r for r in graph}
        self.reuse=json.loads((VER/'machine-definition-reuse.json').read_text(encoding='utf-8'))
        assert self.reuse['approved']
        self.external_namespaces=set(json.loads((VER/'machine-external-namespaces.json').read_text(encoding='utf-8')))
        self.source_scope_cache={}
        self.selector_refs={}
        self.accepted=json.loads((VER/'machine-upload-plan.json').read_text(encoding='utf-8')).get('accepted_library_nodes',{})
        self.name_map={};self.private_aliases={};self.binding_names={}
        for module,receipt in classification['module_receipts'].items():
            path=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
            assert sha(path.read_bytes())==receipt['source_sha256'],module
            data=path.read_text(encoding='utf-8').encode()
            assert sha(data)==receipt['oracle_input_sha256'],module
            self.sources[module]=data
            fp=ROOT/receipt['facts_path']
            assert sha(fp.read_bytes())==receipt['facts_sha256'],module
            self.facts[module]=[json.loads(s) for s in fp.read_text(encoding='utf-8').splitlines() if s.strip()]
            lexical_pairs=[];dot_selectors=set()
            for command in self.contexts[module]['commands']:
                assert 'lexicalIdentifiers' in command, ('Missing parsed reference shape',module)
                for ident in command['lexicalIdentifiers']:
                    lexical_pairs.append((ident['startOffset'],ident['endOffset']))
                dot_selectors.update((s['startOffset'],s['endOffset']) for s in command['dotSelectors'])
                dot_selectors.update((s['startOffset'],s['endOffset']) for s in command.get('caseLabels',[]))
            lexical_pairs.sort();lexical_starts=[a for a,b in lexical_pairs]
            lexical_max_ends=[];last=-1
            for a,b in lexical_pairs:
                last=max(last,b);lexical_max_ends.append(last)
            dot_pairs=sorted(dot_selectors);dot_starts=[a for a,b in dot_pairs]
            dot_max_ends=[];last=-1
            for a,b in dot_pairs:
                last=max(last,b);dot_max_ends.append(last)
            def selector(ref):
                a,b=ref['start']['offset'],ref['end']['offset']
                j=bisect_left(lexical_starts,a)-1
                k=bisect_left(dot_starts,a+1)-1
                return (k>=0 and dot_max_ends[k]>=b) or (j>=0 and lexical_max_ends[j]>=b)
            self.selector_refs[module]={(ref['start']['offset'],ref['end']['offset'])
                for ref in self.facts[module] if ref['kind']=='ref'
                and selector(ref)}
        self.mixfix_priorities={}
        for item in json.loads((VER/'machine-mixfix-priorities.json').read_text(encoding='utf-8')):
            module=item['module']
            if module not in self.sources:continue
            assert sha(self.sources[module])==item['source_sha256'],module
            a=item['offset'];command=item['command'].encode()
            assert self.sources[module][a:a+len(command)]==command
            slot=item['insertOffset']
            assert command[slot:].startswith(item['notationItem'].encode())
            self.mixfix_priorities[(module,a)]=a+slot
        for name,row in self.rows.items():
            uid=self.unit_by_name.get(name)
            u=self.units.get(uid)
            if name in self.reuse['definitions']:
                new=name
            elif u and u['classification']=='reuse-definition':
                new=name
            elif u and u['classification']=='reuse-node':
                primary=u['primary']
                new=self.accepted.get(primary,{}).get('platform_name',primary)
                if name!=primary:new=new+name[len(primary):]
            elif name=='ThreeSum1960614.costs_solve_3sum':new=name
            else:
                user=row['userName']
                pieces=user.split('.')
                if row['isPrivate']:
                    # Different source modules' proof-local helpers coexist in
                    # a generated solution, so their user names must be unique.
                    pieces[-1]='private_'+sha((row['module']+name).encode())[:10]+'_'+pieces[-1]
                if u and u['classification']=='node':pieces=[ascii_component(p) for p in pieces]
                new=prefix+'.'+'.'.join(pieces)
            self.name_map[name]=new
            if row['isPrivate']:
                native_prefix='_private.'+row['module']+'.'
                if name.startswith(native_prefix):
                    self.private_aliases[(row['module'],'_private.'+name[len(native_prefix):])]=name
        # Projectors/constructors of a relocated private structure follow the
        # parent's relocated name; they are not independently renamed helpers.
        for unit in self.units.values():
            primary=unit['primary'];user=self.rows[primary]['userName']
            for name in unit['names']:
                member=self.rows[name]['userName']
                if name!=primary and member.startswith(user+'.'):
                    self.name_map[name]=self.name_map[primary]+member[len(user):]
        # Source-free companions are regenerated by the relocated source
        # command. Map them through their nearest actual source parent.
        for name,row in self.rows.items():
            if row['startLine']!=0:continue
            parents=[n for n in self.unit_by_name if name.startswith(n+'.')]
            if parents:
                parent=max(parents,key=len)
                self.name_map[name]=self.name_map[parent]+name[len(parent):]
        self.namespace_names=set()
        live_names=set(self.unit_by_name)|set(self.reuse['definitions'])
        live_names.update(r['name'] for r in classification.get('preserved_structural_declarations',[]))
        for name in [self.name_map[n] for n in live_names if n in self.name_map]:
            pieces=name.split('.')
            self.namespace_names.update('.'.join(pieces[:i]) for i in range(1,len(pieces)))

    def mapped(self,module,name):
        return self.name_map.get(self.private_aliases.get((module,name),name),name)

    def definition_providers(self,module):
        record=self.reuse['modules'].get(module)
        if record is None:return set()
        return {p['definition_module'] for p in record.get('providers',[record])}

    def relative_binding(self,unit):
        row=self.rows[unit['primary']]
        old=row['userName'];new=self.name_map[unit['primary']]
        # The wrapper already relocates the original enclosing namespace.
        parent=self.scope_stack(unit['module'],unit['fact']['declStart']['offset'])[-1]['namespace']
        root=self.prefix+('.'+parent if parent else '')
        if not new.startswith(root+'.'):return '_root_.'+new
        return new[len(root)+1:]

    def reference_edits(self,module,start,end,*,binding=None,strip_doc=False,strip_private=False):
        changes={}
        binding_ranges=[]
        if binding:
            unit,new_name=binding
            fact=unit['fact'];primary=unit['primary']
            for ref in self.facts[module]:
                if ref['kind']!='ref':continue
                name=self.private_aliases.get((module,ref['const']),ref['const'])
                cutoff=(fact['valStart'] or fact['declEnd'])['offset']
                if name==primary and fact['declStart']['offset']<=ref['start']['offset']<cutoff:
                    binding_ranges.append((ref['start']['offset'],ref['end']['offset']))
            if fact['nameText'] is None and not binding_ranges:
                pass  # Some anonymous instances have no source binder Info.
            else:
                if len(binding_ranges)>1:
                    assert fact['valStart'] is None and self.rows[primary]['kind']=='inductive',(primary,binding_ranges)
                assert binding_ranges,('no official binding range',primary)
                a,b=min(binding_ranges)
                if fact['nameText'] is None:
                    assert self.sources[module][a:b]==b'instance',(primary,a,b)
                    changes[a,b]=('instance '+new_name).encode()
                else:changes[a,b]=new_name.encode()
        for ref in self.facts[module]:
            if ref['kind']!='ref':continue
            a,b=ref['start']['offset'],ref['end']['offset']
            if not (start<=a and b<=end) or (a,b) in changes:continue
            old=self.private_aliases.get((module,ref['const']),ref['const'])
            if binding:
                unit,bound_name=binding
                value_start=unit['fact']['valStart']
                if old==unit['primary'] and value_start is not None and a>=value_start['offset']:
                    # Recursive calls refer to the declaration being generated,
                    # whose local recursion variable has its binding's name.
                    changes[a,b]=bound_name.encode()
                    continue
            if binding:
                unit,_=binding
                if (unit['fact']['valStart'] is None and self.rows[unit['primary']]['kind']=='inductive'
                        and old in unit['names'] and old!=unit['primary']):
                    # Field/constructor binding Info points to its source
                    # label. The enclosing declaration regenerates the label.
                    continue
            new=self.name_map.get(old)
            if new is not None:
                # A projection/method selector is a suffix of a parsed name or
                # a parser `proj`/`dotIdent` field. Prefixing `_root_` there
                # creates the invalid `object._root_.Namespace.field`.
                # The receiver/expected type supplies the relocated namespace.
                if (a,b) in self.selector_refs[module]:
                    leaf=new.rsplit('.',1)[-1]
                    if leaf==old.rsplit('.',1)[-1]:continue
                    value=leaf.encode()
                else:value=('_root_.'+new).encode()
                assert (a,b) not in changes or changes[a,b]==value,('conflicting ref',ref)
                changes[a,b]=value
        if binding:
            unit,_=binding
            for key,remove in [('docstring',strip_doc),('privateTok',strip_private)]:
                item=unit['fact'][key]
                if remove and item:
                    a,b=item['start']['offset'],item['end']['offset']
                    changes[a,b]=b''
        return [(a-start,b-start,value) for (a,b),value in changes.items()]

    def declaration(self,unit,*,target=None,stub=False):
        fact=unit['fact'];module=unit['module']
        a=fact['declStart']['offset']
        b=fact['valStart']['offset'] if stub else fact['declEnd']['offset']
        target=target or self.relative_binding(unit)
        binding=(unit,target)
        changes=self.reference_edits(module,a,b,binding=binding,strip_doc=stub,
                                     strip_private=stub or unit['deprivatize'])
        if binding is None:
            for key,remove in [('docstring',stub),('privateTok',stub or unit['deprivatize'])]:
                item=fact[key]
                if remove and item:
                    changes.append((item['start']['offset']-a,item['end']['offset']-a,b''))
        namespace=self.scope_stack(module,a)[-1]['namespace']
        for wrapper in self.scope_wrappers(unit):
            first=wrapper['startOffset']-a
            last=(wrapper['afterInOffset'] if stub else wrapper['endOffset'])-a
            changes=[e for e in changes if not (first<=e[0] and e[1]<=last)]
            replacement=b'' if stub else self.context_command(module,wrapper,namespace).encode()
            changes.append((first,last,replacement))
        code=edits(self.sources[module][a:b],changes).decode()
        if stub:return code+':= by sorry'
        old_leaf=self.rows[unit['primary']]['userName'].rsplit('.',1)[-1]
        new_leaf=target.rsplit('.',1)[-1]
        if old_leaf!=new_leaf and fact['nameText'] is not None:
            # Local recursive calls are fvars and intentionally absent from
            # the official constant-reference oracle. A declaration-local
            # notation preserves their source spelling after binder renaming.
            # mkIdent deliberately retains the unscoped recursive binder name.
            # Syntax quotation would precheck the forward declaration and add
            # hygiene scopes before its recursion variable exists.
            spellings=[old_leaf]
            if fact['nameText'] not in spellings:spellings.append(fact['nameText'])
            alias=''.join('local macro '+json.dumps(spelling,ensure_ascii=False)+
                          ' : term => pure (Lean.mkIdent `'+target+')\n' for spelling in spellings)
            code='section\n'+alias+code+'\nend\n'
        return code

    def scope_wrappers(self,unit):
        fact=unit['fact']
        matches=[c for c in self.contexts[unit['module']]['commands']
                 if c['startOffset']==fact['declStart']['offset'] and c['endOffset']==fact['declEnd']['offset']]
        assert len(matches)==1,unit['id']
        return matches[0]['scopeWrappers']

    def hoisted_context(self,unit):
        namespace=self.scope_stack(unit['module'],unit['fact']['declStart']['offset'])[-1]['namespace']
        return ''.join(self.context_command(unit['module'],c,namespace)+'\n' for c in self.scope_wrappers(unit))

    def imports(self,module):
        return [i['name'] for imp in self.contexts[module]['imports'] for i in imp['identifiers']]

    def header_comments(self,module):
        context=self.contexts[module]
        data=self.sources[module][:context['headerEndOffset']]
        changes=[(r['startOffset'],r['endOffset'],b'') for r in context['headerKeywordRanges']]
        changes.extend((i['range']['startOffset'],i['range']['endOffset'],b'') for i in context['imports'])
        return edits(data,changes).decode().strip()

    def module_order(self,modules):
        pending=set(modules);order=[]
        dependencies={}
        for module in pending:
            seen=set();todo=list(self.imports(module))
            while todo:
                child=todo.pop()
                if child in seen or child not in self.sources:continue
                seen.add(child);todo.extend(self.imports(child))
            dependencies[module]=seen
        while pending:
            ready=sorted(m for m in pending if not (dependencies[m] & pending))
            assert ready,('import cycle',pending)
            order+=ready;pending.difference_update(ready)
        return order

    def external_imports(self,modules):
        result=set();seen=set();pending=list(modules)
        while pending:
            module=pending.pop()
            if module in seen:continue
            seen.add(module)
            for name in self.imports(module):
                if name in self.sources:pending.append(name)
                else:result.add(name)
        return sorted(result)

    def scope_stack(self,module,before=None):
        frames=[{'namespace':'','name':'','commands':[]}]
        for command in self.contexts[module]['commands']:
            if before is not None and command['startOffset']>=before:break
            if command['hasDeclaration']:continue
            kind=command['syntaxKind'];ids=[i['name'] for i in command['identifiers']]
            if kind==COMMAND+'namespace':
                assert len(ids)==1,command
                # Lean addScopes creates one scope for EACH parsed Name
                # component; `namespace Light.Compiler; end Compiler` leaves
                # Light open. Mirror BuiltinCommand.addScopes/elabEnd.
                assert '\u00ab' not in ids[0] and '_root_' not in ids[0],command
                for part in ids[0].split('.'):
                    parent=frames[-1]['namespace']
                    namespace=(parent+'.' if parent else '')+part
                    frames.append({'namespace':namespace,'name':part,'commands':[]})
            elif kind==COMMAND+'section':
                assert len(ids)<=1,command
                for part in (ids[0].split('.') if ids else ['']):
                    frames.append({'namespace':frames[-1]['namespace'],'name':part,'commands':[]})
            elif kind==COMMAND+'end':
                assert len(ids)<=1,command
                parts=ids[0].split('.') if ids else ['']
                assert len(frames)>len(parts),command
                assert [f['name'] for f in frames[-len(parts):]]==parts,(command,frames[-len(parts):])
                del frames[-len(parts):]
            elif kind not in DIAGNOSTICS|{COMMAND+'moduleDoc',COMMAND+'macro',COMMAND+'mixfix',COMMAND+'attribute'}:
                frames[-1]['commands'].append(command)
        return frames

    def open_namespace(self,name):
        choices=[]
        for value in (name,self.prefix+'.'+name):
            if value in self.namespace_names:choices.append('_root_.'+value)
        return '\n'.join('open '+x for x in choices)+'\n'

    def namespace_choices(self,module,namespace,name):
        if module not in self.source_scope_cache:
            seen=set();todo=[module];declared=set()
            while todo:
                current=todo.pop()
                if current in seen or current not in self.sources:continue
                seen.add(current);todo.extend(self.imports(current))
                for command in self.contexts[current]['commands']:
                    if command['syntaxKind']==COMMAND+'namespace':
                        declared.add(self.scope_stack(current,command['endOffset'])[-1]['namespace'])
            self.source_scope_cache[module]=declared
        declared=self.source_scope_cache[module]
        if name.startswith('_root_.'):
            candidates=[name.removeprefix('_root_.')]
        else:
            parts=namespace.split('.') if namespace else []
            candidates=['.'.join(parts[:i]+[name]) for i in range(len(parts),-1,-1)]
        for candidate in candidates:
            choices=[]
            if candidate in self.external_namespaces or candidate in self.namespace_names:choices.append(candidate)
            mapped=self.prefix+'.'+candidate
            if mapped in self.namespace_names or candidate in declared:choices.append(mapped)
            if choices:return list(dict.fromkeys(choices))
        return [name.removeprefix('_root_.')]

    def active_context(self,module,before):
        result=[]
        for frame in self.scope_stack(module,before):
            if frame['namespace']:result.append(self.open_namespace(frame['namespace']))
            for command in frame['commands']:
                result.append(self.context_command(module,command,frame['namespace']))
        return '\n'.join(result)

    def context_command(self,module,command,namespace=''):
        a,b=command['startOffset'],command['endOffset']
        data=self.sources[module][a:b]
        changes=self.reference_edits(module,a,b)
        if command['syntaxKind']==COMMAND+'open':
            output=[]
            for opened in command['opens']:
                kind=opened['variant']
                if kind in ['simple','scoped']:
                    for ident in opened['namespaces']:
                        choices=([ident['name'].removeprefix('_root_.')] if kind=='scoped' else
                                 self.namespace_choices(module,namespace,ident['name']))
                        output.extend('open '+('scoped ' if kind=='scoped' else '')+'_root_.'+n for n in choices)
                elif kind=='explicit':
                    # An open-list member is an identifier relative to its
                    # namespace, not a term. Preserve its local alias while
                    # relocating its resolved declaration through Stage 2.
                    for member in opened['members']:
                        loc=member['range'];first,last=loc['startOffset'],loc['endOffset']
                        refs=[f for f in self.facts[module] if f['kind']=='ref'
                              and f['start']['offset']==first and f['end']['offset']==last]
                        constants={self.mapped(module,f['const']) for f in refs}
                        assert len(constants)==1,('unresolved open-list member',module,member,refs)
                        mapped=constants.pop();parent,leaf=mapped.rsplit('.',1)
                        alias=self.sources[module][first:last].decode()
                        output.append('open _root_.'+parent+' renaming '+leaf+' -> '+alias)
                else:
                    raise AssertionError(('unhandled source open variant',module,opened))
            return '\n'.join(output)
        return edits(data,changes).decode()

    def skeleton(self,module,selected,*,flatten=False,skip_imported_syntax=False):
        """Subtract every unselected official declaration from this source."""
        selected=set(selected)
        data=self.sources[module]
        # The caller has copied the parsed header's remaining comments above
        # its replacement imports, preserving each source notice verbatim.
        context=self.contexts[module]
        changes=[(0,context['headerEndOffset'],b'')]
        for fact in self.facts[module]:
            if fact['kind']!='decl':continue
            a,b=fact['declStart']['offset'],fact['declEnd']['offset']
            uid=self.unit_by_span.get((module,a,b))
            value=self.declaration(self.units[uid]).encode() if uid in selected else b''
            changes.append((a,b,value))
        namespace=''
        stack=[]
        for command in self.contexts[module]['commands']:
            if command['hasDeclaration']:continue
            kind=command['syntaxKind'];a,b=command['startOffset'],command['endOffset']
            if kind in DIAGNOSTICS:
                changes.append((a,b,b''));continue
            if skip_imported_syntax and kind in {COMMAND+'macro',COMMAND+'mixfix'}:
                # The module's Def provider already exports this syntax.
                # Repeating mixfix declarations creates duplicate parses.
                changes.append((a,b,b''));continue
            if kind==COMMAND+'mixfix':
                # The legacy public library exports the same DSL tokens over
                # different types. Equal-priority choice nodes multiply over
                # long statement chains. Prefer the transplanted syntax while
                # preserving token spelling, associativity, and precedence.
                # The slot is supplied by Lean's mixfix parser, never text search.
                slot=self.mixfix_priorities[(module,a)]
                changes.append((slot,slot,b'(priority := high) '))
            if kind==COMMAND+'namespace':
                ids=command['identifiers'];assert len(ids)==1
                for part in ids[0]['name'].split('.'):
                    stack.append(namespace)
                    namespace=(namespace+'.' if namespace else '')+part
                # Quoted identifiers in macros have no resolved TermInfo ref.
                # Open the original canonical namespace so compatible provided
                # names are captured; relocated declarations remain nearest.
                changes.append((b,b,('\nopen _root_.'+namespace+'\n').encode()))
            elif kind==COMMAND+'section':
                ids=command['identifiers'];assert len(ids)<=1
                stack.extend([namespace]*(len(ids[0]['name'].split('.')) if ids else 1))
            elif kind==COMMAND+'end':
                ids=command['identifiers'];assert len(ids)<=1
                count=len(ids[0]['name'].split('.')) if ids else 1
                assert len(stack)>=count,(module,command)
                for _ in range(count):namespace=stack.pop()
            if flatten and kind in {COMMAND+'namespace',COMMAND+'section',COMMAND+'end'}:
                changes.append((a,b,b''));continue
            if kind==COMMAND+'open':
                changes.append((a,b,self.context_command(module,command,namespace).encode()))
                continue
            changes.extend((a+x,b_+a,value) for x,b_,value in self.reference_edits(module,a,b))
        body=edits(data,changes).decode().rstrip()+'\n'
        # Each native file may deliberately leave its public section open.
        # Close only parser-established live scopes, before closing wrapper.
        for frame in reversed(self.scope_stack(module)[1:]):
            body+='\nend'+(' '+frame['name'] if frame['name'] else '')+'\n'
        return 'namespace '+self.prefix+'\n\n'+body+'\nend '+self.prefix+'\n'

    def source_link(self,unit):
        module=unit['module'];fact=unit['fact']
        path=('Submission/Closed3Sum/'+module.removeprefix('Closed3Sum.').replace('.','/')
              if module.startswith('Closed3Sum.') else module.replace('.','/'))+'.lean'
        return self.plan['public_source_repository']+'/blob/'+self.plan['public_source_commit']+'/'+path+f"#L{fact['declStart']['line']}-L{fact['declEnd']['line']}"

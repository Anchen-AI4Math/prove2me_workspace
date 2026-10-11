"""Parser declaration-name facts disambiguate signature references; graph spans include docs."""
import analyze_oracles as original

def match_decl(facts,name,graph=None):
    # Both identifiers come from actual official parser/graph facts. No declaration regex.
    parsed_names={name,name.rsplit('.',1)[-1]}
    if graph is not None:parsed_names|={graph['userName'],graph['userName'].rsplit('.',1)[-1]}
    matches=[]
    for d in facts:
        if d.get('kind')!='decl' or d['nameText'] not in parsed_names:continue
        if any(ref.get('kind')=='ref' and ref['const']==name and
            d['declStart']['offset']<=ref['start']['offset']<d['valStart']['offset'] for ref in facts):
            if graph is not None:
                assert graph['startLine']<=d['declStart']['line']<=d['declEnd']['line']<=graph['endLine'],(name,graph,d)
            matches.append(d)
    assert len(matches)==1,(name,len(matches))
    return matches[0]

if __name__=='__main__':
    original.match_decl=match_decl
    original.main()

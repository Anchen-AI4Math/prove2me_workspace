"""Adversarial checks of the untrusted certificate input boundary."""
import json
from pathlib import Path
from generate_certificate import load_module

HERE=Path(__file__).resolve().parent

def main():
    ind=load_module('snaky_parser_tests',HERE/'source'/'verification'/'supporting'/'independent_evaluator.py')
    bad=['6 00 6','6 00','6 00 0:800','6 Z0 0','6 00 (11 0','6 00 0 )']
    for text in bad:
        try:
            ind.Parser(text,6).card()
        except ValueError:
            pass
        else:
            raise AssertionError('Accepted malformed certificate: '+text)
    source=(HERE/'source'/'verification'/'certificate.txt').read_text(encoding='ascii')
    cert=ind.Certificate(source)
    assert len(cert.postorder)==1620
    assert len(cert.postorder)-(len(cert.cards)-6)==898
    assert cert.cards[6].height==2 and cert.cards[7].height==3
    assert cert.cards[727].required==frozenset() and cert.cards[727].height==21
    groups=ind.final_groups(cert)
    assert [g['remaining'] for g in groups]==[35,31,21,12,4,0]
    report={'status':'PASS','malformed_inputs_rejected':len(bad),'numbered_cards':728,'all_combinations':1620,'nested_combinations':898,'successive_intersection_sizes':[35,31,21,12,4,0]}
    (HERE/'verification'/'input-tests.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('PASS: malformed references, empty combinations, bad symmetries, bad coordinates, and broken nesting rejected.')

if __name__=='__main__':
    main()

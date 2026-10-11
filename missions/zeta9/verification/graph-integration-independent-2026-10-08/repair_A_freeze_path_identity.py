from pathlib import Path
import hashlib,json
from prepare_A_independent import OUT,write,bind

def main():
    source=OUT/'freeze_A_independent.py';old=source.read_text(encoding='utf-8')
    assert not (OUT/'freeze_A_independent_v2.py').exists()
    write(OUT/'A-freeze-attempt1-source.py',old)
    write(OUT/'A-freeze-attempt1-terminal-error.txt',
        'Actual exec session 51005 terminated with exit 1. No Lean or API call.\n'
        'Full records were already written before this filesystem identity check failed.\n'
        'AssertionError: canonical Batteries.Classes.Cast.olean is reported under lowercase d: '
        'but its precompile binding path uses uppercase D:. Windows path identity is case insensitive.\n'
        'Original resolver records and all mathematical/Expr data remain unchanged.\n')
    replacement=old.replace('import hashlib,json,subprocess,sys,time','import hashlib,json,os,subprocess,sys,time')
    replacement=replacement.replace("baseline={str(pathof(r).resolve()):r for r in preflight['stock_precompile_bindings']}","baseline={os.path.normcase(str(pathof(r).resolve())):r for r in preflight['stock_precompile_bindings']}")
    replacement=replacement.replace("str(Path(row['record']['canonical_olean']).resolve()) in baseline","os.path.normcase(str(Path(row['record']['canonical_olean']).resolve())) in baseline")
    # The first pure freezer already wrote records. V2 recomputes and demands byte equality.
    replacement=replacement.replace("dest=OUT/'A-full-records'/tag/(mod+'.jsonl');write(dest,''.join(json.dumps(r,ensure_ascii=False)+'\\n' for r in rows));files.append(bind(dest))", "dest=OUT/'A-full-records'/tag/(mod+'.jsonl');text=''.join(json.dumps(r,ensure_ascii=False)+'\\n' for r in rows)\n            if dest.exists():assert dest.read_text(encoding='utf-8')==text\n            else:write(dest,text)\n            files.append(bind(dest))")
    assert replacement!=old and 'os.path.normcase' in replacement
    replacement=replacement.replace("bind(Path(__file__))]", "bind(Path(__file__)),bind(OUT/'A-freeze-attempt1-source.py'),bind(OUT/'A-freeze-attempt1-terminal-error.txt'),bind(OUT/'A-freeze-path-identity-repair.json')]")
    write(OUT/'freeze_A_independent_v2.py',replacement)
    write(OUT/'A-freeze-path-identity-repair.json',dict(status='PURE_FREEZE_FILESYSTEM_PATH_IDENTITY_REPAIR',actual_failed_freeze_session=51005,exit_code=1,original_freezer=bind(source),original_snapshot=bind(OUT/'A-freeze-attempt1-source.py'),failure_evidence=bind(OUT/'A-freeze-attempt1-terminal-error.txt'),V2_freezer=bind(OUT/'freeze_A_independent_v2.py'),Windows_case_insensitive_path_key_only=True,all_resolver_raw_paths_retained=True,no_mathematical_Expr_or_type_value_normalization=True,no_Lean_or_API_rerun=True,first_frozen_full_records_retained_and_recomputed_byte_equality_required=True))
    print(json.dumps(dict(status='PURE_FILESYSTEM_IDENTITY_V2_READY',Lean_calls=0,API_calls=0)))
if __name__=='__main__':main()

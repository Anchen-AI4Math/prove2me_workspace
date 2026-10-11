from run import *

source=PROJECT/'missions/zeta9/formalization/CoefficientMapNumeratorPartialFractions.lean'
final=source.read_bytes()
receipt=load(OUT/'compile-receipt.json')
original=next(r for r in receipt['rows'] if r['label']=='r02')
assert original['source_sha256']==sha(OUT/'p0.lean')
try:
    write(source,(OUT/'p0.lean').read_bytes())
    code=run('explicit same-byte first PF object regeneration after file-header-only final build',source,
             'missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions',OUT/'r02.olean')
    assert code==0
    assert sha(OUT/'r02.olean')==original['output_sha256']
finally:
    write(source,final)
dump(OUT/'historical-object-regeneration.json',{
    'initial_source_log_and_exit_retained_unchanged':True,
    'initial_output_was_replaced_by_header_only_final_build_before_snapshot':True,
    'first_object_explicitly_reproduced_from_identical_original_project_source_bytes':True,
    'reproduced_object_sha256_exact_matches_initial_actual_output_hash':sha(OUT/'r02.olean'),
    'initial_output_sha256':original['output_sha256'],
    'final_project_source_restored':sha(source),
    'final_project_cache_object_not_overwritten_by_regeneration':True,
    'regeneration_is_a_separate_actual_successful_invocation':True})
print('Original first PF output archive reproduced exact; final own cache untouched.',flush=True)

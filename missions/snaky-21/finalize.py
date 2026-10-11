"""Require closed-kernel and live-platform evidence before marking complete."""
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime,timezone,timedelta
from pathlib import Path
import pipeline
import publish
import local_completion

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}
BASELINE={
    'ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean; add it to a mission scope.json',
    'ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean; add it to a mission scope.json',
}

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    if not local_completion.unchanged():
        raise RuntimeError('The actual proof sources changed after their completed audit')
    log=(HERE/'verification'/'closed-build.log').read_text(encoding='utf-8')
    match=re.search(r"'OAI\.Snaky21\.snaky21_complete' depends on axioms: \[([^\]]*)\]",log)
    if not match or 'Build completed successfully' not in log:
        raise RuntimeError('Missing successful closed build and main axiom audit')
    axioms={s.strip() for s in match.group(1).split(',') if s.strip()}
    if not axioms<=ALLOWED:
        raise RuntimeError('Unexpected main axioms: '+str(axioms))
    check=subprocess.run([sys.executable,'-B','scripts/workspace.py','check'],cwd=ROOT,env=pipeline.environment(),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    errors={s for s in check.stdout.splitlines() if s.startswith('ERROR:')}
    if errors-BASELINE:
        raise RuntimeError('New workspace errors: '+str(errors-BASELINE))
    (HERE/'verification'/'workspace-check.log').write_text(check.stdout,encoding='utf-8')
    target=publish.request('GET','/theorems/29b16242-e6c3-4ee3-b459-3e4a883b9dcc',publish.api.get_token())
    if target['status']!='Proved':
        raise RuntimeError('Main goal is '+target['status'])
    journal=publish.read_journal()
    # A sketch's children can finish after the queue saved its intermediate
    # result. Refresh those submission records once all targets are proved.
    for key,value in journal.items():
        if key.startswith('proof:') and value.get('status')=='SKETCH_ACCEPTED':
            verified=publish.request('GET','/verify?submission_id='+value['submission_id'],publish.api.get_token())
            if verified['status']!='ACCEPTED':
                raise RuntimeError('A support submission has not resolved to ACCEPTED: '+key+' '+verified['status'])
            value.update({'status':verified['status'],'result':verified})
    publish.save_journal(journal)
    umbrella=journal.get('definition:Snaky21Calc11',{})
    if umbrella.get('status') in ('PENDING','COMPILING'):
        job=publish.request('GET','/publish-jobs/'+umbrella['job_id'],publish.api.get_token())
        umbrella.update({'status':job['status'],'theorem_id':job.get('theorem_id'),'error_message':job.get('error_message')})
        publish.save_journal(journal)
    root=journal['proof:'+target['theorem_name']]
    if root['status']!='ACCEPTED':
        raise RuntimeError('Our main submission is not ACCEPTED')
    submissions=publish.request('GET','/theorems/'+target['theorem_id']+'/submissions?status=ACCEPTED&limit=200',publish.api.get_token())
    own=next((item for item in submissions['submissions'] if item['id']==root['submission_id']),None)
    if own is None or own['user_id']!='418b0711-62a5-416a-ba5d-876ae8758fe3':
        raise RuntimeError('Live accepted main submission is not attributed to the expected user')
    (HERE/'verification'/'final-account-record.json').write_text(json.dumps(own,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    # The API defaults to a shallow graph. Expand the original goal through
    # the grouped certificate proofs before checking for orphaned supports.
    graph_depth=30
    graph=publish.request('GET','/theorems/'+target['theorem_id']+'/graph?depth='+str(graph_depth),publish.api.get_token())
    (HERE/'verification'/'final-graph.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    connected={node.get('theorem_id') for node in graph['nodes']}
    # The captain-linked 35-move milestones have their own roots. Their later
    # support proofs belong to those graphs rather than the 21-move goal.
    unconnected=[key for key,value in journal.items() if key.startswith('theorem:OAI.Snaky21.') and value.get('theorem_id') and value['theorem_id'] not in connected]
    if unconnected:
        raise RuntimeError('Published support theorems are absent from the original goal graph: '+str(unconnected))
    (HERE/'verification'/'final-platform.json').write_text(json.dumps(target,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    sources={}
    for folder,pattern in [(ROOT/'Solutions'/'Snaky21','*.lean'),(ROOT/'Definitions','Def_Snaky21*.lean')]:
        for path in folder.glob(pattern):
            sources[path.relative_to(ROOT).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    original=ROOT/'Definitions'/'Def_SnakyTwentyOne.lean'
    sources[original.relative_to(ROOT).as_posix()]=hashlib.sha256(original.read_bytes()).hexdigest()
    certificate=HERE/'source'/'verification'/'certificate.txt'
    certificate_sha256=hashlib.sha256(certificate.read_bytes()).hexdigest()
    if certificate_sha256!='3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04':
        raise RuntimeError('The pinned source certificate changed')
    report={'status':'COMPLETE','main_theorem_id':target['theorem_id'],'main_status':target['status'],
            'main_submission_id':root['submission_id'],'axioms':sorted(axioms),
            'user_id':own['user_id'],'username':own['username'],'accepted_at':own['accepted_at'],
            'dependency_graph_depth':graph_depth,'dependency_graph_nodes':len(graph['nodes']),
            'dependency_graph_edges':len(graph['edges']),
            'unconnected_support_theorems':[],
            'accepted_proofs':sum(v.get('status')=='ACCEPTED' for k,v in journal.items() if k.startswith('proof:')),
            'published_definitions':sum(v.get('status')=='PUBLISHED' for k,v in journal.items() if k.startswith('definition:')),
            'new_workspace_errors':[],'preexisting_workspace_errors':sorted(errors),'source_sha256':sources,
            'certificate_sha256':certificate_sha256,'numbered_cards':728,'nested_combinations':898,
            'final_height':21,'final_required_cells':0,'final_envelope_cells':251,
            'submissions':{k:v for k,v in journal.items() if k.startswith('proof:')}}
    (HERE/'verification'/'final-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    checked_date=datetime.now(timezone(timedelta(hours=8))).strftime('%Y-%m-%d')
    status=f'''# Snaky 21 步任务：完成

核对日期：{checked_date}。平台原主目标 **Proved**，本次主证明提交 **ACCEPTED**。

- 任务：https://prove2.me/missions/Snaky_in_21_Maker_moves
- 主定理：`{target['theorem_name']}`
- theorem_id：`{target['theorem_id']}`
- submission_id：`{root['submission_id']}`
- 贡献账号：`{own['username']}`，user_id `{own['user_id']}`；已实时核对 ACCEPTED 记录。
- 固定论文提交：`adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`

## 核验

`python scripts/workspace.py build snaky-21` 通过。实际闭合证明的公理依赖仅为
`{', '.join(sorted(axioms))}`；没有 `sorryAx` 或计算预言机公理。
原证书 SHA256 与固定源一致，两套重建逐卡一致。所有 728 张编号卡片及 898 个嵌套组合的
三字段等式经 kernel 检查；最终所需集合为空、高度 21、包络 251 格且包含于指定 17×17 方格。
目录数量与全部高度界另行验证。策略合法于所有有限输入，且不要求第 21 次 Breaker 应答合法。

平台贡献沿组合规则、放置/基础演算、编号卡片块、最终证书和策略抽取连接到原主目标。
上层较大卡片块分成小组，适应服务器编译时限。

工作区结构检查没有新增错误；原有两个 five-primes 未归属文件未改动。

## 文件

- 闭合本地主定理：`Solutions/Snaky21/Main.lean`
- 数学说明：`missions/snaky-21/proof-explanation-zh.md`
- 构建与公理日志：`verification/closed-build.log`
- 完成报告：`verification/final-report.json`
- 实时平台快照：`verification/final-platform.json`
- 提交明细：`platform/journal.json`
- 正式主目标提交源码：`platform/main-proof.lean`

`Theorems/Thm_OAI_Snaky21*.lean` 为平台接口镜像中的占位声明，不能用于独立完成性审计。
上述闭合本地证明使用实际 Solutions 证明模块。
'''
    (HERE/'status.md').write_text(status,encoding='utf-8')
    print('COMPLETE: live main goal Proved, our submission ACCEPTED, standard axioms only.',flush=True)

if __name__=='__main__':
    main()

"""Update current navigation from verified records, preserving historical bytes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os

TASK = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent / "current-progress-57"
PLATFORM = "formalization/platform/readback-2026-10-07/user-submission-current-57/progress-audit.json"
BUILD = "formalization/platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/root-scoped-build/actual-build-receipt.json"
PF = "formalization/platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/publication-audit.json"
PARAMETER = "verification/formalization-coefficient-map-parameter-summation-author-2026-10-07/author-audit.json"
PARAM_REHASH = "verification/formalization-project-handoff-2026-10-07/root-parameter-author-complete-binding-rehash.json"
PHASE = "verification/formalization-analytic-phase-upper-bound-2026-10-07/author-audit.json"
PHASE_REHASH = "verification/formalization-project-handoff-2026-10-07/root-phase-author-complete-binding-rehash.json"


def load(rel):
    return json.loads((TASK / rel).read_text(encoding="utf-8"))


def binding(p):
    data = p.read_bytes()
    return {"task_relative": p.relative_to(TASK).as_posix(), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def link(base, label, rel):
    target = os.path.relpath(TASK / rel, base).replace("\\", "/")
    return f"[{label}]({target})"


def main():
    assert not OUT.exists(), "Preserve earlier current-document reports"
    platform = load(PLATFORM)
    assert (platform["proposal_status"], platform["visibility"], platform["mission_id"]) == ("In review", "public", None)
    assert platform["Accepted_complete_proof_receipts"] == 57
    assert platform["all_saved_complete_proofs_Accepted_public_Proved"]
    assert platform["new_global_PF_Proved_not_referenced"] == 3
    build = load(BUILD)
    assert build["official_task_build_complete"] and all(r["exit_code"] == 0 for r in build["rows"])
    assert load(PARAMETER)["verdict"] == "PASS"
    assert load(PARAM_REHASH)["stable_bindings"] == 755 and load(PARAM_REHASH)["mismatches"] == 0
    assert load(PHASE)["status"] == "NATIVE_ACTUAL_PHASE_AUTHOR_PASS"
    phase_rows = load(PHASE_REHASH)["results"]
    assert len(phase_rows) == 1 and phase_rows[0]["bindings_rehashed"] == 25818
    assert phase_rows[0]["mismatches"] == 0
    OUT.mkdir()
    counts = ("新提案包含 88 个引用项（18 个定义）和 69 条里程碑；"
              "67 个支持定理为 `Proved`，两个支持定理及无理性根目标仍为 `Open`。"
              "**57 份已保存完整证明回执全部 `ACCEPTED`**。")
    chinese = """当前使用新公开提案 **Irrationality of ζ(9)**，ID
`19653cff-d481-498a-a717-10630d1ca1b7`。用户已提交；最新 v0.12.1 认证回读为
**`In review / public`**，`mission_id` 为空，等待平台审核。用户提交步骤已完成。
""" + counts + "\n\n" + """Matrix 三条定理已获完整证明验收，并被新提案引用。新增通用分子部分分式
三条定理及一个定义也已公开，三份完整证明全部 Accepted：实际多项式部分分式、
实际有理函数部分分式和完整局部系数单射性。它们尚未被审核中的提案引用。
七个对应本地模块已逐个构建，随后正式运行 `python scripts/workspace.py build zeta9` 成功。
该任务构建保留既有 PNT statement mirror 的类型集成边界；完整 PNT 证明有另行独审记录。
"""
    local = """最新本地阶段：16 条五输出运输原生作者证明已通过；17 条参数求和运输的原生作者
冻结也已通过，Root 重哈希 755 个绑定无差异。后者包括偶数 n ≥ 2 的真实 HasSum、
绝对可和、tsum 及选定输出运输；独审及平台移植仍待完成。
解析相位的 34 条原生作者证明已通过，给出所有 x > 1 的 phase(x) ≤ −2641/250；
Root 重哈希全部 25818 个绑定无差异，独审仍待完成。
新阶乘对数界仅有完整 SOURCE 草稿，尚未编译。
全体加权矩的统一解析估计 Z9.A、整数原像与分母高度、J 和 ζ(9) 无理性仍未封闭。
"""
    english = """The active target is the submitted public proposal **Irrationality of ζ(9)**,
`19653cff-d481-498a-a717-10630d1ca1b7`. The current authenticated v0.12.1 readback
is **In review / public**, with `mission_id: null`. Human submission is complete;
moderator review is pending. The proposal has 88 references (18 definitions),
69 milestones, 67 Proved supporting theorems and two Open supporting theorems.
The irrationality root remains Open. All **57 saved complete proof receipts are ACCEPTED**.

The Matrix proofs are public Proved and referenced. The three newly accepted
numerator-PF proofs and one public definition are not yet referenced by the
frozen proposal. Seven exact local modules passed serial builds and the official
scoped zeta9 task build. Its existing PNT statement-mirror type-integration
limitation is retained; complete PNT source proofs have separate independent evidence.

Outputs16 native author verification has passed; independent review is pending.
Parameter-summation17 native author verification has passed; Root streamed all
755 frozen bindings with zero mismatches. Its 34 actual calls include 31 successes
and three preserved historical failures, with all final required controls successful.
Independent review and platform transplantation remain pending.
Phase34 native author verification proves phase(x) ≤ −2641/250 for every x > 1.
Root streamed all 25818 bindings with zero mismatches; independent review is pending.
The factorial-log bounds are complete SOURCE candidates and remain uncompiled.
Full uniform weighted-moment Z9.A, integer preimage/height, J and irrationality remain open.
"""
    mapping = [
        ("status.md", "## Current platform target — 2026-10-07", "## Historical 2026-10-04 snapshot (preserved)", english),
        ("README.md", "## 2026-10-07 当前平台目标", "## 以下保留 2026-10-04 交接快照", chinese + "\n" + local),
        ("PUBLIC_OVERVIEW.md", "## 2026-10-07 当前平台目标", "## 以下保留 2026-10-04 研究快照", chinese + "\n" + local),
        ("formalization/README.md", "## 2026-10-07 当前平台目标与验证边界", "## 以下保留 2026-10-04 形式化快照", chinese + "\n" + local),
        ("formalization/COEFFICIENT_ROUTE.md", "## 2026-10-07 当前平台目标与最新本地阶段", "## 以下保留 2026-10-04 构造链快照", chinese + "\n" + local),
    ]
    reports = []
    for rel, start, historical, body in mapping:
        p = TASK / rel
        before = p.read_bytes()
        start_bytes, historical_bytes = start.encode(), historical.encode()
        assert before.count(start_bytes) == before.count(historical_bytes) == 1
        a, b = before.index(start_bytes), before.index(historical_bytes)
        assert a < b
        links = [link(p.parent, label, path) for label, path in [
            ("Current platform readback", PLATFORM), ("PF acceptance", PF),
            ("Scoped task build", BUILD), ("Parameter author Root rehash", PARAM_REHASH),
            ("Phase author Root rehash", PHASE_REHASH)]]
        block = start + "\n\n" + body + "\n" + ", ".join(links) + ".\n\n"
        after = before[:a] + block.encode("utf-8") + before[b:]
        assert after[after.index(historical_bytes):] == before[b:]
        p.write_bytes(after)
        reports.append({"path": rel, "before_sha256": hashlib.sha256(before).hexdigest(),
                        "after": binding(p), "historical_tail_sha256": hashlib.sha256(before[b:]).hexdigest(),
                        "historical_tail_byte_identical": True})
    target = TASK / "publication/2026-10-07/new-public-mission/CURRENT_PLATFORM_TARGET.json"
    (OUT / "target-before.json").write_bytes(target.read_bytes())
    v = json.loads(target.read_text(encoding="utf-8"))
    v.update(current_accepted_complete_proof_receipts=57,
             current_readback_checked_at=platform["checked_at"], current_readback_source=PLATFORM,
             numerator_PF_platform_author="Author and independent review passed; all three complete proofs ACCEPTED/public Proved",
             numerator_PF_new_global_theorems_not_yet_referenced=3,
             numerator_PF_new_global_definitions_not_yet_referenced=1,
             numerator_PF_publication_audit=PF, numerator_PF_official_scoped_build=BUILD,
             numerator_PF_Root_installed_modules=7, registered_task_build_patterns=59,
             parameter_HasSum_transport_candidates="17 original complete endpoints native author PASS; 755 bindings Root rehashed, zero mismatches; independent/platform pending",
             parameter_HasSum_transport_author_report=PARAMETER,
             parameter_HasSum_transport_Root_rehash=PARAM_REHASH,
             analytic_phase_compilation="34 original complete endpoints native author PASS, all x>1 phase(x)<=-2641/250; independent/platform pending; full Z9.A open",
             analytic_phase_Root_rehash=PHASE_REHASH,
             factorial_logarithm_bounds="complete SOURCE candidates; UNCOMPILED",
             all_local_research_formalized=False)
    target.write_text(json.dumps(v, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    report = {"updated_at": datetime.now(timezone.utc).isoformat(), "documents": reports,
              "current_target": binding(target), "evidence": [binding(TASK / r) for r in [PLATFORM, PF, BUILD, PARAMETER, PARAM_REHASH, PHASE, PHASE_REHASH]],
              "historical_records_overwritten": False, "Lean_calls": 0, "API_calls": 0,
              "whole_goal_complete": False}
    (OUT / "current-documents-report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"current_documents_updated": 5, "historical_tails_unchanged": 5, "accepted_proofs": 57, "scoped_build_complete": True}))


if __name__ == "__main__":
    main()

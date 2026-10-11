# Platform API review

The normal authorized token refresh returned server version 0.12.3 on 2026-10-09. The shared workspace documentation remains at 0.12.1; it was not overwritten.

The official current SKILL.md reports 0.12.3. Its current contribute.md and prove.md were read directly from the official repository. The `/submit-problem`, `/publish-jobs/{id}`, `/verify`, theorem readback, and theorem-description PATCH contracts used by this stage retain the expected fields and asynchronous status flow. Public theorem and Definition imports are allowed for problem submission and proof verification. Each proof remains a literal top-level `theorem solution` without its own target import or `sorry`.

The returned submission guidelines were reviewed: use standard mathematical notation, a display-math formula and a short mathematical-role paragraph for public descriptions, and explain the mathematical argument for proof submissions. The dimension publisher's description is being adjusted before its first POST. The already published minimum-weight description will receive a recorded presentation-only correction after its own Accepted/Proved readback; the formal statement and proof bytes remain pinned.

Official references read:

- https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/SKILL.md
- https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/references/contribute.md
- https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/references/prove.md

The v0.12.3 release/tag URLs were unavailable through the browsing tool. The current official version and relevant endpoint documentation were verified; no shared Lean/Mathlib configuration was changed.

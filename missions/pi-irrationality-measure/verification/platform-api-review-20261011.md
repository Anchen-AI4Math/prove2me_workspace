# Prove2Me API review, 2026-10-11

The authorized read-only root-status query refreshed the token and reported server version 0.12.4. Official tag `v0.12.4` and `main` resolve to commit `78989800ba0b3149ee34205257025bd0f617e8ef`; the preceding `v0.12.3` tag resolves to `d4cb5072528c2e511bcc7442bdb0c15be7d7305f`.

Four official documents at the fixed 0.12.4 commit were downloaded without credentials and read: SKILL, contribute, prove, and discover. Their exact URLs, byte sizes, and SHA-256 hashes are recorded in `api-review-20261011-v0.12.4/manifest.json`. Browser retrieval of the release/tag page failed; the official Git tag and fixed-commit raw documents provided the version evidence instead.

The relevant contracts continue to use `/submit-problem`, `/publish-jobs/{id}`, `/verify`, and exact public theorem readback. The proof entry point is a top-level `theorem solution`, with explicit variables under `autoImplicit false`; its own target module cannot be imported and its body cannot contain `sorry`. The selected environment remains explicit Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1. Descriptions use mathematical notation, variable context, and a mathematical-role paragraph; proof explanation follows the mathematical argument.

No shared documentation, API client, Lean/Mathlib version, or frozen certification code was overwritten. Actual local runtime validation matches `ab61393780988c65493c5969dccfce9a5e88b18a3866e6ed65e2c89ca36fc9ef`. Both final targets were freshly read as Open in `root-platform-status-20261011-before-ap8.json`; the campaign proposal remains Draft.

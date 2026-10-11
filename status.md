# Prove2Me workspace dashboard

Navigation refreshed: 2026-10-11 (Asia/Shanghai). Platform state was not refreshed
as part of this local reorganization. Each mission handoff owns its dated status.

## Start here

Open `missions/<slug>/` for a focused agent session. Build only that task with
`python scripts/workspace.py build <slug>`; bare `lake build` now selects an empty
workspace target and does not validate any mission.

- [All missions and workstreams](missions/README.md) — includes Magic Squares I–V,
  node maintenance, and the number-theory textbook proposal.
- [Workspace layout and contribution rules](docs/workspace-layout.md)
- [Large verification data: verify and restore](archives/verification/README.md)
- [Workspace cleanup record](docs/workspace-cleanup-2026-10-11.json)
- [Earlier dashboard and full historical work log](docs/history/status-before-2026-09-20.md)
- [Platform workflow](SKILL.md)

## Find a task

The [mission index](missions/README.md) is the single navigation table for all
21 workstreams, including the pi irrationality-measure and Snaky tasks.
Use `python scripts/workspace.py list` for the current registry and
`python scripts/workspace.py show <slug>` for the selected handoff and tools.

## Shared environment

Read `lean-toolchain` and `lake-manifest.json` for the pinned environment.
Keep `.lake/` for dependency and build reuse. Platform-facing module paths remain
`Definitions/`, `Theorems/`, and `Solutions/`; local helper targets are declared
in `lakefile.lean`. A different platform toolchain needs a separate checkout.

Update the relevant mission handoff after work. Keep detailed chronology there;
this page stays a short navigation dashboard.

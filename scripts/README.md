# Shared tools

- `p2m_api.py`: platform API client (some commands perform writes).
- `extract_decl_graph.lean`, `extract_sketch_info.lean`: Lean inspection tools.
- `workspace.py`: offline mission navigation, scoped builds and layout validation.
- `test_workspace.py`: build-isolation regression checks (`python scripts/test_workspace.py`).
- `workspace_data.py`: lossless packing, SHA-256 verification and restoration of large evidence records. See [archive instructions](../archives/verification/README.md).
- `test_workspace_data.py`: archive round-trip, corruption and overwrite protection checks (`python scripts/test_workspace_data.py`).

Mission-specific scripts are under `missions/<slug>/scripts/`.
Run `python scripts/workspace.py show <slug>` to find them.
See [the migration map](../docs/script-migration.json) for previous paths.

Use `python scripts/workspace.py files <slug>` for source navigation and
`python scripts/workspace.py build <slug> --dry-run` to inspect build roots.
Drop `--dry-run` to build only those roots and their imports, using the shared
pinned toolchain. Research-only tasks report that no target is registered.

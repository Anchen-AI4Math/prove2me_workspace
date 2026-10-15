# Expansion-232 machine extension

`lean/Submission/` contains the ten-module dependency closure of the pinned
upstream Light scalar safety library, plus the new quartic switch implementation.
The immutable upstream snapshot remains under `../verification/upstream`.
`../verification/machine-port-manifest.json` pins each inherited source hash.

`QuarticSwitch.lean` implements the exact degree-four integer comparison,
least accepted integer scan, scalar safety and a linear-in-residual Light
execution bound. `ActualQuarticSwitch.lean` connects admissible depths to the
accepted finite scheduling theorem, including the zero-residual case.
Both are local machine work; their compilation status is recorded in the
mission verification logs. They have not been uploaded as a complete project.

`lean/Closed3Sum/` is generated from exact ACCEPTED proof solutions, changing
only module imports and the top-level theorem names. The local definition
copies have identical declaration bodies with focused mathematical imports,
to avoid loading the whole Mathlib library into each audit process. Its manifest records
accepted submission IDs and source hashes. These mirrors are intended for
independent kernel axiom audits and eventual standalone packaging, rather than
using local `by sorry` platform reference files as final proof artifacts.

Build through `python scripts/workspace.py build 3sum-1960614`. The root Lake
library is opt-in through this mission's wrappers. The full cover, global
encoding, cost assembly, hybrid solver and unchanged word-RAM end statement
remain necessary before a Big O Speedrun submission.

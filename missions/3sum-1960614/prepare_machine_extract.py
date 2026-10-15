"""Configure the platform's Lean declaration oracle for built machine roots."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
code=(ROOT/'scripts/extract_decl_graph.lean').read_text(encoding='utf-8')
assert 'import SumSquares' in code and 'let projPrefix := `SumSquares' in code
code=code.replace('import SumSquares',
 'import Submission.ThreeSum.ActualQuarticSwitch\nimport Submission.ThreeSum.LocalCoverBounds',1)
code=code.replace('let projPrefix := `SumSquares','let projPrefix := `Submission',1)
code=code.replace('let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m',
 'let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m || (`Closed3Sum).isPrefixOf m',1)
code=code.replace('IO.FS.writeFile "decl_graph.jsonl"',
 'IO.FS.writeFile "missions/3sum-1960614/verification/machine-decl-graph.jsonl"',1)
(HERE/'verification/extract_machine_decl_graph.lean').write_text(code,encoding='utf-8')
print('Prepared unchanged declaration oracle with machine imports and output path.')

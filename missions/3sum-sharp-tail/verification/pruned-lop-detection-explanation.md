This proof constructs a native uniform Lop counter from the actual
`program31P G`. An explicit finite program tests `D^B <= N^A`; it calls the
parameterized offline routine in that regime and the actual thin-brute
routine otherwise. Both branches prove `SolvesN` with polynomial word, cell,
and depth needs, for every valid input, memory, free pointer, and appended
program. The fallback is proved from its loop implementation, rather than
assumed as an oracle.

The exact rational-power equivalence connects the finite test to
`D <= N^a`. The native Count-to-Detect program then changes positive counts
to flags, with explicit address and word safety. Its final time bound uses
the already-Proved offline step certificate, including the test overhead
and the `N*D+w+1` detector overhead. The only theorem imports are the
Proved native resource wrapper, rational-power representation, and offline
step bound. This is the generic original Lop-detection interface; it does
not assume the remaining 3SUM reduction.

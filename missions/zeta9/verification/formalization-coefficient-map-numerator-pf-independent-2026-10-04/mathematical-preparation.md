This is an independent, uncompiled preparation note for the fixed final PF
source `2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77`.
The reviewer did not author this NumeratorPartialFractions source. Data is an
inherited dependency previously authored by this reviewer; that authorship is
disclosed, and Data will still be rebuilt from its frozen source in this new
empty project. No existing Data object will be borrowed.

The new PF proofs use the actual shifted numerator and the actual inverse
cleared denominator. Nine truncated coefficients match each pole modulo X^9.
Pairwise coprime pole factors give full denominator divisibility of A minus the
candidate. Only the final proper-numerator reconstruction uses the strict bound
deg(A) < 9(m+1); its candidate bound 9m+8 is compatible also at m=0. Actual
division uses regularity at every k=0,...,m, with all orders s=1,...,9 included.
The injectivity proof retains strict properness of both A and B so their
difference stays strictly below the full denominator degree.

Prepared independent controls distinguish the unconditional divisibility/jet
matching results from reconstruction and injectivity. At m=0, X^9 is nonzero
but all nine principal-part coefficients vanish; it is excluded by the strict
degree condition. X^8 is admissible but yields 1/t, so properness alone cannot
be used to claim absolute summability. Controls retain k=0,8 and s=1,9, both
real poles t=0,-1, a regular two-pole point t=1, and an off-range denominator
identity whose source type legitimately needs no j<=m hypothesis.

This preparation does not establish arbitrary principal-part array uniqueness,
the desired local coefficient parameter transport, all five output transport,
integer heights, HasSum parameter transport or irrationality. Data's historical
UNCOMPILED header is preserved literally; successful author compilation is
separate evidence and is not an independent PASS. All expected type controls,
full-value Meta/rfl checks and own boundaries remain uncompiled until the
parent grants a Lean lane.

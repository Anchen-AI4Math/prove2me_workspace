# Matrix platform preparation

This directory contains pure offline preparation for the actual monomial-row
matrix and its selected rational inverse. No Lean or Lake has been run for this
platform batch. The native Matrix source and its prior author/independent audits
are inputs, not evidence that this new transplantation has compiled.

The three selected original declarations are:

- `actualFMatrix_det_ne_zero`: the genuine F determinant is nonzero.
- `selectedIntegerMultiplier_coordinates_product`: the actual rational
  multiplier's coordinates equal `(b,a) * S * F⁻¹`.
- `selectedIntegerMultiplier_actual_HasSum_and_absolute`: the actual positive
  integer weighted-R series has sum `b+a*zetaReal 9` and summable norms.

Each retains `n>=2` and `Even n`. Integers b and a specify the output; the inverse
matrix and multiplier remain rational. No invertibility, determinant, aggregate
kernel, sum, summability or zeta-independence premise is added. Integer inverse
coefficients, heights, small integer forms, transport and irrationality are
separate obligations.

`prepare.py` verifies all 517 frozen native-independent bindings and the fixed
source/author/review hashes. It prepares 13 genuine native source files, 12 exact
installed parent Definition sources, four original controls, and graph/parser/
header tools. The fresh author project is `.rt/ma1`; its proof cache and `.lake`
are absent at this checkpoint. The longest planned `.olean` path plus 64 reserved
characters is 242, within the Windows limit 259.

`execute_oracles.py` is a future lane-gated serial driver. Its 44 planned calls
include 13 native compiles, four native controls, 11 further parent Definition
compiles, one graph, 13 source parsers, one header and one runtime query. It must
only be started after Root explicitly grants a Lean lane. It retains all actual
attempts and permits only its own proof cache plus the fixed Mathlib package
cache. The four original control sources are copied unchanged.

After those actual oracles, five Matrix Definition bodies must be taken from
the actual source spans. The actual type/value graph and source parser determine
the complete cross-module helper closure for each Solution, including instances
and namespace opens. The 17 original Matrix proof bodies remain complete. No
Matrix target Theorem or Solution is imported to prove itself. The three
reference statements may contain explicit `sorry` only as statement mirrors;
they are excluded from proof evidence.

Full native and staged shared-alias kernel checks must compare all five whole
Definition types and values, with full Expr/proof output and closed whole-function
rfl checks. Existing KernelBridge/Aggregate proof-bearing data use the actual
frozen parent definitions and their established complete value evidence. The
new Matrix graph's actual `valueDeps` and reference spans must justify every
dependency; this preparation does not invent those edges or source positions.

The new batch's actual graph count, helper closure size and compilation results
are pending. The count 70 for project definitions is a planning expectation from
the preceding actual Kernel batch plus the five Matrix definitions, explicitly
pending this batch's own graph. A separate non-author platform review, Root
scoped build, publication and platform acceptance remain later steps.

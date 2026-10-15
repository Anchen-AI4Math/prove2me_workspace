This proof gives native polynomial word, cell and depth needs for arbitrary
`RatParams G`. Its conclusion is an actual `Meets` specification for the
original `program31P G` offline procedure, for every appended program and
free pointer, under the exact `CostsWithinP` and `lopCountTask.Pre` conditions.

The generic Hyp30 below/top bounds control the true data-structure layout
by powers of `(N+1)^5`. Only finite coefficients in the need depend on G.
The word need includes parameter-procedure overhead, the space need covers
the original top address, and the depth need bounds the actual recursion.
Polynomiality is established explicitly by a degree-20 product bound.
The final execution proof composes these limits with the already-Proved
generic program correctness theorem and extends it to appended programs.

This resource theorem is an intermediate program statement. It does not
by itself establish the global detector, the new Exact Triangle exponent,
or the final 3SUM bound.

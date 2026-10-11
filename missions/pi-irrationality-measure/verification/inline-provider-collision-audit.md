# Inline-provider collision audit

Snapshot: 799-module provisional plan, 312 nodes, 5335 units. Full extraction is still incomplete. All counts and complete DAG/range/scope/reference evidence are in `inline-provider-collision-audit.json`, bound to the exact plan/inventory/graph SHA-256 values.

- 326 public theorem names from 325 shared commands are copied into multiple nodes; 888 shared placements across 166 nodes. All are at most ten proof lines.
- 84 node import closures contain duplicate public helper providers. The existing own-inline versus direct-child-inline guard catches 62; 22 transitive/sibling cases are not caught at the consumer.
- 24 nodes also encounter the existing private-inline rejection. Every one of the 312 nodes is reachable from the original root; the current generator cannot generate the complete root tree.

Minimal direct example: `FormalLogTruncation.logTail_mem_rationalWeightedIdeal` imports `liftSeries_eq_toMvPowerSeries`; both copy `FormalLogJet.coeff_liftSeries`. The helper is bytes 510–876, its AST theorem token is 518–525, and its binding is 526–542. Insert private at the theorem token, preserving the preceding simp attribute. The two consumer references are bytes 616–645 and 13053–13082 in FormalLogTruncation.

Sibling example: `RetainedPrimeCycle.retainedChild_dimension` imports `prime_hilbert_natDegree_add_one_eq_krullDim` and `minimal_prime_hypersurface_dimension`; both export `exists_finite_normalization_with_dimension` from PrimeHilbertDimension lines 81–88. The parent does not copy this helper, so its current direct guard misses the collision.

Three public helper names occur in four node statements: `logTail_constantCoeff`, `finite_zeroIdeal_of_mono` (two consumers), and `primeRectangular_maps_maximal`. These must have canonical importable public proved providers rather than node-private clones. Recommend adding all reachable theorem type-dependency roots to the planner's importable theorem closure; propagate complete body/type/constructor and whole-command closure into Definition-embedded material, unless an explicitly reviewed public child-node provider preserves the exact source interface and axiom dependencies. Do not reclassify only private statement dependencies while leaving public statement helpers inline.

The one shared non-atomic command is `@[reassoc] affinePresentation_comp`, which also creates `affinePresentation_comp_assoc`; it needs separate companion-name evidence and is rejected by the narrow isolation prototype.

Isolation invariants: preserve source scopes and wrappers; use authoritative theorem-token and binding/ref ranges; assign each consumer-node/source-binding pair a unique generated helper alias; join original private references by same-file binding identity; discover generated private kernel names from the actual environment with privateToUserName and OwnModule ownership, never fabricate private prefixes. Check complete provider import closures, keep public node types unchanged, and perform exact-text compilation within 300 seconds plus source/generated kernel type, helper-map, dependency and standard-axiom validation. Accepted nodes and global plans remain unchanged. No Lean or network was used in this audit.

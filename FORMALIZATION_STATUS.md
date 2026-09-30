# Formalization status

Pinned environment:

- Lean `v4.32.2`;
- mathlib tag `v4.32.2`;
- mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`.

The current numbered theorem map is in `README.md` and `Numbered/*.lean`.

## Kernel-checked coverage

### Scalar contract

File: `SharpRadialClipping/Scalar.lean`

- definition of `c_p`, `F`, `K_p`, and `r_star`;
- exact bound `F_le_K_p`;
- denominator-free bound `scalar_numerator_le`;
- equality at the explicit critical radius;
- attainment and smallest-uniform-constant statements;
- agreement of the two closed branch formulas at every nonzero phase-boundary
  point `α = p β`;
- continuous extension by zero of the second closed branch expression at the
  origin, relative to its natural nonnegative second-regime cone;
- divergence of the normalized energy objective as `r ↓ 0` when `β > 0` and
  `p > 2`, proving the necessity of the exponent restriction;
- all maximizing-radius cases:
  - every positive radius for zero weights;
  - unique radius `1` in the nonzero first regime when `1 < p < 2`;
  - exactly `0 < r ≤ 1` in the nonzero first regime when `p = 2`;
  - unique radius `r_star` in the second regime.

### Deterministic contract

Files: `SharpRadialClipping/Deterministic.lean`, `SharpRadialClipping/DeterministicP1.lean`

- radial clipping on arbitrary real normed spaces;
- exact formulas for the clipped norm and residual norm;
- the deterministic bias--energy envelope;
- an explicit nonzero equality witness in every nontrivial normed space;
- minimality of `K_p` among vector-valued uniform constants.
- the separate article Theorem 2.2 at `p = 1`: the optimal constant is
  `K_p α β 1 = max α β`, including both the pointwise inequality and
  smallest-constant statement in a nontrivial normed space.

### Measure-theoretic and stochastic upper bounds

Files: `SharpRadialClipping/ClippingMeasure.lean`, `SharpRadialClipping/Integration.lean`,
`SharpRadialClipping/Stochastic.lean`

- continuity and a.e. strong measurability of radial clipping;
- integrability of the clipped vector and its squared norm on finite measure
  spaces;
- integration of the pointwise envelope with explicit measurability, so the
  proof does not rely on the totalized value of a nonmeasurable Bochner
  integral;
- the Hilbert variance identity;
- the full unconditional stochastic envelope under the sole moment
  hypothesis `X ∈ L^p`.

### Conditional envelope

Files: `SharpRadialClipping/ConditionalL2.lean`, `SharpRadialClipping/ConditionalExtended.lean`

- the conditional Hilbert variance identity for `Y ∈ L²`;
- the conditional Sharp Radial Clipping envelope for a deterministic clipping threshold,
  with all integrability hypotheses discharged from `X ∈ L^p`;
- the random `𝒢`-measurable-threshold version at the global-`L²` level,
  under explicit weighted-integrability hypotheses;
- the canonical extended conditional variance `condVarENN`, defined through
  `condLExp`, and its real representative `condVarReal`;
- compatibility of `condLExp` with restriction to a
  conditioning-measurable set and the local bridge from `condLExp.toReal` to
  ordinary Bochner conditional expectation;
- the extended conditional Hilbert variance inequality assuming only
  `Y ∈ L¹`, with no global second-moment or finite-measure hypothesis;
- measurable threshold bands
  `1 / (n + 1) ≤ τ ≤ n + 1`, their a.e. covering property when `τ > 0`
  a.e., and automatic local `L²` and weighted integrability on every band;
- the fully localized random-threshold conditional Sharp Radial Clipping theorem from exactly
  `X ∈ L^p`, `1 < p ≤ 2`, deterministic nonnegative weights, and a positive
  strongly `𝒢`-measurable threshold, without any global `L²` or weighted
  integrability assumptions;
- a proof that the extended conditional variance is finite almost everywhere;
- both the paper-facing real-valued inequality and a simultaneous
  extended-nonnegative-valued formulation.

### Sharpness and one-parameter corollaries

Files: `SharpRadialClipping/Sharpness.lean`, `SharpRadialClipping/Corollaries.lean`

- exact centered symmetric two-point attainment in the first regime;
- exact formulas for the actual centered rare Bernoulli construction in the
  second regime: its mean, clipped mean, variance, `p`-moment, and normalized
  objective;
- identification of the normalized rare-law objective with the reduced scalar
  ratio and its convergence to `K_p` at the critical radius;
- epsilon-optimality of actual centered two-point laws in the second regime;
- the normalized upper bound for every admissible `L^p` random vector;
- minimality of `K_p`: every constant which bounds all centered laws must
  already bound the explicit probability laws on the two-point space `Bool`,
  and hence is at least `K_p`;
- a literal `sSup` theorem showing that the admissible centered two-point laws
  have supremum exactly `K_p` (and therefore already determine the global
  constant);
- strict nonattainment of `K_p` by every nonzero centered admissible law in
  the second regime;
- the one-parameter deterministic envelope;
- the explicit phase split for `κ_p` and its `p = 2` specialization.

### Support-function radius geometry

File: `SharpRadialClipping/Geometry.lean`

- every nonzero nonnegative support direction has a maximizing radius in
  `[1, p / (p - 1)]`;
- every radius on that arc maximizes the zero direction;
- elimination of the radius gives the stated curve
  `Bias = Energy ^ ((p - 1) / p) - Energy`;
- the exact support-function statement: in every nonzero nonnegative
  direction, `K_p` is the greatest linear value on the limiting rare-shock
  curve;
- every continuation point with `r > p / (p - 1)` is strictly dominated in
  both limiting bias and energy coordinates by the endpoint of the exposed
  arc.

### Closure of the attainable set

File: `SharpRadialClipping/Attainable.lean`

- every finite rare-law pair is realized by an actual centered two-point law
  on `Bool`;
- these finite-law pairs converge to the limiting rare-shock point;
- the radius-one endpoint is attained by the symmetric two-point law;
- the entire rare-shock curve for `r ≥ 1` is contained in the topological
  closure of the actual centered two-point attainable set.

### Intermediate exact `1 < p ≤ 2` attainable-set lemmas

Files: `SharpRadialClipping/AttainableExact.lean`, `SharpRadialClipping/Sharpness.lean`

- the one-nonzero-atom Bernoulli law has its exact normalized pair for every
  real exponent `p > 1`;
- every point strictly left of a parameterized rare-shock boundary point is
  realized by such a two-atom law;
- the open curved boundary arc, excluding its junction with the flat part and
  the attained `(1,0)` endpoint, is proved unattainable via a tangent support
  direction and strictness of the stochastic envelope for positive energy
  weight. The junction and full set equality are covered in the later
  `Article41` module.

### Exact `p = 1` attainable set and signed support

Files: `SharpRadialClipping/RandomLaw.lean`, `SharpRadialClipping/AttainableP1.lean`,
`SharpRadialClipping/SignedSupportP1.lean`

- a universe-polymorphic interface for arbitrary probability laws with a
  finite positive norm moment;
- the exact `p = 1` attainable region: the closed unit triangle in
  energy--bias coordinates with only `(0,1)` excluded;
- explicit two-atom realizations of every strict-interior point and every
  attainable point on the sloping boundary;
- the signed support formula `max {0, α, β}` at `p = 1`, including the fact
  that excluding `(0,1)` does not change the supremum.

### Signed support for `1 < p ≤ 2`

File: `SharpRadialClipping/SignedSupport.lean`

- the four-branch signed support formula over the full set of admissible
  Hilbert-valued laws, not merely over the limiting rare-shock curve;
- a universal upper bound for all admissible laws;
- exact witnesses for the linear branches and an epsilon-optimal rare-law
  construction for the nonlinear branch;
- a single `IsLUB` theorem combining all four cases.

### Article Theorem 4.1 and related results

Files: `SharpRadialClipping/RareBoundaryInverse.lean`, `SharpRadialClipping/AttainableClassification.lean`,
`SharpRadialClipping/ConvexHullExact.lean`, `SharpRadialClipping/Article41.lean`, `SharpRadialClipping/PointwiseArc.lean`,
`SharpRadialClipping/TwoAtom.lean`

- the exact attainable set for arbitrary nontrivial real Hilbert spaces and
  every `1 < p ≤ 2`, first in radius-parametric form;
- the closed convex hull as the intersection of all signed-support
  half-spaces;
- the same closed convex hull as the explicit region below the article's
  piecewise upper boundary `F_p`;
- the curved excluded arc both in radius-parametric form and in the
  article's explicit energy coordinate;
- the literal Theorem 4.1 equality: attainable set equals its closed convex
  hull (equivalently, the explicit piecewise `F_p` region) minus precisely
  that arc, including the left endpoint and excluding `(1, 0)`;
- the article's pointwise arc lemma and equality cases;
- one-dimensional two-atom realization of every attainable pair, including
  the `p = 1` case (Corollary 4.4).

### The `p = 1` stochastic and conditional envelope

Files: `SharpRadialClipping/StochasticConditionalP1.lean`,
`SharpRadialClipping/StochasticSharpP1.lean`

- Theorem 3.1 at `p = 1`;
- Proposition 3.2 at `p = 1`: the supremum over actual nonzero stochastic
  laws is `K_p α β 1 = max α β`;
- the full variable-threshold conditional Corollary 3.3 at `p = 1`.

### Theorem 4.5: simultaneous three-dimensional realization

Files: `SharpRadialClipping/AllThresholds.lean`, `SharpRadialClipping/AllThresholdsGeometry.lean`,
`SharpRadialClipping/AllThresholdsFold.lean`, `SharpRadialClipping/AllThresholdsLongitudinal.lean`,
`SharpRadialClipping/AllThresholdsQuantization.lean`, `SharpRadialClipping/AllThresholdsApprox.lean`,
`SharpRadialClipping/AllThresholdsLimit.lean`, `SharpRadialClipping/AllThresholdsAssembly.lean`,
`SharpRadialClipping/AllThresholdsFiniteShell.lean`, `SharpRadialClipping/AllThresholdsFinitePath.lean`,
`SharpRadialClipping/AllThresholdsPushforward.lean`, `SharpRadialClipping/AllThresholdsFiniteLaw.lean`,
`SharpRadialClipping/AllThresholdsHinge.lean`, `SharpRadialClipping/AllThresholdsFiniteAssembly.lean`,
`SharpRadialClipping/AllThresholdsFinalPrep.lean`

- radial-shell residual identities and interpolation of distances along a
  segment;
- placement of the initial two-vector triangle in `ℝ³` with all three side
  lengths preserved, and preservation of every linear combination of those
  two vectors;
- orthogonal folding of a new vertex, conditional on a compatible longitudinal
  component, preserving distances to anchors while not increasing the jump;
- explicit rank-one and rank-two longitudinal constructions from the three
  anchor distances, plus transport of the previous vertex's transverse norm
  and longitudinal distance under matched anchor data;
- the complete one-step extension lemma
  `exists_next_vertex_three_space_with_no_larger_jump`, including degenerate
  anchor configurations: three next-vertex distances are preserved while
  the weighted adjacent-slope jump does not increase;
- finite-range downward quantization of the source radius, including its
  pointwise error estimate and `L¹` convergence for an integrable random
  vector; convergence of the original and clipped means, clipping bias,
  clipped second moment, and centered clipped energy;
- signed-atom construction, conditional on the finite-radius geometric
  coefficients, preserving the radial law and both clipping quantities for
  every threshold;
- finite radial-shell partition of the source integral, exact atomic radial
  test formula, total shell mass, shell-coefficient norm bound, and
  finite piecewise-linear residual-mean formula;
- one simultaneously constructed three-dimensional sequence of residual-path
  vertices, preserving all vertex/anchor/edge distances and all weighted
  adjacent-slope jump bounds; the same holds for both distances at every
  point in the interior of each line segment;
- spatial push-forward of the finite signed-atom random vector preserves its
  radial distribution, clipping bias, and centered energy; the conditional
  theorem `exists_spatial_signedAtom_law_of_geometry` now produces a law on
  `ℝ³` directly from a finite coefficient family with the required geometric
  equalities;
- the finite shell masses and a geometrically valid coefficient family now
  produce an actual three-dimensional probability law in
  `exists_spatial_law_of_finite_shell_geometry`;
- algebraic reconstruction of a finite hinge path from its slope jumps,
  interval-wise matching of the two required distances, and the coefficient
  norm bound after folding are proved in `AllThresholdsHinge`;
- `AllThresholdsFiniteAssembly` orders every positive radial shell, identifies
  its coefficient as the corresponding slope jump, constructs folded
  coefficients with no larger norms, and proves the unconditional finite-radius
  realization theorem `exists_spatial_law_of_finite_radius_source`;
- tightness and a Prokhorov weak-subsequence theorem under a common radial
  tail bound;
- preservation of the radial law under weak convergence;
- convergence of clipped means, untruncated means under uniform radial-tail
  control, clipping bias, and centered clipped energy;
- passage of the two clipping equalities from finite approximations to a weak
  limit, conditional on convergence of the source-side approximations.
- a single proved conditional assembly theorem:
  `exists_all_thresholds_realization_of_quantized_realizations` derives the
  all-threshold three-dimensional law from finite realizations of every
  radial quantization; radial tightness, Prokhorov extraction, integrability,
  radial-law identification, mean convergence, bias convergence, and energy
  convergence are all discharged inside its proof.
- `exists_all_thresholds_realization_from_finite_radius` reduces the full
  theorem to one finite-radius realization theorem and discharges the
  quantization-to-limit application under that explicit hypothesis.
- `exists_all_thresholds_three_dimensional_realization` applies the proved
  finite-radius theorem to every quantization and concludes the full
  all-threshold statement for one law on `ℝ³`.

The final theorem has no finite-support or geometric assumption. Its sole
source hypotheses are measurability and integrability of the Hilbert-valued
random vector.

### Section 5 applications

- `SharpRadialClipping/ApplicationTradingHelpers.lean` and `SharpRadialClipping/ApplicationTrading.lean`
  prove the complete Corollary 5.2 trading regret inequality for arbitrary
  positive returns and every constant comparison weight in `[0,1]`. The proof
  includes positive wealth, the logarithmic tangent inequality, projection
  contraction, the deterministic `K_2` envelope, and the telescoping sum.
- `SharpRadialClipping/ApplicationReinsuranceFull.lean` proves the complete Corollary 5.1
  `reinsuranceRiskCost_le_of_iid` from an integer-valued count with finite
  second moment, nonnegative IID `L²` losses, and independence of the count
  from the entire loss sequence. The final `K_2` cost bound is no longer
  conditional on separately assumed random-sum identities.
- `SharpRadialClipping/ApplicationRandomSum.lean`, `ApplicationRandomSumVariance.lean`,
  `ApplicationRandomSumLimit.lean`, and `ApplicationRandomSumFull.lean` derive
  the random-sum mean and variance identities, first for bounded counts and
  then for unbounded counts by dominated convergence. The IID and clipping
  bridge is in `ApplicationReinsuranceIID.lean`.

## Current audit state

- root `lake build SharpRadialClipping`: passing (`3609` jobs, rechecked 2026-09-30);
- occurrences of `sorry` or `admit`: zero;
- user-declared axioms: zero;
- scalar core independently reconstructed and compiled by a separate audit
  agent;
- the measure-theoretic rare-law construction independently reconstructed and
  compiled by a separate audit agent;
- the arbitrary-space nonattainment theorem independently developed, compiled
  twice in isolation, integrated, and rebuilt as part of the root module;
- the localization lemmas, the extended conditional variance inequality, and
  the final full conditional theorem were independently developed in separate
  audit files before integration;
- the integrated conditional module and root module were rebuilt independently
  after integration;
- a separate final read-only audit matched both full conditional theorem
  signatures against the then-current specification, checked the localization
  chain for circularity and safe use of totalized conditional expectation,
  and independently repeated the build and axiom inspection;
- an independent line-by-line theorem-specification audit found no circular
  dependence in the unconditional deterministic or stochastic proof chain;
- inspected axioms of the scalar limit theorems, exact stochastic supremum,
  strict nonattainment, support geometry, global-`L²` conditional theorem,
  attainable-set closure theorem, extended variance theorem, and both full
  localized conditional theorems are only the standard mathlib foundations
  `propext`, `Classical.choice`, and `Quot.sound`.
- supplemental audit on 2026-09-29: the new exact `p = 1` attainable-set
  classification and both signed-support `IsLUB` theorems also depend only on
  `propext`, `Classical.choice`, and `Quot.sound`; their modules build without
  `sorry` or `admit`.
- axiom audit on 2026-09-29: the final Theorem 2.2 smallest-constant statement,
  the geometric Theorem 4.1 set-difference statement, and the exact
  closed-hull/support-intersection theorem depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- the final explicit `F_p` version of Theorem 4.1 and the `p = 1` stochastic
  supremum (Proposition 3.2) have the same axiom profile.
- `#print axioms exists_all_thresholds_three_dimensional_realization` reports
  only `propext`, `Classical.choice`, and `Quot.sound`; the completed Theorem 4.5
  modules contain no `sorry`, `admit`, or new axioms.
- the Corollary 5.2 theorem `trading_regret_bound` and the full
  Corollary 5.1 theorem `reinsuranceRiskCost_le_of_iid` also report only
  these three standard axioms.
- the bounded-count mean and off-diagonal-moment theorems in
  `ApplicationRandomSum.lean` have the same axiom profile.

## Scope boundary

- Theorem 4.1, including the flat/curved junction and equivalence with the
  closed-convex-hull description, is kernel-checked. The separate `p = 1`
  region is fully classified in `SharpRadialClipping/AttainableP1.lean`.
- Theorem 4.5, the simultaneous three-dimensional construction for every
  clipping threshold, is kernel-checked in
  `SharpRadialClipping/AllThresholdsFinalPrep.lean`.
- Corollaries 5.1 and 5.2 are fully kernel-checked under their stated model
  assumptions.
- The Whitehouse, anchored-minibatch, FTRL, and gross-exposure applications
  are not formalized in Lean.  They rely on the kernel-checked envelope but
  require their own mathematical and source audits.

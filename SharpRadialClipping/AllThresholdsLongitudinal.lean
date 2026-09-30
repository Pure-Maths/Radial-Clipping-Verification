import SharpRadialClipping.AllThresholdsFold

/-!
# Longitudinal placement in the all-thresholds folding step

The anchor line/plane carries the longitudinal component of the new vertex.
The lemmas here construct that component from the matched anchor distances.
-/

noncomputable section

/-- A point's longitudinal part along a nonzero anchor vector can be
transported to another vector of the same length.  The residual is
orthogonal to the anchor; hence the two anchored radii of the longitudinal
part agree in the source and target. -/
theorem exists_longitudinal_on_matched_anchor_line
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a x : H) (a' : E) (ha : a ≠ 0) (haNorm : ‖a'‖ = ‖a‖) :
    ∃ y : H, ∃ y' : E, ∃ v : H,
      x = y + v ∧
      y ∈ Submodule.span ℝ {a} ∧ y' ∈ Submodule.span ℝ {a'} ∧
      inner ℝ a v = 0 ∧
      ‖y‖ = ‖y'‖ ∧ ‖y - a‖ = ‖y' - a'‖ := by
  let c : ℝ := inner ℝ a x / ‖a‖ ^ 2
  let y : H := c • a
  let y' : E := c • a'
  let v : H := x - y
  refine ⟨y, y', v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [v]; abel
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a'))
  · have hAnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    dsimp [v, y, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  · dsimp [y, y']
    rw [norm_smul, norm_smul, haNorm]
  · have hsource : y - a = (c - 1) • a := by
      dsimp [y]
      rw [sub_smul, one_smul]
    have htarget : y' - a' = (c - 1) • a' := by
      dsimp [y']
      rw [sub_smul, one_smul]
    rw [hsource, htarget]
    rw [norm_smul, norm_smul, haNorm]

/-- Three pairwise distances transport a linear relation between two
anchor vectors. In particular, a collinear third anchor has the same
coordinate on the target anchor line. -/
theorem smul_relation_of_three_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : H) (a' b' : E) (t : ℝ)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (hline : b = t • a) : b' = t • a' := by
  have hinner : inner ℝ a b = inner ℝ a' b' := by
    simpa using inner_eq_of_three_distances a b 0 a' b' 0
      (by simpa using ha) (by simpa using hb) hab
  have hinner' : inner ℝ b' a' = inner ℝ b a := by
    calc
      inner ℝ b' a' = inner ℝ a' b' := real_inner_comm _ _
      _ = inner ℝ a b := hinner.symm
      _ = inner ℝ b a := real_inner_comm _ _
  have hsq : ‖b' - t • a'‖ ^ 2 = ‖b - t • a‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, ha, hb]
    rw [hinner']
  rw [hline, sub_self, norm_zero, zero_pow (by norm_num)] at hsq
  have hz : ‖b' - t • a'‖ = 0 := by
    nlinarith [norm_nonneg (b' - t • a')]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Once two points and the origin form congruent triangles, distance to
every point of the line through the origin and one anchor is also matched. -/
theorem norm_sub_smul_of_three_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a y : H) (a' y' : E) (t : ℝ)
    (ha : ‖a‖ = ‖a'‖) (hy : ‖y‖ = ‖y'‖)
    (hya : ‖y - a‖ = ‖y' - a'‖) :
    ‖y - t • a‖ = ‖y' - t • a'‖ := by
  have h := norm_affineCombination_sub_eq_of_three_distances
    (A := (0 : H)) (B := a) (C := y)
    (A' := (0 : E)) (B' := a') (C' := y') t
    (by simpa [norm_neg] using hy)
    (by simpa [norm_sub_rev] using hya)
    (by simpa [norm_neg] using ha)
  simpa [norm_sub_rev] using h

/-- The entire rank-one longitudinal placement for the anchor triple
`0,a,b`.  Pairwise distance data force the same affine coordinate for
`b` and `b'`; the new point's projection therefore preserves all three
anchor distances, and its residual is orthogonal to the anchor line. -/
theorem exists_longitudinal_for_collinear_anchor_triple
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b x : H) (a' b' : E) (t : ℝ)
    (haNonzero : a ≠ 0)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (hline : b = t • a) :
    ∃ y : H, ∃ y' : E, ∃ v : H,
      x = y + v ∧
      y ∈ Submodule.span ℝ {a} ∧
      y' ∈ Submodule.span ℝ {a'} ∧
      ‖y‖ = ‖y'‖ ∧ ‖y - a‖ = ‖y' - a'‖ ∧
      ‖y - b‖ = ‖y' - b'‖ ∧
      inner ℝ y v = 0 ∧
      inner ℝ (y - a) v = 0 ∧
      inner ℝ (y - b) v = 0 := by
  have hline' : b' = t • a' :=
    smul_relation_of_three_distances a b a' b' t ha hb hab hline
  obtain ⟨y, y', v, hx, hySpan, hy'Span, hav, hyNorm, hyaNorm⟩ :=
    exists_longitudinal_on_matched_anchor_line a x a' haNonzero ha.symm
  have hybNorm : ‖y - b‖ = ‖y' - b'‖ := by
    rw [hline, hline']
    exact norm_sub_smul_of_three_distances a y a' y' t ha hyNorm hyaNorm
  have hyo : inner ℝ y v = 0 := by
    change y ∈ ℝ ∙ a at hySpan
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hySpan
    rw [← hc, real_inner_smul_left, hav, mul_zero]
  have hyao : inner ℝ (y - a) v = 0 := by
    rw [inner_sub_left, hyo, hav, sub_self]
  have hybo : inner ℝ (y - b) v = 0 := by
    rw [inner_sub_left, hyo, hline, real_inner_smul_left, hav]
    simp
  exact ⟨y, y', v, hx, hySpan, hy'Span, hyNorm, hyaNorm, hybNorm,
    hyo, hyao, hybo⟩

/-- Matching the three side lengths of two anchor triangles identifies
their Gram matrices, hence the norm of every common linear combination. -/
theorem norm_two_anchor_linear_combination_of_three_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : H) (a' b' : E) (s t : ℝ)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖) :
    ‖s • a + t • b‖ = ‖s • a' + t • b'‖ := by
  have hinner : inner ℝ a b = inner ℝ a' b' := by
    simpa using inner_eq_of_three_distances a b 0 a' b' 0
      (by simpa using ha) (by simpa using hb) hab
  have hsq : ‖s • a + t • b‖ ^ 2 = ‖s • a' + t • b'‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right, ha, hb, hinner]
  nlinarith [norm_nonneg (s • a + t • b),
    norm_nonneg (s • a' + t • b')]

/-- Explicit Gram-coordinate construction for a nondegenerate anchor
plane.  The determinant hypothesis is exactly the rank-two condition.
The source residual is perpendicular to both anchor directions, while
the transported longitudinal part retains its three anchor radii. -/
theorem exists_longitudinal_for_rank_two_anchor_triple
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b x : H) (a' b' : E)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (hdet : ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 ≠ 0) :
    ∃ y : H, ∃ y' : E, ∃ v : H,
      x = y + v ∧
      y ∈ Submodule.span ℝ {a, b} ∧
      y' ∈ Submodule.span ℝ {a', b'} ∧
      ‖y‖ = ‖y'‖ ∧ ‖y - a‖ = ‖y' - a'‖ ∧
      ‖y - b‖ = ‖y' - b'‖ ∧
      inner ℝ a v = 0 ∧ inner ℝ b v = 0 := by
  let aa : ℝ := ‖a‖ ^ 2
  let bb : ℝ := ‖b‖ ^ 2
  let ab : ℝ := inner ℝ a b
  let d : ℝ := aa * bb - ab ^ 2
  have hd : d ≠ 0 := hdet
  let r : ℝ := inner ℝ a x
  let s : ℝ := inner ℝ b x
  let c : ℝ := (r * bb - s * ab) / d
  let e : ℝ := (s * aa - r * ab) / d
  let y : H := c • a + e • b
  let y' : E := c • a' + e • b'
  let v : H := x - y
  have haa : inner ℝ a a = aa := real_inner_self_eq_norm_sq a
  have hbb : inner ℝ b b = bb := real_inner_self_eq_norm_sq b
  have hba : inner ℝ b a = ab := by
    rw [real_inner_comm]
  have hao : inner ℝ a v = 0 := by
    dsimp [v, y]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, haa]
    change r - (c * aa + e * ab) = 0
    dsimp [c, e]
    field_simp
    dsimp [d]
    ring
  have hbo : inner ℝ b v = 0 := by
    dsimp [v, y]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hba, hbb]
    change s - (c * ab + e * bb) = 0
    dsimp [c, e]
    field_simp
    dsimp [d]
    ring
  have hyNorm : ‖y‖ = ‖y'‖ := by
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' c e ha hb hab
  have hyaNorm : ‖y - a‖ = ‖y' - a'‖ := by
    have hs : y - a = (c - 1) • a + e • b := by
      dsimp [y]; rw [sub_smul, one_smul]; abel
    have ht : y' - a' = (c - 1) • a' + e • b' := by
      dsimp [y']; rw [sub_smul, one_smul]; abel
    rw [hs, ht]
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' (c - 1) e ha hb hab
  have hybNorm : ‖y - b‖ = ‖y' - b'‖ := by
    have hs : y - b = c • a + (e - 1) • b := by
      dsimp [y]; rw [sub_smul, one_smul]; abel
    have ht : y' - b' = c • a' + (e - 1) • b' := by
      dsimp [y']; rw [sub_smul, one_smul]; abel
    rw [hs, ht]
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' c (e - 1) ha hb hab
  refine ⟨y, y', v, ?_, ?_, ?_, hyNorm, hyaNorm, hybNorm, hao, hbo⟩
  · dsimp [v]; abel
  · dsimp [y]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · dsimp [y']
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Non-collinearity of the two nonzero anchor directions is equivalent to
nondegeneracy of the real two-by-two Gram matrix. This discharges the
determinant hypothesis of the rank-two construction. -/
theorem gram_determinant_ne_zero_of_not_collinear
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : H) (ha : a ≠ 0)
    (hnoncol : ¬ ∃ t : ℝ, b = t • a) :
    ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 ≠ 0 := by
  have hb : b ≠ 0 := by
    intro hb
    apply hnoncol
    exact ⟨0, by simp [hb]⟩
  intro hdet
  have hsq : (inner ℝ a b) ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
    nlinarith
  have habs : |inner ℝ a b| = ‖a‖ * ‖b‖ := by
    nlinarith [sq_abs (inner ℝ a b), abs_nonneg (inner ℝ a b),
      norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  have habsNorm : ‖inner ℝ a b‖ = ‖a‖ * ‖b‖ := by
    simpa [Real.norm_eq_abs] using habs
  obtain ⟨t, _, hbt⟩ :=
    (norm_inner_eq_norm_iff (𝕜 := ℝ) ha hb).mp habsNorm
  exact hnoncol ⟨t, hbt⟩

/-- A previously fixed target vertex with the same three anchor radii
has the same transverse length as its source counterpart.  Its transverse
part is orthogonal to both target anchor directions, so it can be used as
the incoming component in the folding lemma. -/
theorem matched_transverse_of_two_anchor_radii
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b x y v : H) (a' b' x' y' : E)
    (hx : x = y + v)
    (hySpan : y ∈ Submodule.span ℝ {a, b})
    (hy'Span : y' ∈ Submodule.span ℝ {a', b'})
    (hav : inner ℝ a v = 0) (hbv : inner ℝ b v = 0)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hxNorm : ‖x‖ = ‖x'‖)
    (hxa : ‖x - a‖ = ‖x' - a'‖)
    (hxb : ‖x - b‖ = ‖x' - b'‖)
    (hyNorm : ‖y‖ = ‖y'‖)
    (hya : ‖y - a‖ = ‖y' - a'‖)
    (hyb : ‖y - b‖ = ‖y' - b'‖) :
    ∃ u' : E, x' = y' + u' ∧
      inner ℝ a' u' = 0 ∧ inner ℝ b' u' = 0 ∧ ‖u'‖ = ‖v‖ := by
  let u' : E := x' - y'
  have hax : inner ℝ a x = inner ℝ a' x' := by
    simpa using inner_eq_of_three_distances a x 0 a' x' 0
      (by simpa using ha) (by simpa using hxNorm) (by simpa [norm_sub_rev] using hxa)
  have hbx : inner ℝ b x = inner ℝ b' x' := by
    simpa using inner_eq_of_three_distances b x 0 b' x' 0
      (by simpa using hb) (by simpa using hxNorm) (by simpa [norm_sub_rev] using hxb)
  have hay : inner ℝ a y = inner ℝ a' y' := by
    simpa using inner_eq_of_three_distances a y 0 a' y' 0
      (by simpa using ha) (by simpa using hyNorm) (by simpa [norm_sub_rev] using hya)
  have hby : inner ℝ b y = inner ℝ b' y' := by
    simpa using inner_eq_of_three_distances b y 0 b' y' 0
      (by simpa using hb) (by simpa using hyNorm) (by simpa [norm_sub_rev] using hyb)
  have haxEq : inner ℝ a x = inner ℝ a y := by
    rw [hx, inner_add_right, hav, add_zero]
  have hbxEq : inner ℝ b x = inner ℝ b y := by
    rw [hx, inner_add_right, hbv, add_zero]
  have hau' : inner ℝ a' u' = 0 := by
    dsimp [u']
    rw [inner_sub_right, ← hax, ← hay, haxEq, sub_self]
  have hbu' : inner ℝ b' u' = 0 := by
    dsimp [u']
    rw [inner_sub_right, ← hbx, ← hby, hbxEq, sub_self]
  have hyvo : inner ℝ y v = 0 := by
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hySpan
    rw [← hcd, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hav, hbv]
    ring
  have hy'u' : inner ℝ y' u' = 0 := by
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hy'Span
    rw [← hcd, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, hau', hbu']
    ring
  have hsquare : ‖u'‖ ^ 2 = ‖v‖ ^ 2 := by
    have hs : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [hx, norm_add_sq_real, hyvo]
      ring
    have ht : ‖x'‖ ^ 2 = ‖y'‖ ^ 2 + ‖u'‖ ^ 2 := by
      have hxu : x' = y' + u' := by dsimp [u']; abel
      rw [hxu, norm_add_sq_real, hy'u']
      ring
    rw [hxNorm, hyNorm] at hs
    linarith
  have hnorm : ‖u'‖ = ‖v‖ := by
    nlinarith [norm_nonneg u', norm_nonneg v]
  exact ⟨u', by dsimp [u']; abel, hau', hbu', hnorm⟩

/-- Inside the span of two anchors, the three distances to `0,a,b`
uniquely determine a point.  No linear-independence assumption is needed:
the statement includes the collinear case. -/
theorem eq_of_same_radii_in_two_anchor_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b y z : E)
    (hy : y ∈ Submodule.span ℝ {a, b})
    (hz : z ∈ Submodule.span ℝ {a, b})
    (h0 : ‖y‖ = ‖z‖)
    (ha : ‖y - a‖ = ‖z - a‖)
    (hb : ‖y - b‖ = ‖z - b‖) : y = z := by
  have hay : inner ℝ a y = inner ℝ a z := by
    simpa using inner_eq_of_three_distances a y 0 a z 0
      (by simp) (by simpa using h0) (by simpa [norm_sub_rev] using ha)
  have hby : inner ℝ b y = inner ℝ b z := by
    simpa using inner_eq_of_three_distances b y 0 b z 0
      (by simp) (by simpa using h0) (by simpa [norm_sub_rev] using hb)
  have hao : inner ℝ a (y - z) = 0 := by
    rw [inner_sub_right, hay, sub_self]
  have hbo : inner ℝ b (y - z) = 0 := by
    rw [inner_sub_right, hby, sub_self]
  obtain ⟨c, d, hcd⟩ :=
    Submodule.mem_span_pair.mp ((Submodule.span ℝ {a, b}).sub_mem hy hz)
  have hself : inner ℝ (y - z) (y - z) = 0 := by
    calc
      inner ℝ (y - z) (y - z) = inner ℝ (c • a + d • b) (y - z) := by rw [hcd]
      _ = 0 := by
        rw [inner_add_left, real_inner_smul_left,
          real_inner_smul_left, hao, hbo]
        ring
  have hnorm : ‖y - z‖ = 0 := by
    have hsq : ‖y - z‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hself
    nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Anchor radii force the target longitudinal point to have exactly
the same two coefficients as its source counterpart. -/
theorem target_longitudinal_eq_common_coefficients
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b y : H) (a' b' y' : E) (c d : ℝ)
    (hy : y = c • a + d • b)
    (hy'Span : y' ∈ Submodule.span ℝ {a', b'})
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (h0 : ‖y‖ = ‖y'‖)
    (hya : ‖y - a‖ = ‖y' - a'‖)
    (hyb : ‖y - b‖ = ‖y' - b'‖) :
    y' = c • a' + d • b' := by
  let z' : E := c • a' + d • b'
  have hz'Span : z' ∈ Submodule.span ℝ {a', b'} := by
    exact Submodule.mem_span_pair.mpr ⟨c, d, rfl⟩
  have hz0 : ‖y'‖ = ‖z'‖ := by
    rw [← h0, hy]
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' c d ha hb hab
  have hza : ‖y' - a'‖ = ‖z' - a'‖ := by
    rw [← hya]
    have hs : y - a = (c - 1) • a + d • b := by
      rw [hy, sub_smul, one_smul]; abel
    have ht : z' - a' = (c - 1) • a' + d • b' := by
      dsimp [z']; rw [sub_smul, one_smul]; abel
    rw [hs, ht]
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' (c - 1) d ha hb hab
  have hzb : ‖y' - b'‖ = ‖z' - b'‖ := by
    rw [← hyb]
    have hs : y - b = c • a + (d - 1) • b := by
      rw [hy, sub_smul, one_smul]; abel
    have ht : z' - b' = c • a' + (d - 1) • b' := by
      dsimp [z']; rw [sub_smul, one_smul]; abel
    rw [hs, ht]
    exact norm_two_anchor_linear_combination_of_three_distances
      a b a' b' c (d - 1) ha hb hab
  exact eq_of_same_radii_in_two_anchor_span a' b' y' z'
    hy'Span hz'Span hz0 hza hzb

/-- Longitudinal distances between *different* vertices are also
preserved by the three anchor radii, provided both points lie in their
respective anchor spans. This is the missing metric invariant for the
longitudinal velocity jump at an interior radius. -/
theorem norm_sub_longitudinal_of_matched_anchor_radii
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b y₁ y₂ : H) (a' b' y₁' y₂' : E)
    (hy₁ : y₁ ∈ Submodule.span ℝ {a, b})
    (hy₂ : y₂ ∈ Submodule.span ℝ {a, b})
    (hy₁' : y₁' ∈ Submodule.span ℝ {a', b'})
    (hy₂' : y₂' ∈ Submodule.span ℝ {a', b'})
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (h₁₀ : ‖y₁‖ = ‖y₁'‖)
    (h₁a : ‖y₁ - a‖ = ‖y₁' - a'‖)
    (h₁b : ‖y₁ - b‖ = ‖y₁' - b'‖)
    (h₂₀ : ‖y₂‖ = ‖y₂'‖)
    (h₂a : ‖y₂ - a‖ = ‖y₂' - a'‖)
    (h₂b : ‖y₂ - b‖ = ‖y₂' - b'‖) :
    ‖y₁ - y₂‖ = ‖y₁' - y₂'‖ := by
  obtain ⟨c₁, d₁, hcd₁⟩ := Submodule.mem_span_pair.mp hy₁
  obtain ⟨c₂, d₂, hcd₂⟩ := Submodule.mem_span_pair.mp hy₂
  have htarget₁ : y₁' = c₁ • a' + d₁ • b' :=
    target_longitudinal_eq_common_coefficients a b y₁ a' b' y₁' c₁ d₁
      hcd₁.symm hy₁' ha hb hab h₁₀ h₁a h₁b
  have htarget₂ : y₂' = c₂ • a' + d₂ • b' :=
    target_longitudinal_eq_common_coefficients a b y₂ a' b' y₂' c₂ d₂
      hcd₂.symm hy₂' ha hb hab h₂₀ h₂a h₂b
  have hs : y₁ - y₂ = (c₁ - c₂) • a + (d₁ - d₂) • b := by
    rw [← hcd₁, ← hcd₂, sub_smul, sub_smul]
    abel
  have ht : y₁' - y₂' = (c₁ - c₂) • a' + (d₁ - d₂) • b' := by
    rw [htarget₁, htarget₂, sub_smul, sub_smul]
    abel
  rw [hs, ht]
  exact norm_two_anchor_linear_combination_of_three_distances
    a b a' b' (c₁ - c₂) (d₁ - d₂) ha hb hab

/-- The norm of a linear combination of three vertices depends only on
their six pairwise distances (including distances to the origin). -/
theorem norm_three_vector_linear_combination_of_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : H) (a' b' c' : E) (s t u : ℝ)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hc : ‖c‖ = ‖c'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (hac : ‖a - c‖ = ‖a' - c'‖)
    (hbc : ‖b - c‖ = ‖b' - c'‖) :
    ‖s • a + t • b + u • c‖ = ‖s • a' + t • b' + u • c'‖ := by
  have hiab : inner ℝ a b = inner ℝ a' b' := by
    simpa using inner_eq_of_three_distances a b 0 a' b' 0
      (by simpa using ha) (by simpa using hb) hab
  have hiac : inner ℝ a c = inner ℝ a' c' := by
    simpa using inner_eq_of_three_distances a c 0 a' c' 0
      (by simpa using ha) (by simpa using hc) hac
  have hibc : inner ℝ b c = inner ℝ b' c' := by
    simpa using inner_eq_of_three_distances b c 0 b' c' 0
      (by simpa using hb) (by simpa using hc) hbc
  have hs : ‖s • a + t • b‖ ^ 2 = ‖s • a' + t • b'‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right, ha, hb, hiab]
  have hsq : ‖s • a + t • b + u • c‖ ^ 2 =
      ‖s • a' + t • b' + u • c'‖ ^ 2 := by
    rw [norm_add_sq_real (s • a + t • b) (u • c),
      norm_add_sq_real (s • a' + t • b') (u • c')]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_add_left, real_inner_smul_left, real_inner_smul_right,
      hc, hiac, hibc, hs]
  nlinarith [norm_nonneg (s • a + t • b + u • c),
    norm_nonneg (s • a' + t • b' + u • c')]

/-- The longitudinal part of an adjacent-slope jump has the same length
after placement in three-space.  This works for arbitrary (nonzero or zero)
real reciprocal step coefficients; positivity is only needed later when
interpreting them as radii differences. -/
theorem norm_longitudinal_slope_jump_of_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (prev cur next : H) (prev' cur' next' : E) (s t : ℝ)
    (hprev : ‖prev‖ = ‖prev'‖)
    (hcur : ‖cur‖ = ‖cur'‖)
    (hnext : ‖next‖ = ‖next'‖)
    (hpc : ‖prev - cur‖ = ‖prev' - cur'‖)
    (hcn : ‖cur - next‖ = ‖cur' - next'‖)
    (hpn : ‖prev - next‖ = ‖prev' - next'‖) :
    ‖s • (cur - prev) - t • (next - cur)‖ =
      ‖s • (cur' - prev') - t • (next' - cur')‖ := by
  have hs : s • (cur - prev) - t • (next - cur) =
      (-s) • prev + (-t) • next + (s + t) • cur := by module
  have ht : s • (cur' - prev') - t • (next' - cur') =
      (-s) • prev' + (-t) • next' + (s + t) • cur' := by module
  rw [hs, ht]
  exact norm_three_vector_linear_combination_of_distances
    prev next cur prev' next' cur' (-s) (-t) (s + t)
    hprev hnext hcur hpn hpc (by simpa [norm_sub_rev] using hcn)

/-- Choose a future transverse displacement opposite to the previously
fixed one.  Positive step weights are incorporated in the comparison, so
the result can be used directly for adjacent derivative jumps. -/
theorem exists_weighted_opposite_transverse
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Submodule ℝ E) [Nontrivial N]
    (prev next : H) (prev' : E) (hprev' : prev' ∈ N)
    (hprevNorm : ‖prev'‖ = ‖prev‖)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ∃ next' : E, next' ∈ N ∧ ‖next'‖ = ‖next‖ ∧
      ‖s • prev' + t • next'‖ ≤ ‖s • prev + t • next‖ := by
  let U' : E := -(s • prev')
  have hU'N : U' ∈ N := N.neg_mem (N.smul_mem s hprev')
  obtain ⟨V', hV'N, hV'Norm, hV'Dist⟩ :=
    exists_aligned_in_submodule N U' hU'N
      (r := t * ‖next‖) (mul_nonneg ht.le (norm_nonneg next))
  let next' : E := t⁻¹ • V'
  have hnext'N : next' ∈ N := N.smul_mem _ hV'N
  have hnext'Norm : ‖next'‖ = ‖next‖ := by
    dsimp [next']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), hV'Norm]
    field_simp
  refine ⟨next', hnext'N, hnext'Norm, ?_⟩
  have htNext : t • next' = V' := by
    dsimp [next']
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have htarget : ‖s • prev' + t • next'‖ = |s * ‖prev‖ - t * ‖next‖| := by
    rw [htNext]
    have heq : s • prev' + V' = V' - U' := by dsimp [U']; abel
    rw [heq, norm_sub_rev, hV'Dist]
    simp [U', norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, hprevNorm]
  rw [htarget]
  have hreverse := abs_norm_sub_norm_le (-(s • prev)) (t • next)
  have hsum : -(s • prev) - t • next = -(s • prev + t • next) := by module
  have hnormEq : ‖-(s • prev) - t • next‖ = ‖s • prev + t • next‖ := by
    rw [hsum, norm_neg]
  rw [hnormEq] at hreverse
  simpa only [norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs, abs_of_pos ht] using hreverse

/-- The final Pythagorean comparison: if both longitudinal and
transverse parts are orthogonal, preserving the former length and
contracting the latter contracts the whole jump. -/
theorem norm_jump_le_of_orthogonal_parts
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (long trans : H) (long' trans' : E)
    (hlong : ‖long'‖ = ‖long‖)
    (htrans : ‖trans'‖ ≤ ‖trans‖)
    (ho : inner ℝ long trans = 0)
    (ho' : inner ℝ long' trans' = 0) :
    ‖long' + trans'‖ ≤ ‖long + trans‖ := by
  have hsq : ‖long' + trans'‖ ^ 2 ≤ ‖long + trans‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real, ho, ho', hlong]
    nlinarith [norm_nonneg trans', norm_nonneg trans]
  nlinarith [norm_nonneg (long' + trans'), norm_nonneg (long + trans)]

/-- Uniform longitudinal projection for all ranks of the two-anchor
configuration, including coincident anchors.  The output supplies exactly
the data needed to place the next vertex by a transverse fold. -/
theorem exists_longitudinal_for_any_anchor_triple
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b x : H) (a' b' : E)
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖) :
    ∃ y : H, ∃ y' : E, ∃ v : H,
      x = y + v ∧
      y ∈ Submodule.span ℝ {a, b} ∧
      y' ∈ Submodule.span ℝ {a', b'} ∧
      ‖y‖ = ‖y'‖ ∧ ‖y - a‖ = ‖y' - a'‖ ∧
      ‖y - b‖ = ‖y' - b'‖ ∧
      inner ℝ y v = 0 ∧
      inner ℝ (y - a) v = 0 ∧
      inner ℝ (y - b) v = 0 := by
  by_cases hA : a = 0
  · have hA' : a' = 0 := by
      have : ‖a'‖ = 0 := by simpa [hA] using ha.symm
      exact norm_eq_zero.mp this
    by_cases hB : b = 0
    · have hB' : b' = 0 := by
        have : ‖b'‖ = 0 := by simpa [hB] using hb.symm
        exact norm_eq_zero.mp this
      subst a; subst b; subst a'; subst b'
      refine ⟨0, 0, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    · obtain ⟨y, y', v, hx, hySpan, hy'Span, h0, hbDist, haDist,
        hyo, hbo, hao⟩ :=
        exists_longitudinal_for_collinear_anchor_triple b a x b' a' 0
          hB hb ha (by simpa [norm_sub_rev] using hab)
          (by simp [hA])
      refine ⟨y, y', v, hx, ?_, ?_, h0, haDist, hbDist,
        hyo, hao, hbo⟩
      · exact (Submodule.span_mono (by simp : ({b} : Set H) ⊆ {a, b})) hySpan
      · exact (Submodule.span_mono (by simp : ({b'} : Set E) ⊆ {a', b'})) hy'Span
  · by_cases hLine : ∃ t : ℝ, b = t • a
    · obtain ⟨t, ht⟩ := hLine
      obtain ⟨y, y', v, hx, hySpan, hy'Span, h0, haDist, hbDist,
        hyo, hao, hbo⟩ :=
        exists_longitudinal_for_collinear_anchor_triple a b x a' b' t
          hA ha hb hab ht
      refine ⟨y, y', v, hx, ?_, ?_, h0, haDist, hbDist,
        hyo, hao, hbo⟩
      · exact (Submodule.span_mono (by simp : ({a} : Set H) ⊆ {a, b})) hySpan
      · exact (Submodule.span_mono (by simp : ({a'} : Set E) ⊆ {a', b'})) hy'Span
    · have hdet := gram_determinant_ne_zero_of_not_collinear a b hA hLine
      obtain ⟨y, y', v, hx, hySpan, hy'Span, h0, haDist,
        hbDist, hao, hbo⟩ :=
        exists_longitudinal_for_rank_two_anchor_triple a b x a' b'
          ha hb hab hdet
      have hyo : inner ℝ y v = 0 := by
        obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hySpan
        rw [← hcd, inner_add_left, real_inner_smul_left,
          real_inner_smul_left, hao, hbo]
        ring
      have hyao : inner ℝ (y - a) v = 0 := by
        rw [inner_sub_left, hyo, hao, sub_self]
      have hybo : inner ℝ (y - b) v = 0 := by
        rw [inner_sub_left, hyo, hbo, sub_self]
      exact ⟨y, y', v, hx, hySpan, hy'Span, h0, haDist,
        hbDist, hyo, hyao, hybo⟩

/-- Orthogonality to two generators is orthogonality to their span. -/
theorem inner_zero_of_mem_two_anchor_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b z w : E)
    (hw : w ∈ Submodule.span ℝ {a, b})
    (ha : inner ℝ a z = 0) (hb : inner ℝ b z = 0) :
    inner ℝ w z = 0 := by
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hw
  rw [← hcd, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, ha, hb]
  ring

/-- A vector orthogonal to both anchor generators belongs to the
orthogonal complement of their span. -/
theorem mem_orthogonal_two_anchor_span_of_inner_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b z : E)
    (ha : inner ℝ a z = 0) (hb : inner ℝ b z = 0) :
    z ∈ (Submodule.span ℝ {a, b})ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  exact inner_zero_of_mem_two_anchor_span a b z w hw ha hb

/-- The span of two anchor directions in three-space leaves a nontrivial
normal direction, regardless of whether the anchors coincide. -/
theorem orthogonal_two_anchor_span_nontrivial
    (a b : EuclideanSpace ℝ (Fin 3)) :
    Nontrivial (Submodule.span ℝ {a, b})ᗮ := by
  classical
  apply orthogonal_complement_nontrivial_of_finrank_le_two
  have hcard : ({a, b} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card ≤ 2 := by
    simpa using (Finset.card_le_two (a := a) (b := b))
  exact (finrank_span_le_card ({a, b} : Set (EuclideanSpace ℝ (Fin 3)))).trans hcard

/-- Complete finite one-step folding lemma.  The previous target vertex
is already fixed.  The new target vertex retains the distances to the
origin and both fixed anchors, and its adjacent weighted-slope jump does
not exceed the source jump.  The proof covers anchor ranks zero, one,
and two without changing the target three-space. -/
theorem exists_next_vertex_three_space_with_no_larger_jump
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b prev next : H)
    (a' b' prev' : EuclideanSpace ℝ (Fin 3))
    (ha : ‖a‖ = ‖a'‖) (hb : ‖b‖ = ‖b'‖)
    (hab : ‖a - b‖ = ‖a' - b'‖)
    (hprev0 : ‖prev‖ = ‖prev'‖)
    (hpreva : ‖prev - a‖ = ‖prev' - a'‖)
    (hprevb : ‖prev - b‖ = ‖prev' - b'‖)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ∃ next' : EuclideanSpace ℝ (Fin 3),
      ‖next‖ = ‖next'‖ ∧
      ‖next - a‖ = ‖next' - a'‖ ∧
      ‖next - b‖ = ‖next' - b'‖ ∧
      ‖s • (b' - prev') - t • (next' - b')‖ ≤
        ‖s • (b - prev) - t • (next - b)‖ := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ {a', b'}
  letI : Nontrivial Kᗮ := orthogonal_two_anchor_span_nontrivial a' b'
  obtain ⟨yp, yp', vp, hprevSource, hypSpan, hyp'Span,
    hyp0, hypa, hypb, hypOrth0, hypOrtha, hypOrthb⟩ :=
    exists_longitudinal_for_any_anchor_triple a b prev a' b' ha hb hab
  obtain ⟨yn, yn', vn, hnextSource, hynSpan, hyn'Span,
    hyn0, hyna, hynb, hynOrth0, hynOrtha, hynOrthb⟩ :=
    exists_longitudinal_for_any_anchor_triple a b next a' b' ha hb hab
  have hpA : inner ℝ a vp = 0 := by
    have h := hypOrtha
    rw [inner_sub_left, hypOrth0] at h
    linarith
  have hpB : inner ℝ b vp = 0 := by
    have h := hypOrthb
    rw [inner_sub_left, hypOrth0] at h
    linarith
  obtain ⟨up', hprevTarget, huA, huB, huNorm⟩ :=
    matched_transverse_of_two_anchor_radii a b prev yp vp a' b' prev' yp'
      hprevSource hypSpan hyp'Span hpA hpB ha hb
      hprev0 hpreva hprevb hyp0 hypa hypb
  have huK : up' ∈ Kᗮ :=
    mem_orthogonal_two_anchor_span_of_inner_zero a' b' up' huA huB
  obtain ⟨vn', hvnK, hvnNorm, htransBound⟩ :=
    exists_weighted_opposite_transverse Kᗮ vp vn up' huK huNorm hs ht
  let next' : EuclideanSpace ℝ (Fin 3) := yn' + vn'
  have hnext0 : ‖next‖ = ‖next'‖ := by
    rw [hnextSource]
    simpa [next'] using (norm_folded_vertex_sub_anchor yn 0 vn yn' 0 vn'
      (by simpa using hyn0) hvnNorm.symm
      (by simpa using hynOrth0)
      (by simpa using Submodule.inner_right_of_mem_orthogonal hyn'Span hvnK))
  have hnexta : ‖next - a‖ = ‖next' - a'‖ := by
    rw [hnextSource]
    exact norm_folded_vertex_sub_anchor yn a vn yn' a' vn'
      hyna hvnNorm.symm hynOrtha
      (Submodule.inner_right_of_mem_orthogonal (K.sub_mem hyn'Span
        (Submodule.subset_span (by simp))) hvnK)
  have hnextb : ‖next - b‖ = ‖next' - b'‖ := by
    rw [hnextSource]
    exact norm_folded_vertex_sub_anchor yn b vn yn' b' vn'
      hynb hvnNorm.symm hynOrthb
      (Submodule.inner_right_of_mem_orthogonal (K.sub_mem hyn'Span
        (Submodule.subset_span (by simp))) hvnK)
  have hypn : ‖yp - yn‖ = ‖yp' - yn'‖ :=
    norm_sub_longitudinal_of_matched_anchor_radii a b yp yn a' b' yp' yn'
      hypSpan hynSpan hyp'Span hyn'Span ha hb hab
      hyp0 hypa hypb hyn0 hyna hynb
  let long : H := s • (b - yp) - t • (yn - b)
  let long' : EuclideanSpace ℝ (Fin 3) :=
    s • (b' - yp') - t • (yn' - b')
  have hlongNorm : ‖long'‖ = ‖long‖ :=
    (norm_longitudinal_slope_jump_of_distances yp b yn yp' b' yn' s t
      hyp0 hb hyn0 (by simpa [norm_sub_rev] using hypb)
      (by simpa [norm_sub_rev] using hynb) hypn).symm
  let trans : H := -(s • vp + t • vn)
  let trans' : EuclideanSpace ℝ (Fin 3) := -(s • up' + t • vn')
  have htransNorm : ‖trans'‖ ≤ ‖trans‖ := by
    change ‖-(s • up' + t • vn')‖ ≤ ‖-(s • vp + t • vn)‖
    simpa only [norm_neg] using htransBound
  have hnA : inner ℝ a vn = 0 := by
    have h := hynOrtha
    rw [inner_sub_left, hynOrth0] at h
    linarith
  have hnB : inner ℝ b vn = 0 := by
    have h := hynOrthb
    rw [inner_sub_left, hynOrth0] at h
    linarith
  have hlongSpan : long ∈ Submodule.span ℝ {a, b} := by
    dsimp [long]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ ((Submodule.span ℝ {a, b}).sub_mem
        (Submodule.subset_span (by simp)) hypSpan)
    · exact Submodule.smul_mem _ _ ((Submodule.span ℝ {a, b}).sub_mem
        hynSpan (Submodule.subset_span (by simp)))
  have hlong'Span : long' ∈ K := by
    dsimp [long']
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (K.sub_mem
        (Submodule.subset_span (by simp)) hyp'Span)
    · exact Submodule.smul_mem _ _ (K.sub_mem
        hyn'Span (Submodule.subset_span (by simp)))
  have htransA : inner ℝ a trans = 0 := by
    dsimp [trans]
    rw [inner_neg_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hpA, hnA]
    ring
  have htransB : inner ℝ b trans = 0 := by
    dsimp [trans]
    rw [inner_neg_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hpB, hnB]
    ring
  have horth : inner ℝ long trans = 0 :=
    inner_zero_of_mem_two_anchor_span a b trans long hlongSpan htransA htransB
  have htrans'K : trans' ∈ Kᗮ := by
    dsimp [trans']
    exact Kᗮ.neg_mem (Kᗮ.add_mem (Kᗮ.smul_mem s huK)
      (Kᗮ.smul_mem t hvnK))
  have horth' : inner ℝ long' trans' = 0 :=
    Submodule.inner_right_of_mem_orthogonal hlong'Span htrans'K
  have hsourceJump : s • (b - prev) - t • (next - b) = long + trans := by
    rw [hprevSource, hnextSource]
    dsimp [long, trans]
    module
  have htargetJump : s • (b' - prev') - t • (next' - b') = long' + trans' := by
    rw [hprevTarget]
    dsimp [long', trans', next']
    module
  refine ⟨next', hnext0, hnexta, hnextb, ?_⟩
  rw [hsourceJump, htargetJump]
  exact norm_jump_le_of_orthogonal_parts long trans long' trans'
    hlongNorm htransNorm horth horth'

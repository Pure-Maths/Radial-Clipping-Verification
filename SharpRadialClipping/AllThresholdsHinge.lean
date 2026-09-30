import SharpRadialClipping.AllThresholdsFinitePath

/-!
# Reconstructing a finite residual path from its slope jumps

The coefficient at a knot is the difference of the slopes immediately to
its right and left.  A finite sum of positive-part hinge functions then
recovers the whole polygonal path.
-/

noncomputable section

/-- Tail sums of adjacent slope jumps telescope. -/
theorem sum_Ioc_adjacent_slope_jumps
    {E : Type*} [AddCommGroup E] (u : ℕ → E)
    (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ Finset.Ioc k m, (u (i + 1) - u i)) =
      u (m + 1) - u (k + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction d with
  | zero =>
      simp
  | succ d ih =>
      simp only [Nat.add_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.le_add_right k d)]
      rw [ih (Nat.le_add_right k d)]
      abel

/-- Discrete integration by parts for the hinge coefficients.  This form
avoids predecessor indices and therefore works also for the first knot. -/
theorem sum_Ioc_weighted_adjacent_slope_jumps
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (u : ℕ → E)
    (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ Finset.Ioc k m, (r i - r k) • (u (i + 1) - u i)) =
      (r m - r k) • u (m + 1) -
        ∑ i ∈ Finset.Ioc k m, (r i - r (i - 1)) • u i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction d with
  | zero => simp
  | succ d ih =>
      simp only [Nat.add_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.le_add_right k d)]
      rw [Finset.sum_Ioc_succ_top (Nat.le_add_right k d)]
      rw [ih (Nat.le_add_right k d)]
      have hk : k + d + 1 - 1 = k + d := by omega
      rw [hk]
      simp only [smul_sub, sub_smul]
      simp only [Nat.succ_eq_add_one, Nat.add_zero, Nat.add_assoc]
      abel

/-- On an interval between two consecutive knots, exactly the later hinge
terms remain active. -/
theorem sum_hinges_eq_tail_on_knot_interval
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (v : ℕ → E) (hr : StrictMono r)
    (k m : ℕ) (hkm : k ≤ m) (τ : ℝ)
    (hleft : r k ≤ τ) (hright : τ ≤ r (k + 1)) :
    (∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 • v i) =
      ∑ i ∈ Finset.Ioc k m, (r i - τ) • v i := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le k) hkm,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  have hzero : (∑ i ∈ Finset.Ioc 0 k, max (r i - τ) 0 • v i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≤ k := (Finset.mem_Ioc.mp hi).2
    have hri : r i ≤ τ := (hr.monotone hik).trans hleft
    have hmax : max (r i - τ) 0 = 0 := max_eq_right (sub_nonpos.mpr hri)
    simp [hmax]
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : k + 1 ≤ i := Nat.succ_le_iff.mpr (Finset.mem_Ioc.mp hi).1
  have hri : τ ≤ r i := hright.trans (hr.monotone hik)
  rw [max_eq_left (sub_nonneg.mpr hri)]

/-- Summation by parts at an arbitrary threshold, not just at a knot. -/
theorem sum_Ioc_hinge_slope_jumps
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (u : ℕ → E)
    (k m : ℕ) (hkm : k ≤ m) (τ : ℝ) :
    (∑ i ∈ Finset.Ioc k m, (r i - τ) • (u (i + 1) - u i)) =
      (r m - τ) • u (m + 1) -
        ∑ i ∈ Finset.Ioc k m, (r i - r (i - 1)) • u i -
          (r k - τ) • u (k + 1) := by
  calc
    _ = (∑ i ∈ Finset.Ioc k m,
          (r i - r k) • (u (i + 1) - u i)) +
        (r k - τ) • (∑ i ∈ Finset.Ioc k m, (u (i + 1) - u i)) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have h : r i - τ = (r i - r k) + (r k - τ) := by ring
      rw [h, add_smul]
    _ = (r m - r k) • u (m + 1) -
          (∑ i ∈ Finset.Ioc k m, (r i - r (i - 1)) • u i) +
          (r k - τ) • (u (m + 1) - u (k + 1)) := by
      rw [sum_Ioc_weighted_adjacent_slope_jumps r u k m hkm,
        sum_Ioc_adjacent_slope_jumps u k m hkm]
    _ = (r m - τ) • u (m + 1) -
          (∑ i ∈ Finset.Ioc k m, (r i - r (i - 1)) • u i) -
          (r k - τ) • u (k + 1) := by
      have h : r m - τ = (r m - r k) + (r k - τ) := by ring
      rw [h, add_smul, smul_sub]
      abel

/-- Vertex increments telescope over a knot interval. -/
theorem sum_Ioc_backward_differences
    {E : Type*} [AddCommGroup E] (Z : ℕ → E)
    (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ Finset.Ioc k m, (Z i - Z (i - 1))) = Z m - Z k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction d with
  | zero => simp
  | succ d ih =>
      simp only [Nat.add_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.le_add_right k d)]
      rw [ih (Nat.le_add_right k d)]
      have hk : k + d + 1 - 1 = k + d := by omega
      rw [hk]
      abel

/-- If the last vertex is zero, earlier vertices are negative cumulative
segment increments. -/
theorem vertex_eq_negative_tail_segments
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z u : ℕ → E)
    (k m : ℕ) (hkm : k ≤ m) (hterminal : Z m = 0)
    (hsegment : ∀ i ∈ Finset.Ioc k m,
      Z i - Z (i - 1) = (r i - r (i - 1)) • u i) :
    Z k = -(∑ i ∈ Finset.Ioc k m,
      (r i - r (i - 1)) • u i) := by
  have hsum := sum_Ioc_backward_differences Z k m hkm
  have hreplace :
      (∑ i ∈ Finset.Ioc k m, (Z i - Z (i - 1))) =
        ∑ i ∈ Finset.Ioc k m, (r i - r (i - 1)) • u i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsegment i hi
  rw [hreplace] at hsum
  rw [hterminal] at hsum
  simpa only [zero_sub, neg_neg] using congrArg Neg.neg hsum.symm

/-- Exact reconstruction of every point on a polygonal residual path from
the jumps in its slopes. -/
theorem finite_hinge_reconstruction_on_interval
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z u : ℕ → E)
    (hr : StrictMono r) (k m : ℕ) (hkm : k ≤ m)
    (τ : ℝ) (hleft : r k ≤ τ) (hright : τ ≤ r (k + 1))
    (hterminalVertex : Z m = 0) (hterminalSlope : u (m + 1) = 0)
    (hsegments : ∀ i ∈ Finset.Ioc k m,
      Z i - Z (i - 1) = (r i - r (i - 1)) • u i) :
    (∑ i ∈ Finset.Ioc 0 m,
      max (r i - τ) 0 • (u (i + 1) - u i)) =
      Z k + (τ - r k) • u (k + 1) := by
  rw [sum_hinges_eq_tail_on_knot_interval r
    (fun i => u (i + 1) - u i) hr k m hkm τ hleft hright]
  rw [sum_Ioc_hinge_slope_jumps r u k m hkm τ, hterminalSlope]
  simp only [smul_zero, zero_sub]
  have hv := vertex_eq_negative_tail_segments r Z u k m hkm
    hterminalVertex hsegments
  rw [hv]
  have hscalar : τ - r k = -(r k - τ) := by ring
  rw [hscalar, neg_smul]
  abel

/-- Slope of the segment immediately to the left of knot `i`. -/
def finitePathSlope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z : ℕ → E) (i : ℕ) : E :=
  (r i - r (i - 1))⁻¹ • (Z i - Z (i - 1))

theorem finitePathSlope_segment
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z : ℕ → E) (hr : StrictMono r)
    (i : ℕ) (hi : 0 < i) :
    Z i - Z (i - 1) =
      (r i - r (i - 1)) • finitePathSlope r Z i := by
  have hprev : i - 1 < i := by omega
  have hgap : r i - r (i - 1) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hr hprev))
  simp only [finitePathSlope, smul_smul,
    mul_inv_cancel₀ hgap, one_smul]

/-- The line reconstructed by a segment slope is its usual affine
interpolation, with no extra geometric assumptions. -/
theorem affine_eq_vertex_add_slope
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b : E) (δ gap : ℝ) :
    (1 - δ / gap) • a + (δ / gap) • b =
      a + δ • (gap⁻¹ • (b - a)) := by
  simp only [div_eq_mul_inv, smul_smul, smul_sub, sub_smul,
    one_smul]
  abel

/-- Fully instantiated reconstruction for a path whose last two listed
vertices are zero. -/
theorem finite_hinge_reconstruction_for_path
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z : ℕ → E)
    (hr : StrictMono r) (k m : ℕ) (hkm : k ≤ m)
    (τ : ℝ) (hleft : r k ≤ τ) (hright : τ ≤ r (k + 1))
    (hterminal : Z m = 0) (hafter : Z (m + 1) = 0) :
    (∑ i ∈ Finset.Ioc 0 m,
      max (r i - τ) 0 •
        (finitePathSlope r Z (i + 1) - finitePathSlope r Z i)) =
      Z k + (τ - r k) • finitePathSlope r Z (k + 1) := by
  have hterminalSlope : finitePathSlope r Z (m + 1) = 0 := by
    have hpred : m + 1 - 1 = m := by omega
    simp [finitePathSlope, hpred, hterminal, hafter]
  have hsegments : ∀ i ∈ Finset.Ioc k m,
      Z i - Z (i - 1) =
        (r i - r (i - 1)) • finitePathSlope r Z i := by
    intro i hi
    exact finitePathSlope_segment r Z hr i
      (lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_Ioc.mp hi).1)
  exact finite_hinge_reconstruction_on_interval r Z
    (finitePathSlope r Z) hr k m hkm τ hleft hright
    hterminal hterminalSlope hsegments

/-- Matching an affine segment's norm and distance to its initial anchor
matches both corresponding hinge-path quantities at every threshold in that
segment. -/
theorem finite_hinge_norms_match_on_interval
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ → ℝ) (R : ℕ → H) (Z : ℕ → E)
    (hr : StrictMono r) (k m : ℕ) (hkm : k ≤ m)
    (τ : ℝ) (hleft : r k ≤ τ) (hright : τ ≤ r (k + 1))
    (hRterminal : R m = 0) (hRafter : R (m + 1) = 0)
    (hZterminal : Z m = 0) (hZafter : Z (m + 1) = 0)
    (hsegment : ∀ θ : ℝ,
      ‖(1 - θ) • R k + θ • R (k + 1)‖ =
        ‖(1 - θ) • Z k + θ • Z (k + 1)‖ ∧
      ‖(1 - θ) • R k + θ • R (k + 1) - R 0‖ =
        ‖(1 - θ) • Z k + θ • Z (k + 1) - Z 0‖) :
    let FR := ∑ i ∈ Finset.Ioc 0 m,
      max (r i - τ) 0 •
        (finitePathSlope r R (i + 1) - finitePathSlope r R i)
    let FZ := ∑ i ∈ Finset.Ioc 0 m,
      max (r i - τ) 0 •
        (finitePathSlope r Z (i + 1) - finitePathSlope r Z i)
    ‖FR‖ = ‖FZ‖ ∧ ‖FR - R 0‖ = ‖FZ - Z 0‖ := by
  dsimp
  rw [finite_hinge_reconstruction_for_path r R hr k m hkm τ hleft hright
      hRterminal hRafter,
    finite_hinge_reconstruction_for_path r Z hr k m hkm τ hleft hright
      hZterminal hZafter]
  let θ := (τ - r k) / (r (k + 1) - r k)
  have hpred : k + 1 - 1 = k := by omega
  have hRaff : R k + (τ - r k) • finitePathSlope r R (k + 1) =
      (1 - θ) • R k + θ • R (k + 1) := by
    simpa only [θ, finitePathSlope, hpred] using
      (affine_eq_vertex_add_slope (R k) (R (k + 1))
        (τ - r k) (r (k + 1) - r k)).symm
  have hZaff : Z k + (τ - r k) • finitePathSlope r Z (k + 1) =
      (1 - θ) • Z k + θ • Z (k + 1) := by
    simpa only [θ, finitePathSlope, hpred] using
      (affine_eq_vertex_add_slope (Z k) (Z (k + 1))
        (τ - r k) (r (k + 1) - r k)).symm
  rw [hRaff, hZaff]
  exact hsegment θ

/-- The folded-path jump inequality is precisely the pointwise bound for
the new hinge coefficient at a radius. -/
theorem finite_hinge_coefficient_norm_le
    {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ → ℝ) (R : ℕ → H) (Z : ℕ → E) (n : ℕ)
    (hjump :
      ‖(r (n + 1) - r n)⁻¹ • (Z (n + 1) - Z n) -
          (r (n + 2) - r (n + 1))⁻¹ • (Z (n + 2) - Z (n + 1))‖ ≤
        ‖(r (n + 1) - r n)⁻¹ • (R (n + 1) - R n) -
          (r (n + 2) - r (n + 1))⁻¹ • (R (n + 2) - R (n + 1))‖) :
    ‖finitePathSlope r Z (n + 2) - finitePathSlope r Z (n + 1)‖ ≤
      ‖finitePathSlope r R (n + 2) - finitePathSlope r R (n + 1)‖ := by
  have hp1 : n + 1 - 1 = n := by omega
  have hp2 : n + 2 - 1 = n + 1 := by omega
  simpa only [finitePathSlope, hp1, hp2, norm_sub_rev] using hjump

/-- The radius-weighted sum of the hinge coefficients is the initial
vertex: it is the residual path evaluated at threshold zero. -/
theorem finite_hinge_weighted_sum_eq_initial
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (Z : ℕ → E)
    (hr0 : r 0 = 0) (hr : StrictMono r) (m : ℕ)
    (hterminal : Z m = 0) (hafter : Z (m + 1) = 0) :
    (∑ i ∈ Finset.Ioc 0 m,
      r i • (finitePathSlope r Z (i + 1) - finitePathSlope r Z i)) =
      Z 0 := by
  have hzero : r 0 ≤ (0 : ℝ) := by simp [hr0]
  have hnext : (0 : ℝ) ≤ r (0 + 1) := by
    rw [← hr0]
    exact (hr (by omega : 0 < 0 + 1)).le
  have hrec := finite_hinge_reconstruction_for_path r Z hr 0 m
    (Nat.zero_le m) 0 hzero hnext hterminal hafter
  have hsum :
      (∑ i ∈ Finset.Ioc 0 m,
        max (r i - 0) 0 •
          (finitePathSlope r Z (i + 1) - finitePathSlope r Z i)) =
        ∑ i ∈ Finset.Ioc 0 m,
          r i • (finitePathSlope r Z (i + 1) - finitePathSlope r Z i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : 0 < i := (Finset.mem_Ioc.mp hi).1
    have hri : 0 ≤ r i := by
      rw [← hr0]
      exact (hr hi0).le
    simp [max_eq_left hri]
  rw [hsum] at hrec
  simpa [hr0] using hrec

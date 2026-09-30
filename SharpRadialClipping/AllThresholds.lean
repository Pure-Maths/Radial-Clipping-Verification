import SharpRadialClipping.Stochastic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Simultaneous radial-clipping realization: geometric and moment lemmas

The article's simultaneous three-dimensional realization proceeds by preserving
the lengths of the residual-mean path and its distance from the initial mean.
The first lemmas below isolate the Hilbert-space interpolation and moment
identities needed for that construction.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A clipped vector's residual has its original direction, with length
`(‖x‖ - τ)₊`. The zero-vector convention is absorbed by Lean's division. -/
theorem radialClip_residual_direction_formula {τ : ℝ} (hτ : 0 < τ) (x : H) :
    x - radialClip τ x = (max (‖x‖ - τ) 0 / ‖x‖) • x := by
  by_cases hx : ‖x‖ ≤ τ
  · rw [radialClip_of_norm_le hx]
    simp [max_eq_right (sub_nonpos.mpr hx)]
  · have hlt : τ < ‖x‖ := lt_of_not_ge hx
    have hnorm : ‖x‖ ≠ 0 := ne_of_gt (hτ.trans hlt)
    rw [radialClip_of_lt_norm hlt, max_eq_left (sub_nonneg.mpr hlt.le)]
    have hc : (‖x‖ - τ) / ‖x‖ = 1 - τ / ‖x‖ := by
      field_simp
    rw [hc]
    module

/-- On a radial shell of deterministic radius `r`, the mean clipping
residual is a scalar multiple of the original mean, at every threshold. -/
theorem integral_residual_of_ae_constant_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → H)
    {r τ : ℝ} (_hr : 0 < r) (hτ : 0 < τ)
    (hnorm : ∀ᵐ ω ∂μ, ‖X ω‖ = r) :
    (∫ ω, X ω - radialClip τ (X ω) ∂μ) =
      (max (r - τ) 0 / r) • ∫ ω, X ω ∂μ := by
  calc
    (∫ ω, X ω - radialClip τ (X ω) ∂μ) =
        ∫ ω, (max (r - τ) 0 / r) • X ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hnorm] with ω hω
      rw [radialClip_residual_direction_formula hτ, hω]
    _ = (max (r - τ) 0 / r) • ∫ ω, X ω ∂μ := integral_smul _ _

/-- The squared distance of a point on a segment to a fixed anchor is
determined by the two endpoint distances and the segment length. -/
theorem norm_affineCombination_sub_sq (A B C : H) (s : ℝ) :
    ‖(1 - s) • A + s • B - C‖ ^ 2 =
      (1 - s) * ‖A - C‖ ^ 2 + s * ‖B - C‖ ^ 2 -
        s * (1 - s) * ‖B - A‖ ^ 2 := by
  have hv : (1 - s) • A + s • B - C = (1 - s) • (A - C) + s • (B - C) := by
    module
  have hdiff : B - A = (B - C) - (A - C) := by module
  rw [hv, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left, real_inner_smul_right,
    mul_pow, sq_abs]
  rw [hdiff, norm_sub_sq_real (B - C) (A - C)]
  rw [real_inner_comm (B - C) (A - C)]
  ring

/-- Segment distances to a common anchor are preserved when the corresponding
endpoint distances and the two segment lengths agree. -/
theorem norm_affineCombination_sub_eq_of_three_distances
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    (A B C : H) (A' B' C' : H') (s : ℝ)
    (hA : ‖A - C‖ = ‖A' - C'‖)
    (hB : ‖B - C‖ = ‖B' - C'‖)
    (hAB : ‖B - A‖ = ‖B' - A'‖) :
    ‖(1 - s) • A + s • B - C‖ =
      ‖(1 - s) • A' + s • B' - C'‖ := by
  have hsquares :
      ‖(1 - s) • A + s • B - C‖ ^ 2 =
        ‖(1 - s) • A' + s • B' - C'‖ ^ 2 := by
    rw [norm_affineCombination_sub_sq, norm_affineCombination_sub_sq,
      hA, hB, hAB]
  nlinarith [norm_nonneg ((1 - s) • A + s • B - C),
    norm_nonneg ((1 - s) • A' + s • B' - C')]

/-- Three pairwise distances determine the corresponding inner product.
This is the Gram-data invariant used when transporting a residual-path
triangle to three-space before folding the next vertex. -/
theorem inner_eq_of_three_distances
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    (A B C : H) (A' B' C' : H')
    (hA : ‖A - C‖ = ‖A' - C'‖)
    (hB : ‖B - C‖ = ‖B' - C'‖)
    (hAB : ‖A - B‖ = ‖A' - B'‖) :
    inner ℝ (A - C) (B - C) = inner ℝ (A' - C') (B' - C') := by
  have hdiff : (A - C) - (B - C) = A - B := by module
  have hdiff' : (A' - C') - (B' - C') = A' - B' := by module
  have hsource := norm_sub_sq_real (A - C) (B - C)
  have htarget := norm_sub_sq_real (A' - C') (B' - C')
  rw [hdiff] at hsource
  rw [hdiff'] at htarget
  rw [hA, hB, hAB] at hsource
  linarith

/-- The Pythagorean comparison behind the folding step. The old transverse
velocities may point in arbitrary directions; after folding, they are aligned,
so their difference has the smallest norm compatible with their lengths. -/
theorem folded_jump_le
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    (P U V : H) (P' U' V' : H')
    (hP : ‖P'‖ = ‖P‖) (hU : ‖U'‖ = ‖U‖) (hV : ‖V'‖ = ‖V‖)
    (horth : inner ℝ P (U - V) = 0)
    (horth' : inner ℝ P' (U' - V') = 0)
    (halign : ‖U' - V'‖ = |‖U'‖ - ‖V'‖|) :
    ‖P' + (U' - V')‖ ≤ ‖P + (U - V)‖ := by
  have htrans : ‖U' - V'‖ ≤ ‖U - V‖ := by
    rw [halign, hU, hV]
    exact abs_norm_sub_norm_le U V
  have hsquares : ‖P' + (U' - V')‖ ^ 2 ≤ ‖P + (U - V)‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real, horth, horth', hP]
    nlinarith [norm_nonneg (U' - V'), norm_nonneg (U - V)]
  nlinarith [norm_nonneg (P' + (U' - V')), norm_nonneg (P + (U - V))]

/-- Any vector can be matched by another of a prescribed nonnegative length
on the same ray, minimizing their mutual distance. The case of a zero input
uses an arbitrary unit direction. -/
theorem exists_aligned_vector_of_norm [Nontrivial H] (U : H)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ V : H, ‖V‖ = r ∧ ‖U - V‖ = |‖U‖ - r| := by
  by_cases hU : U = 0
  · obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
    refine ⟨r • e, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, he, mul_one]
    · subst U
      rw [zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hr, he, mul_one]
      simp [abs_of_nonneg hr]
  · have hnorm : 0 < ‖U‖ := norm_pos_iff.mpr hU
    let e : H := (‖U‖)⁻¹ • U
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      field_simp
    have hUe : U = ‖U‖ • e := by
      dsimp [e]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    refine ⟨r • e, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, he, mul_one]
    · rw [hUe, ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one,
        norm_smul, Real.norm_eq_abs, abs_of_pos hnorm, he, mul_one]

omit [InnerProductSpace ℝ H] in
/-- When no anchor geometry constrains the new segment, one can choose its
velocity in the target space to minimize the jump relative to the previous
velocity. This is the article's fully coincident-anchor case. -/
theorem exists_next_velocity_with_no_larger_jump
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    [Nontrivial H'] (U V : H) (U' : H') (hU : ‖U'‖ = ‖U‖) :
    ∃ V' : H', ‖V'‖ = ‖V‖ ∧ ‖V' - U'‖ ≤ ‖V - U‖ := by
  obtain ⟨V', hV', hdist⟩ :=
    exists_aligned_vector_of_norm U' (H := H') (r := ‖V‖) (norm_nonneg _)
  refine ⟨V', hV', ?_⟩
  rw [norm_sub_rev, hdist, hU]
  exact abs_norm_sub_norm_le U V |>.trans_eq (norm_sub_rev U V)

/-- A concrete one-step vertex extension when the origin, the initial
residual mean, and the current vertex all coincide. The next vertex keeps its
radius and does not increase the adjacent-slope jump. -/
theorem exists_next_vertex_zero_anchors
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    [Nontrivial H'] (prev next : H) (prev' : H')
    (hprev : ‖prev'‖ = ‖prev‖)
    {a b : ℝ} (_ha : 0 < a) (hb : 0 < b) :
    ∃ next' : H', ‖next'‖ = ‖next‖ ∧
      ‖b⁻¹ • next' - (-(a⁻¹ • prev'))‖ ≤
        ‖b⁻¹ • next - (-(a⁻¹ • prev))‖ := by
  have hleft : ‖-(a⁻¹ • prev')‖ = ‖-(a⁻¹ • prev)‖ := by
    simp only [norm_neg, norm_smul, Real.norm_eq_abs, hprev]
  obtain ⟨V', hV', hjump⟩ :=
    exists_next_velocity_with_no_larger_jump
      (-(a⁻¹ • prev)) (b⁻¹ • next) (-(a⁻¹ • prev')) hleft
  refine ⟨b • V', ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb, hV',
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    field_simp
  · rwa [smul_smul, inv_mul_cancel₀ hb.ne', one_smul]

/-- Every vector in a nontrivial Hilbert space has a unit direction. For the
zero vector, any unit direction works. -/
theorem exists_unit_direction [Nontrivial H] (v : H) :
    ∃ e : H, ‖e‖ = 1 ∧ ‖v‖ • e = v := by
  by_cases hv : v = 0
  · obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
    refine ⟨e, he, ?_⟩
    simp [hv]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨(‖v‖)⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]

/-- At a radius of probability mass `q`, a vector coefficient of norm at most
`q` can be split into two nonnegative signed atom weights. -/
theorem signed_atom_weights (q d : ℝ) (hd : 0 ≤ d) (hqd : d ≤ q) :
    0 ≤ (q + d) / 2 ∧ 0 ≤ (q - d) / 2 ∧
      (q + d) / 2 + (q - d) / 2 = q ∧
      (q + d) / 2 - (q - d) / 2 = d := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> ring

/-- The two signed atoms at radius `r` reproduce the desired vector
coefficient `v`, provided `e` is its unit direction. -/
theorem signed_atoms_reproduce_coefficient
    (q r : ℝ) (v e : H) (he : ‖v‖ • e = v) :
    ((q + ‖v‖) / 2) • (r • e) +
      ((q - ‖v‖) / 2) • (-(r • e)) = r • v := by
  calc
    ((q + ‖v‖) / 2) • (r • e) +
        ((q - ‖v‖) / 2) • (-(r • e)) = r • (‖v‖ • e) := by module
    _ = r • v := by rw [he]

/-- The residual from a unit-direction atom at radius `r` is the corresponding
positive-part scalar times its direction. -/
theorem radialClip_residual_of_unit_direction
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (e : H) (he : ‖e‖ = 1) :
    r • e - radialClip τ (r • e) = max (r - τ) 0 • e := by
  have hnorm : ‖r • e‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]
  rw [radialClip_residual_direction_formula hτ, hnorm, smul_smul]
  congr 1
  field_simp

/-- The corresponding negative atom contributes the opposite residual. -/
theorem radialClip_residual_of_negative_unit_direction
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (e : H) (he : ‖e‖ = 1) :
    -(r • e) - radialClip τ (-(r • e)) = -(max (r - τ) 0 • e) := by
  have hnorm : ‖-(r • e)‖ = r := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, mul_one]
  rw [radialClip_residual_direction_formula hτ, hnorm]
  rw [smul_neg, smul_smul]
  congr 1
  field_simp

/-- The signed pair of radius-`r` atoms contributes exactly the prescribed
coefficient `v` to the entire residual-mean path, simultaneously for every
positive clipping threshold. -/
theorem signed_atoms_reproduce_residual_path
    (q r : ℝ) (v e : H) (hr : 0 < r) (he : ‖e‖ = 1)
    (hve : ‖v‖ • e = v) {τ : ℝ} (hτ : 0 < τ) :
    ((q + ‖v‖) / 2) • (r • e - radialClip τ (r • e)) +
      ((q - ‖v‖) / 2) • (-(r • e) - radialClip τ (-(r • e))) =
        max (r - τ) 0 • v := by
  rw [radialClip_residual_of_unit_direction hτ hr e he,
    radialClip_residual_of_negative_unit_direction hτ hr e he]
  calc
    ((q + ‖v‖) / 2) • (max (r - τ) 0 • e) +
        ((q - ‖v‖) / 2) • (-(max (r - τ) 0 • e)) =
          max (r - τ) 0 • (‖v‖ • e) := by module
    _ = max (r - τ) 0 • v := by rw [hve]

/-- Summing the signed-atom construction over finitely many radii gives the
residual path used in the finite-support part of the article's proof. -/
theorem signed_atoms_reproduce_finite_residual_path
    {ι : Type*} (s : Finset ι) (q r : ι → ℝ) (v e : ι → H)
    (hr : ∀ i ∈ s, 0 < r i)
    (he : ∀ i ∈ s, ‖e i‖ = 1)
    (hve : ∀ i ∈ s, ‖v i‖ • e i = v i)
    {τ : ℝ} (hτ : 0 < τ) :
    ∑ i ∈ s,
      (((q i + ‖v i‖) / 2) •
          (r i • e i - radialClip τ (r i • e i)) +
        ((q i - ‖v i‖) / 2) •
          (-(r i • e i) - radialClip τ (-(r i • e i)))) =
      ∑ i ∈ s, max (r i - τ) 0 • v i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact signed_atoms_reproduce_residual_path
    (q i) (r i) (v i) (e i) (hr i hi) (he i hi) (hve i hi) hτ

/-- The real-valued weight of each point in the finite signed-atom sample
space. `none` represents a zero-length atom. -/
def signedAtomWeight {ι : Type*} (q0 : ℝ) (q : ι → ℝ) (v : ι → H) :
    Option (ι × Bool) → ℝ
  | none => q0
  | some (i, true) => (q i + ‖v i‖) / 2
  | some (i, false) => (q i - ‖v i‖) / 2

omit [InnerProductSpace ℝ H] in
theorem signedAtomWeight_nonneg
    {ι : Type*} (q0 : ℝ) (q : ι → ℝ) (v : ι → H)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i) :
    ∀ a, 0 ≤ signedAtomWeight q0 q v a := by
  intro a
  cases a with
  | none => exact hq0
  | some a =>
    rcases a with ⟨i, b⟩
    cases b <;> simp only [signedAtomWeight] <;> linarith [norm_nonneg (v i), hv i]

omit [InnerProductSpace ℝ H] in
theorem sum_signedAtomWeight
    {ι : Type*} [Fintype ι] (q0 : ℝ) (q : ι → ℝ) (v : ι → H) :
    ∑ a : Option (ι × Bool), signedAtomWeight q0 q v a =
      q0 + ∑ i, q i := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [signedAtomWeight, Fintype.sum_bool]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The finite probability mass function implementing the signed-atom
construction. This is a genuine probability law, not merely formal weights. -/
def signedAtomPMF {ι : Type*} [Fintype ι]
    (q0 : ℝ) (q : ι → ℝ) (v : ι → H)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1) : PMF (Option (ι × Bool)) := by
  let w : Option (ι × Bool) → ℝ := signedAtomWeight q0 q v
  have hw : ∀ a, 0 ≤ w a := signedAtomWeight_nonneg q0 q v hq0 hv
  apply PMF.ofFintype (fun a ↦ ENNReal.ofReal (w a))
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun a _ ↦ hw a)]
  have hmass : (∑ a, w a) = 1 := by
    change (∑ a, signedAtomWeight q0 q v a) = 1
    rw [sum_signedAtomWeight]
    exact hsum
  rw [hmass]
  simp

/-- The finite random vector associated with a signed-atom sample. -/
def signedAtomRV {ι : Type*} (r : ι → ℝ) (e : ι → H) :
    Option (ι × Bool) → H
  | none => 0
  | some (i, true) => r i • e i
  | some (i, false) => -(r i • e i)

/-- The finite signed-atom *probability law* has precisely the prescribed
residual path. This is the probabilistic counterpart of the algebraic finite
sum identity above. -/
theorem integral_signedAtomRV_residual
    {ι : Type*} [Fintype ι] [CompleteSpace H]
    [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → H)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hr : ∀ i, 0 < r i) (he : ∀ i, ‖e i‖ = 1)
    (hve : ∀ i, ‖v i‖ • e i = v i)
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ a, (signedAtomRV r e a - radialClip τ (signedAtomRV r e a))
      ∂(signedAtomPMF q0 q v hq0 hv hsum).toMeasure) =
      ∑ i, max (r i - τ) 0 • v i := by
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  change (∫ a, signedAtomRV r e a - radialClip τ (signedAtomRV r e a)
    ∂p.toMeasure) = _
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [signedAtomRV, radialClip_zero hτ.le, sub_self, smul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  simp only [p, signedAtomPMF, PMF.ofFintype_apply, signedAtomWeight]
  have hweights := signed_atom_weights (q i) ‖v i‖ (norm_nonneg _) (hv i)
  rw [ENNReal.toReal_ofReal hweights.1,
    ENNReal.toReal_ofReal hweights.2.1]
  exact signed_atoms_reproduce_residual_path
    (q i) (r i) (v i) (e i) (hr i) (he i) (hve i) hτ

/-- The mean of the finite signed-atom law is the initial value of its
residual path, namely the sum of `r i • v i`. -/
theorem integral_signedAtomRV
    {ι : Type*} [Fintype ι] [CompleteSpace H]
    [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → H)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hve : ∀ i, ‖v i‖ • e i = v i) :
    (∫ a, signedAtomRV r e a
      ∂(signedAtomPMF q0 q v hq0 hv hsum).toMeasure) =
      ∑ i, r i • v i := by
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  change (∫ a, signedAtomRV r e a ∂p.toMeasure) = _
  rw [PMF.integral_eq_sum, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [signedAtomRV, smul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  simp only [p, signedAtomPMF, PMF.ofFintype_apply, signedAtomWeight]
  have hweights := signed_atom_weights (q i) ‖v i‖ (norm_nonneg _) (hv i)
  rw [ENNReal.toReal_ofReal hweights.1,
    ENNReal.toReal_ofReal hweights.2.1]
  exact signed_atoms_reproduce_coefficient (q i) (r i) (v i) (e i) (hve i)

/-- Every test function of the radius sees precisely the original mass `q0`
at zero and mass `q i` at radius `r i`, regardless of the chosen directions. -/
theorem integral_signedAtomRV_norm_test
    {ι : Type*} [Fintype ι] [CompleteSpace H]
    [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → H)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hr : ∀ i, 0 < r i) (he : ∀ i, ‖e i‖ = 1)
    (f : ℝ → ℝ) :
    (∫ a, f ‖signedAtomRV r e a‖
      ∂(signedAtomPMF q0 q v hq0 hv hsum).toMeasure) =
      q0 * f 0 + ∑ i, q i * f (r i) := by
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  change (∫ a, f ‖signedAtomRV r e a‖ ∂p.toMeasure) = _
  rw [PMF.integral_eq_sum, Fintype.sum_option, Fintype.sum_prod_type]
  have hq0real : (ENNReal.ofReal q0).toReal = q0 := ENNReal.toReal_ofReal hq0
  simp only [p, signedAtomPMF, PMF.ofFintype_apply, signedAtomWeight,
    signedAtomRV, norm_zero, hq0real, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  have hweights := signed_atom_weights (q i) ‖v i‖ (norm_nonneg _) (hv i)
  rw [ENNReal.toReal_ofReal hweights.1,
    ENNReal.toReal_ofReal hweights.2.1]
  have hnorm : ‖r i • e i‖ = r i := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr i), he i, mul_one]
  rw [norm_neg, hnorm]
  ring

omit [InnerProductSpace ℝ H] in
/-- If the source radial law has the finite mass formula, the signed-atom
construction reproduces that law as an equality of pushforward measures. -/
theorem signedAtomRV_same_radial_law
    {ι Ω H' : Type*} [Fintype ι] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [MeasurableSpace Ω] [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → H)
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → H')
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hr : ∀ i, 0 < r i) (he : ∀ i, ‖e i‖ = 1)
    (hXmeas : AEMeasurable (fun ω ↦ ‖X ω‖) μ)
    (hXtest : ∀ f : ℝ →ᵇ ℝ,
      (∫ ω, f ‖X ω‖ ∂μ) = q0 * f 0 + ∑ i, q i * f (r i)) :
    Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun a ↦ ‖signedAtomRV r e a‖)
        (signedAtomPMF q0 q v hq0 hv hsum).toMeasure := by
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  let ν : Measure (Option (ι × Bool)) := p.toMeasure
  have hZmeas : Measurable (fun a ↦ ‖signedAtomRV r e a‖) :=
    measurable_of_finite _
  have hmapX : IsProbabilityMeasure (Measure.map (fun ω ↦ ‖X ω‖) μ) :=
    Measure.isProbabilityMeasure_map hXmeas
  have hmapZ : IsProbabilityMeasure
      (Measure.map (fun a ↦ ‖signedAtomRV r e a‖) ν) :=
    Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  letI := hmapX
  letI := hmapZ
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hf : AEStronglyMeasurable (fun x : ℝ ↦ f x)
      (Measure.map (fun ω ↦ ‖X ω‖) μ) :=
    f.continuous.measurable.aestronglyMeasurable
  have hf' : AEStronglyMeasurable (fun x : ℝ ↦ f x)
      (Measure.map (fun a ↦ ‖signedAtomRV r e a‖) ν) :=
    f.continuous.measurable.aestronglyMeasurable
  calc
    (∫ x, f x ∂Measure.map (fun ω ↦ ‖X ω‖) μ)
        = ∫ ω, f ‖X ω‖ ∂μ := integral_map hXmeas hf
    _ = q0 * f 0 + ∑ i, q i * f (r i) := hXtest f
    _ = ∫ a, f ‖signedAtomRV r e a‖ ∂ν := by
      simpa [ν, p] using
        (integral_signedAtomRV_norm_test q0 q r v e hq0 hv hsum hr he f).symm
    _ = ∫ x, f x ∂Measure.map (fun a ↦ ‖signedAtomRV r e a‖) ν :=
      (integral_map hZmeas.aemeasurable hf').symm

/-- Equality of radial laws fixes every clipped second moment, independently
of the directions of the random vectors. -/
theorem integral_norm_radialClip_sq_eq_of_same_radial_law
    {Ω Ω' H' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → H) (Z : Ω' → H')
    (hX : AEMeasurable (fun ω ↦ ‖X ω‖) μ)
    (hZ : AEMeasurable (fun ω ↦ ‖Z ω‖) ν)
    (hradius : Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun ω ↦ ‖Z ω‖) ν)
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ ω, ‖radialClip τ (X ω)‖ ^ 2 ∂μ) =
      (∫ ω, ‖radialClip τ (Z ω)‖ ^ 2 ∂ν) := by
  let f : ℝ → ℝ := fun r ↦ (min r τ) ^ 2
  have hf : Measurable f := by fun_prop
  have hfX : AEStronglyMeasurable f (Measure.map (fun ω ↦ ‖X ω‖) μ) :=
    hf.aestronglyMeasurable
  have hfZ : AEStronglyMeasurable f (Measure.map (fun ω ↦ ‖Z ω‖) ν) :=
    hf.aestronglyMeasurable
  calc
    (∫ ω, ‖radialClip τ (X ω)‖ ^ 2 ∂μ)
        = ∫ ω, f ‖X ω‖ ∂μ := by simp [f, norm_radialClip hτ]
    _ = ∫ r, f r ∂Measure.map (fun ω ↦ ‖X ω‖) μ :=
      (integral_map hX hfX).symm
    _ = ∫ r, f r ∂Measure.map (fun ω ↦ ‖Z ω‖) ν := by rw [hradius]
    _ = ∫ ω, f ‖Z ω‖ ∂ν := integral_map hZ hfZ
    _ = ∫ ω, ‖radialClip τ (Z ω)‖ ^ 2 ∂ν := by
      simp [f, norm_radialClip hτ]

/-- For random vectors with the same radial law, preserving the norm of the
clipped mean is exactly the remaining condition for equality of centered
clipping energies. -/
theorem integral_centered_radialClip_sq_eq_of_same_radial_law
    {Ω Ω' H' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    [CompleteSpace H']
    (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → H) (Z : Ω' → H')
    (hX : Integrable X μ) (hZ : Integrable Z ν)
    (hradius : Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun ω ↦ ‖Z ω‖) ν)
    {τ : ℝ} (hτ : 0 < τ)
    (hmean : ‖∫ ω, radialClip τ (X ω) ∂μ‖ =
      ‖∫ ω, radialClip τ (Z ω) ∂ν‖) :
    (∫ ω, ‖radialClip τ (X ω) -
      ∫ ξ, radialClip τ (X ξ) ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖radialClip τ (Z ω) -
        ∫ ξ, radialClip τ (Z ξ) ∂ν‖ ^ 2 ∂ν) := by
  have hY : Integrable (fun ω ↦ radialClip τ (X ω)) μ :=
    integrable_radialClip hX.1 hτ
  have hY' : Integrable (fun ω ↦ radialClip τ (Z ω)) ν :=
    integrable_radialClip hZ.1 hτ
  have hYsq : Integrable (fun ω ↦ ‖radialClip τ (X ω)‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hX.1 hτ
  have hYsq' : Integrable (fun ω ↦ ‖radialClip τ (Z ω)‖ ^ 2) ν :=
    integrable_sq_norm_radialClip hZ.1 hτ
  rw [integral_norm_sub_mean_sq μ _ hY hYsq,
    integral_norm_sub_mean_sq ν _ hY' hYsq']
  rw [integral_norm_radialClip_sq_eq_of_same_radial_law μ ν X Z
      hX.1.norm.aemeasurable hZ.1.norm.aemeasurable hradius hτ, hmean]

/-- The two residual-path distances used in the article, together with the
radial law, imply both conclusions of its simultaneous-realization theorem.
This theorem is independent of how a matching path is constructed. -/
theorem all_thresholds_bias_energy_of_residual_path_geometry
    {Ω Ω' H' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    [CompleteSpace H']
    (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → H) (Z : Ω' → H')
    (hX : Integrable X μ) (hZ : Integrable Z ν)
    (hradius : Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun ω ↦ ‖Z ω‖) ν)
    (hresidual : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, X ω - radialClip τ (X ω) ∂μ‖ =
        ‖∫ ω, Z ω - radialClip τ (Z ω) ∂ν‖)
    (hclipped : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, radialClip τ (X ω) ∂μ‖ =
        ‖∫ ω, radialClip τ (Z ω) ∂ν‖) :
    ∀ τ : ℝ, 0 < τ →
      ‖(∫ ω, radialClip τ (X ω) ∂μ) - ∫ ω, X ω ∂μ‖ =
        ‖(∫ ω, radialClip τ (Z ω) ∂ν) - ∫ ω, Z ω ∂ν‖ ∧
      (∫ ω, ‖radialClip τ (X ω) -
        ∫ ξ, radialClip τ (X ξ) ∂μ‖ ^ 2 ∂μ) =
        (∫ ω, ‖radialClip τ (Z ω) -
          ∫ ξ, radialClip τ (Z ξ) ∂ν‖ ^ 2 ∂ν) := by
  intro τ hτ
  have hY : Integrable (fun ω ↦ radialClip τ (X ω)) μ :=
    integrable_radialClip hX.1 hτ
  have hY' : Integrable (fun ω ↦ radialClip τ (Z ω)) ν :=
    integrable_radialClip hZ.1 hτ
  constructor
  · rw [norm_sub_rev (∫ ω, radialClip τ (X ω) ∂μ) (∫ ω, X ω ∂μ),
      norm_sub_rev (∫ ω, radialClip τ (Z ω) ∂ν) (∫ ω, Z ω ∂ν),
      ← integral_sub hX hY, ← integral_sub hZ hY']
    exact hresidual τ hτ
  · exact integral_centered_radialClip_sq_eq_of_same_radial_law
      μ ν X Z hX hZ hradius hτ (hclipped τ hτ)

/-- Once the finite three-dimensional path coefficients satisfy the two
distance conditions, the signed-atom law realizes the *full* bias--energy
trajectory. The geometric folding step is isolated in the two hypotheses
`hresidualGeometry` and `hclippedGeometry`. -/
theorem signedAtomRV_realizes_all_thresholds_of_geometry
    {ι Ω H' : Type*} [Fintype ι] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [MeasurableSpace Ω] [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → H)
    (hX : Integrable X μ)
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → H')
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hr : ∀ i, 0 < r i) (he : ∀ i, ‖e i‖ = 1)
    (hve : ∀ i, ‖v i‖ • e i = v i)
    (hXtest : ∀ f : ℝ →ᵇ ℝ,
      (∫ ω, f ‖X ω‖ ∂μ) = q0 * f 0 + ∑ i, q i * f (r i))
    (hresidualGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, X ω - radialClip τ (X ω) ∂μ‖ =
        ‖∑ i, max (r i - τ) 0 • v i‖)
    (hclippedGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, radialClip τ (X ω) ∂μ‖ =
        ‖(∑ i, r i • v i) - ∑ i, max (r i - τ) 0 • v i‖) :
    let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
    let Z : Option (ι × Bool) → H' := signedAtomRV r e
    Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun a ↦ ‖Z a‖) p.toMeasure ∧
      ∀ τ : ℝ, 0 < τ →
        ‖(∫ ω, radialClip τ (X ω) ∂μ) - ∫ ω, X ω ∂μ‖ =
          ‖(∫ a, radialClip τ (Z a) ∂p.toMeasure) -
            ∫ a, Z a ∂p.toMeasure‖ ∧
        (∫ ω, ‖radialClip τ (X ω) -
          ∫ ξ, radialClip τ (X ξ) ∂μ‖ ^ 2 ∂μ) =
          (∫ a, ‖radialClip τ (Z a) -
            ∫ b, radialClip τ (Z b) ∂p.toMeasure‖ ^ 2 ∂p.toMeasure) := by
  dsimp only
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  let Z : Option (ι × Bool) → H' := signedAtomRV r e
  let ν : Measure (Option (ι × Bool)) := p.toMeasure
  have hZ : Integrable Z ν := Integrable.of_finite
  have hradius : Measure.map (fun ω ↦ ‖X ω‖) μ =
      Measure.map (fun a ↦ ‖Z a‖) ν := by
    exact signedAtomRV_same_radial_law μ X q0 q r v e hq0 hv hsum hr he
      hX.1.norm.aemeasurable hXtest
  have hresidual : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, X ω - radialClip τ (X ω) ∂μ‖ =
        ‖∫ a, Z a - radialClip τ (Z a) ∂ν‖ := by
    intro τ hτ
    rw [show (∫ a, Z a - radialClip τ (Z a) ∂ν) =
      ∑ i, max (r i - τ) 0 • v i by
      exact integral_signedAtomRV_residual q0 q r v e
        hq0 hv hsum hr he hve hτ]
    exact hresidualGeometry τ hτ
  have hclipped : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, radialClip τ (X ω) ∂μ‖ =
        ‖∫ a, radialClip τ (Z a) ∂ν‖ := by
    intro τ hτ
    have hY : Integrable (fun a ↦ radialClip τ (Z a)) ν :=
      integrable_radialClip hZ.1 hτ
    have hmean : (∫ a, Z a ∂ν) = ∑ i, r i • v i :=
      integral_signedAtomRV q0 q r v e hq0 hv hsum hve
    have hres : (∫ a, Z a - radialClip τ (Z a) ∂ν) =
        ∑ i, max (r i - τ) 0 • v i :=
      integral_signedAtomRV_residual q0 q r v e hq0 hv hsum hr he hve hτ
    calc
      ‖∫ ω, radialClip τ (X ω) ∂μ‖ =
          ‖(∑ i, r i • v i) - ∑ i, max (r i - τ) 0 • v i‖ :=
        hclippedGeometry τ hτ
      _ = ‖∫ a, radialClip τ (Z a) ∂ν‖ := by
        rw [← hmean, ← hres, integral_sub hZ hY]
        congr 1
        abel
  constructor
  · exact hradius
  · exact all_thresholds_bias_energy_of_residual_path_geometry
      μ ν X Z hX hZ hradius hresidual hclipped

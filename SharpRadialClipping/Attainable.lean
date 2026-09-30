import SharpRadialClipping.Geometry
import SharpRadialClipping.Sharpness

/-!
# Closure of the attainable bias--energy set

This module connects the limiting rare-shock curve to actual centered
two-point laws.  It proves only the inclusion of the curve in the closure of
the attainable set; no converse or complete feasible-set description is
claimed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open unitInterval

noncomputable section

/-- The normalized `(clipped energy, clipping bias)` coordinates of one law. -/
def normalizedBiasEnergyPair
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure Ω) (p τ : ℝ) (X : Ω → H) : ℝ × ℝ :=
  (stochasticClippingRatio μ 0 1 p τ X,
    stochasticClippingRatio μ 1 0 p τ X)

/-- Actual normalized bias--energy pairs realized by centered nonzero laws on
the finite measurable space `Bool`. -/
def centeredBoolBiasEnergyPairs
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p τ : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ (μ : Measure Bool) (_hμ : IsProbabilityMeasure μ)
      (X : Bool → H),
      MemLp X (ENNReal.ofReal p) μ ∧
      (∫ b, X b ∂μ) = 0 ∧
      0 < ∫ b, ‖X b‖ ^ p ∂μ ∧
      z = normalizedBiasEnergyPair μ p τ X}

/-- Exact finite-`q` pair produced by the centered rare two-point law. -/
def rareTwoPointBiasEnergyPair (p R q : ℝ) : ℝ × ℝ :=
  (rareReducedRatio 0 1 p R q, rareReducedRatio 1 0 p R q)

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every admissible finite-`q` rare pair is genuinely realized by a centered
law on `Bool`; this is not merely a formal parametrized curve. -/
theorem rareTwoPointBiasEnergyPair_mem_centeredBool
    {p R q τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < q) (hq : q < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    rareTwoPointBiasEnergyPair p R q ∈
      centeredBoolBiasEnergyPairs H p τ := by
  have hq1 : q < 1 := by
    have hden : 0 < 1 + R := by linarith
    exact hq.trans ((div_lt_one hden).2 (by linarith))
  let qI : I := ⟨q, hq0.le, hq1.le⟩
  let X : Bool → H := rareTwoPoint R τ q e
  refine ⟨rareBernoulli qI, inferInstance, X, MemLp.of_discrete, ?_, ?_, ?_⟩
  · dsimp only [X, qI]
    exact integral_rareTwoPoint hR hq e
  · dsimp only [X, qI]
    rw [integral_norm_rareTwoPoint_rpow hR hτ hq0 hq he]
    have hdenq : 0 < 1 - q := sub_pos.mpr hq1
    have htail :
        0 ≤ q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1) :=
      div_nonneg
        (mul_nonneg (Real.rpow_nonneg hq0.le (p - 1))
          (Real.rpow_nonneg (zero_lt_one.trans hR).le p))
        (Real.rpow_nonneg hdenq.le (p - 1))
    exact mul_pos
      (mul_pos hq0 (Real.rpow_pos_of_pos hτ p))
      (add_pos_of_pos_of_nonneg
        (Real.rpow_pos_of_pos (zero_lt_one.trans hR) p) htail)
  · apply Prod.ext
    · dsimp only [normalizedBiasEnergyPair, rareTwoPointBiasEnergyPair, X, qI]
      simpa only [qI] using
        (stochasticClippingRatio_rareTwoPoint_eq
          (H := H) (q := qI) (α := 0) (β := 1) (p := p)
          hR hτ (by simpa [qI] using hq0)
          (by simpa [qI] using hq) he).symm
    · dsimp only [normalizedBiasEnergyPair, rareTwoPointBiasEnergyPair, X, qI]
      simpa only [qI] using
        (stochasticClippingRatio_rareTwoPoint_eq
          (H := H) (q := qI) (α := 1) (β := 0) (p := p)
          hR hτ (by simpa [qI] using hq0)
          (by simpa [qI] using hq) he).symm

/-- The finite rare-law pairs converge to the limiting rare-shock point. -/
theorem tendsto_rareTwoPointBiasEnergyPair
    {p R : ℝ} (hp : 1 < p) (hR : 0 < R) :
    Tendsto (fun q => rareTwoPointBiasEnergyPair p R q)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (rareEnergy p R, rareBias p R)) := by
  have henergy :=
    tendsto_rareReducedRatio (α := 0) (β := 1) hp hR
  have hbias :=
    tendsto_rareReducedRatio (α := 1) (β := 0) hp hR
  have hpair := henergy.prodMk_nhds hbias
  simpa only [rareTwoPointBiasEnergyPair, rareEnergy, rareBias,
    zero_mul, zero_add, one_mul, add_zero, Real.rpow_neg hR.le,
    div_eq_mul_inv] using hpair

/-- The radius-one endpoint `(1,0)` is itself realized by the centered
symmetric two-point law. -/
theorem normalizedBiasEnergyPair_symmetric_eq
    {p τ : ℝ} (hτ : 0 < τ) {e : H} (he : ‖e‖ = 1) :
    normalizedBiasEnergyPair symmetricBernoulli p τ
        (symmetricTwoPoint τ e) = (1, 0) := by
  have hpow : τ ^ (1 - p) * τ ^ p = τ := by
    rw [← Real.rpow_add hτ]
    norm_num
  apply Prod.ext
  · dsimp only [normalizedBiasEnergyPair, stochasticClippingRatio]
    rw [integral_centered_clipped_symmetricTwoPoint_sq hτ he,
      integral_norm_symmetricTwoPoint_rpow hτ he,
      integral_symmetricTwoPoint,
      integral_radialClip_symmetricTwoPoint hτ he, hpow]
    field_simp [hτ.ne']
    simp
  · dsimp only [normalizedBiasEnergyPair, stochasticClippingRatio]
    rw [integral_symmetricTwoPoint,
      integral_radialClip_symmetricTwoPoint hτ he,
      integral_norm_symmetricTwoPoint_rpow hτ he]
    simp

/-- The radius-one rare-shock endpoint is an actual attainable pair. -/
theorem rare_endpoint_mem_centeredBool
    [Nontrivial H] {p τ : ℝ} (hτ : 0 < τ) :
    (rareEnergy p 1, rareBias p 1) ∈
      centeredBoolBiasEnergyPairs H p τ := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let X : Bool → H := symmetricTwoPoint τ e
  have hmoment :
      0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli := by
    dsimp only [X]
    rw [integral_norm_symmetricTwoPoint_rpow hτ he]
    exact Real.rpow_pos_of_pos hτ p
  refine ⟨symmetricBernoulli, inferInstance, X, MemLp.of_discrete,
    integral_symmetricTwoPoint τ e, hmoment, ?_⟩
  rw [normalizedBiasEnergyPair_symmetric_eq hτ he]
  simp [rareEnergy, rareBias]

/-- Every limiting rare-shock point with radius strictly above one belongs to
the closure of the actual centered finite two-point attainable set. -/
theorem rare_point_mem_closure_centeredBool
    [Nontrivial H] {p R τ : ℝ}
    (hp : 1 < p) (hR : 1 < R) (hτ : 0 < τ) :
    (rareEnergy p R, rareBias p R) ∈
      closure (centeredBoolBiasEnergyPairs H p τ) := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  apply mem_closure_of_tendsto
    (tendsto_rareTwoPointBiasEnergyPair hp (zero_lt_one.trans hR))
  have hupper : ∀ᶠ q : ℝ in 𝓝[>] 0, q < 1 / (1 + R) :=
    (eventually_lt_nhds
      (show (0 : ℝ) < 1 / (1 + R) by positivity)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hupper] with q hq0 hq
  exact rareTwoPointBiasEnergyPair_mem_centeredBool
    (H := H) hR hτ hq0 hq he

/-- Literal scope-boundary statement: every point of the rare-shock curve
with radius at least one lies in the closure of the actual centered
two-point attainable set.  No converse is asserted. -/
theorem rareCurve_subset_closure_centeredBool
    [Nontrivial H] {p τ : ℝ} (hp : 1 < p) (hτ : 0 < τ) :
    rareCurve p ⊆ closure (centeredBoolBiasEnergyPairs H p τ) := by
  intro z hz
  rcases hz with ⟨R, hR, rfl⟩
  rcases hR.eq_or_lt with rfl | hR'
  · exact subset_closure
      (rare_endpoint_mem_centeredBool (H := H) hτ)
  · exact rare_point_mem_closure_centeredBool (H := H) hp hR' hτ

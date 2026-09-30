import H099.AttainableP1
import H099.StochasticConditionalP1

/-! Exact stochastic sharpness at the first-moment endpoint. -/

open MeasureTheory

noncomputable section

universe u v

variable {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

omit [MeasurableSpace H] [CompleteSpace H] in
/-- The normalized weighted objective is linear in its two weights. -/
lemma stochasticClippingRatio_p1_linear
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (α β τ : ℝ) (X : Ω → H) :
    stochasticClippingRatio μ α β 1 τ X =
      α * stochasticClippingRatio μ 1 0 1 τ X +
        β * stochasticClippingRatio μ 0 1 1 τ X := by
  dsimp [stochasticClippingRatio]
  ring

/-- All first-moment stochastic objective values over nonzero laws. -/
def p1StochasticRatios
    (H : Type v) [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (α β τ : ℝ) : Set ℝ :=
  {z | ∃ law : RandomVectorLaw.{u, v} H 1,
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    z = stochasticClippingRatio law.μ α β 1 τ law.X}

/-- Every weighted value is at most the sharp first-moment constant. -/
theorem p1StochasticRatios_le
    {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 < τ)
    {z : ℝ} (hz : z ∈ p1StochasticRatios.{u, v} H α β τ) :
    z ≤ K_p α β 1 := by
  obtain ⟨law, hz⟩ := hz
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  rw [hz]
  have hX : Integrable law.X law.μ :=
    law.memLp.integrable (ENNReal.one_le_ofReal.mpr le_rfl)
  have henv := stochastic_radialClip_envelope_p1
    law.μ hα hβ hτ law.X hX
  have hden : 0 < τ ^ (1 - (1 : ℝ)) *
      (∫ ω, ‖law.X ω‖ ^ (1 : ℝ) ∂law.μ) :=
    mul_pos (Real.rpow_pos_of_pos hτ _) law.moment_pos
  dsimp only [stochasticClippingRatio]
  apply (div_le_iff₀ hden).2
  simpa only [mul_assoc] using henv

/-- A realized energy--bias pair yields the corresponding weighted objective. -/
lemma weighted_ratio_mem_of_pair
    {α β τ e d : ℝ}
    (hpair : (e, d) ∈ attainableBiasEnergyPairsP1.{u, v} H τ) :
    α * d + β * e ∈ p1StochasticRatios.{u, v} H α β τ := by
  obtain ⟨law, hlaw⟩ := hpair
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  refine ⟨law, ?_⟩
  have hcoords :
      stochasticClippingRatio law.μ 0 1 1 τ law.X = e ∧
      stochasticClippingRatio law.μ 1 0 1 τ law.X = d := by
    have h := Prod.mk.inj hlaw.symm
    exact ⟨h.1.symm, h.2.symm⟩
  rw [stochasticClippingRatio_p1_linear, hcoords.1, hcoords.2]

/-- Proposition 3.2 at `p=1`: the supremum over actual nonzero stochastic
laws is `K₁(α,β)=max α β`, with no centering restriction. -/
theorem sSup_p1StochasticRatios_eq_K_p
    [Nontrivial H] {α β τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 < τ) :
    sSup (p1StochasticRatios.{u, v} H α β τ) = K_p α β 1 := by
  have hnonempty : (p1StochasticRatios.{u, v} H α β τ).Nonempty := by
    have hpair := p1_boundary_mem_attainable (H := H)
      hτ (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)
    refine ⟨β, ?_⟩
    simpa using weighted_ratio_mem_of_pair (H := H) (α := α) (β := β) hpair
  rw [K_p_one_eq_max hα hβ]
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hnonempty
  · intro z hz
    simpa [K_p_one_eq_max hα hβ] using
      p1StochasticRatios_le (H := H) hα hβ hτ hz
  · intro a ha
    by_cases hβα : α ≤ β
    · have hpair := p1_boundary_mem_attainable (H := H)
        hτ (show (0 : ℝ) ≤ 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)
      refine ⟨β, ?_, ?_⟩
      · simpa using weighted_ratio_mem_of_pair (H := H) (α := α) (β := β) hpair
      · simpa [max_eq_right hβα] using ha
    · have hβα' : β < α := lt_of_not_ge hβα
      have haα : a < α := by simpa [max_eq_left hβα'.le] using ha
      by_cases haβ : a < β
      · have hpair := p1_boundary_mem_attainable (H := H)
          hτ (show (0 : ℝ) ≤ 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)
        refine ⟨β, ?_, haβ⟩
        simpa using weighted_ratio_mem_of_pair (H := H) (α := α) (β := β) hpair
      · have hβa : β ≤ a := le_of_not_gt haβ
        let ε : ℝ := (α - a) / (2 * (α - β))
        have hε : 0 < ε := by dsimp [ε]; positivity
        have hεhalf : ε ≤ 1 / 2 := by
          dsimp [ε]
          apply (div_le_iff₀ (by positivity : 0 < 2 * (α - β))).2
          nlinarith
        let d : ℝ := 1 - ε
        have hd : 0 ≤ d := by dsimp [d]; linarith
        have hdlt : d < 1 := by dsimp [d]; linarith
        have hpair := p1_boundary_mem_attainable (H := H)
          hτ hd hdlt
        let z : ℝ := α * d + β * (1 - d)
        refine ⟨z, ?_, ?_⟩
        · exact weighted_ratio_mem_of_pair (H := H) (α := α) (β := β) hpair
        · have heq : (α - β) * ε = (α - a) / 2 := by
            dsimp [ε]
            field_simp [ne_of_gt (sub_pos.mpr hβα')]
          dsimp [z, d]
          nlinarith

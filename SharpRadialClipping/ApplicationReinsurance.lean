import SharpRadialClipping.Stochastic

/-!
# Reinsurance application of the joint clipping envelope

The final inequality is proved once the standard first-two-moment identities
for a random sum of independent identically distributed claims are supplied.
Those identities are explicit hypotheses below; the theorem does not claim
they have yet been derived from independence in this module.
-/

open MeasureTheory

noncomputable section

/-- For a nonnegative scalar, radial clipping is the usual retained loss. -/
lemma radialClip_nonneg_real_eq_min {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    radialClip τ x = min x τ := by
  unfold radialClip
  by_cases h : x ≤ τ
  · simp [h, Real.norm_eq_abs, abs_of_nonneg hx]
  · have hxpos : 0 < x := lt_of_le_of_lt hτ.le (lt_of_not_ge h)
    simp [h, Real.norm_eq_abs, abs_of_pos hxpos, min_eq_right (le_of_lt (lt_of_not_ge h)),
      smul_eq_mul, div_mul_cancel₀ _ hxpos.ne']

/-- The retained loss remains between zero and the original loss. -/
lemma radialClip_nonneg_real_bounds {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    0 ≤ radialClip τ x ∧ radialClip τ x ≤ x := by
  rw [radialClip_nonneg_real_eq_min hτ hx]
  exact ⟨le_min hx hτ.le, min_le_left _ _⟩

/-- Risk-adjusted cost expressed in terms of the random-sum mean and variance. -/
def reinsuranceRiskCost {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Claims X : Ω → ℝ) (μN α γ : ℝ) (τ : ℝ) : ℝ :=
  (∫ ω, Claims ω ∂μ) +
    (1 + α) * μN * (∫ ω, X ω - radialClip τ (X ω) ∂μ) +
    γ * (∫ ω, (Claims ω - ∫ z, Claims z ∂μ) ^ 2 ∂μ)

/-- The reinsurance envelope under exact random-sum mean and variance identities.
The independence-to-moment-identities bridge is deliberately not assumed
silently: `hClaimsMean` and `hClaimsVar` state it exactly. -/
theorem reinsuranceRiskCost_le_of_random_sum_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Claims X : Ω → ℝ) {μN σN2 α γ τ : ℝ}
    (hμN : 0 ≤ μN) (hσN2 : 0 ≤ σN2)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hX : Integrable X μ)
    (hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ)
    (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hClaimsMean : (∫ ω, Claims ω ∂μ) =
      μN * (∫ ω, radialClip τ (X ω) ∂μ))
    (hClaimsVar : (∫ ω, (Claims ω - ∫ z, Claims z ∂μ) ^ 2 ∂μ) =
      μN * (∫ ω, (radialClip τ (X ω) -
        ∫ z, radialClip τ (X z) ∂μ) ^ 2 ∂μ) +
      σN2 * (∫ ω, radialClip τ (X ω) ∂μ) ^ 2) :
    reinsuranceRiskCost μ Claims X μN α γ τ ≤
      μN * (∫ ω, X ω ∂μ) +
      μN / τ * K_p α (γ * τ) 2 * (∫ ω, X ω ^ 2 ∂μ) +
      γ * σN2 * (∫ ω, X ω ∂μ) ^ 2 := by
  let Y : Ω → ℝ := fun ω => radialClip τ (X ω)
  let m : ℝ := ∫ ω, X ω ∂μ
  let b : ℝ := ∫ ω, Y ω ∂μ
  let v : ℝ := ∫ ω, (Y ω - b) ^ 2 ∂μ
  have hY : Integrable Y μ := integrable_radialClip hX.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hX.1 hτ
  have hXsq' : Integrable (fun ω => ‖X ω‖ ^ (2 : ℝ)) μ := by
    convert hXsq using 1
    ext ω
    norm_num
  have hb0 : 0 ≤ b := by
    exact integral_nonneg_of_ae (hXnonneg.mono fun ω hω =>
      (radialClip_nonneg_real_bounds hτ hω).1)
  have hbm : b ≤ m := by
    exact integral_mono_ae hY hX (hXnonneg.mono fun ω hω =>
      (radialClip_nonneg_real_bounds hτ hω).2)
  have hm0 : 0 ≤ m := le_trans hb0 hbm
  have hJoint := stochastic_radialClip_envelope μ hα
    (mul_nonneg hγ hτ.le) (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≤ 2) hτ X hX hY hYsq hXsq'
  have hnormSq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by
    rw [Real.norm_eq_abs]
    exact sq_abs x
  have hnormRpow (x : ℝ) : ‖x‖ ^ (2 : ℝ) = x ^ 2 := by
    norm_num
  have hJoint' : α * (m - b) + γ * v ≤
      K_p α (γ * τ) 2 / τ * (∫ ω, X ω ^ 2 ∂μ) := by
    dsimp only at hJoint
    have hn : ‖b - m‖ = m - b := by rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hbm)]
    rw [hn] at hJoint
    have hγτ : (γ * τ) / τ = γ := by field_simp
    rw [hγτ] at hJoint
    have hpow : τ ^ (1 - (2 : ℝ)) = 1 / τ := by
      rw [show 1 - (2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]; ring
    rw [hpow] at hJoint
    simp_rw [hnormSq] at hJoint
    simp_rw [hnormRpow] at hJoint
    convert hJoint using 1
    ring
  have hdiff : (∫ ω, X ω - Y ω ∂μ) = m - b := integral_sub hX hY
  have hbSq : b ^ 2 ≤ m ^ 2 := by nlinarith
  dsimp [reinsuranceRiskCost]
  rw [hClaimsVar, hClaimsMean]
  change μN * b + (1 + α) * μN * (∫ ω, X ω - Y ω ∂μ) +
    γ * (μN * v + σN2 * b ^ 2) ≤
      μN * m + μN / τ * K_p α (γ * τ) 2 * (∫ ω, X ω ^ 2 ∂μ) +
      γ * σN2 * m ^ 2
  rw [hdiff]
  have hscaled : μN * (α * (m - b) + γ * v) ≤
      μN * (K_p α (γ * τ) 2 / τ * (∫ ω, X ω ^ 2 ∂μ)) :=
    mul_le_mul_of_nonneg_left hJoint' hμN
  have hscaled' : μN * (α * (m - b) + γ * v) ≤
      μN / τ * K_p α (γ * τ) 2 * (∫ ω, X ω ^ 2 ∂μ) := by
    calc
      _ ≤ μN * (K_p α (γ * τ) 2 / τ * (∫ ω, X ω ^ 2 ∂μ)) := hscaled
      _ = _ := by ring
  have hlast : γ * σN2 * b ^ 2 ≤ γ * σN2 * m ^ 2 :=
    mul_le_mul_of_nonneg_left hbSq (mul_nonneg hγ hσN2)
  nlinarith [hscaled', hlast]

#print axioms reinsuranceRiskCost_le_of_random_sum_moments

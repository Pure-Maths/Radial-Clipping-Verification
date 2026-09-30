import SharpRadialClipping.ApplicationRandomSumFull
import SharpRadialClipping.ApplicationReinsuranceIID
import SharpRadialClipping.ApplicationReinsurance

/-!
# Reinsurance corollary from IID loss and independent count assumptions

This module discharges the random-sum moment hypotheses of
`reinsuranceRiskCost_le_of_random_sum_moments`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The article's risk-adjusted reinsurance bound, under the IID loss model. -/
theorem reinsuranceRiskCost_le_of_iid
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (X : ℕ → Ω → ℝ) {α γ τ : ℝ}
    (hN : Measurable N)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ)
    (hXmeas : ∀ i, Measurable (X i))
    (hXnonneg : ∀ i ω, 0 ≤ X i ω)
    (hX2 : MemLp (X 0) 2 μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hIndep : iIndepFun X μ)
    (hNseq : IndepFun N (fun ω : Ω ↦ fun i : ℕ ↦ X i ω) μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hτ : 0 < τ) :
    reinsuranceRiskCost μ
      (retainedClaims N (fun i ω ↦ radialClip τ (X i ω))) (X 0)
      (∫ ω, (N ω : ℝ) ∂μ) α γ τ ≤
      (∫ ω, (N ω : ℝ) ∂μ) * (∫ ω, X 0 ω ∂μ) +
      (∫ ω, (N ω : ℝ) ∂μ) / τ * K_p α (γ * τ) 2 *
        (∫ ω, X 0 ω ^ 2 ∂μ) +
      γ * ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) -
        (∫ ω, (N ω : ℝ) ∂μ) ^ 2) *
        (∫ ω, X 0 ω ∂μ) ^ 2 := by
  let Y : ℕ → Ω → ℝ := fun i ω ↦ radialClip τ (X i ω)
  let Claims : Ω → ℝ := retainedClaims N Y
  let μN : ℝ := ∫ ω, (N ω : ℝ) ∂μ
  let σN2 : ℝ := (∫ ω, (N ω : ℝ) ^ 2 ∂μ) - μN ^ 2
  let m : ℝ := ∫ ω, Y 0 ω ∂μ
  let s : ℝ := ∫ ω, Y 0 ω ^ 2 ∂μ
  have hYmeas (i : ℕ) : Measurable (Y i) :=
    (continuous_radialClip τ hτ).measurable.comp (hXmeas i)
  have hYbound (i : ℕ) (ω : Ω) : 0 ≤ Y i ω ∧ Y i ω ≤ τ := by
    rw [show Y i ω = min (X i ω) τ from radialClip_nonneg_real_eq_min hτ (hXnonneg i ω)]
    exact ⟨le_min (hXnonneg i ω) hτ.le, min_le_right _ _⟩
  obtain ⟨hYIdent, hYIndep, hYNseq⟩ :=
    clipped_iid_independence_data μ N X τ hτ hIdent hIndep hNseq
  have hYL2 : MemLp (Y 0) 2 μ := by
    apply MemLp.of_le hX2 (aestronglyMeasurable_radialClip hX2.1 hτ)
    filter_upwards with ω
    exact (norm_radialClip hτ (X 0 ω)).trans_le (min_le_left _ _)
  obtain ⟨_, hYint, hYsq, hYmean, hYsecond⟩ :=
    iid_l2_moment_data μ Y hYIdent hYL2
  have hYpair (i j : ℕ) (hij : i ≠ j) : IndepFun (Y i) (Y j) μ :=
    hYIndep.indepFun hij
  have hMom := random_sum_mean_and_second_moment μ N Y τ m s
    hN hN2 hYmeas hYbound hYint hYsq hYmean hYsecond hYpair hYNseq
  have hCVar := random_sum_centered_variance μ N Y τ m s
    hN hN2 hYmeas hYbound hYint hYsq hYmean hYsecond hYpair hYNseq
  have hNint : Integrable (fun ω ↦ (N ω : ℝ)) μ := by
    have hB : Integrable (fun ω ↦ 1 + (N ω : ℝ) ^ 2) μ :=
      (integrable_const (1 : ℝ)).add hN2
    have hNreal : Measurable (fun ω ↦ (N ω : ℝ)) := by fun_prop
    apply Integrable.mono' hB hNreal.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    nlinarith [sq_nonneg ((N ω : ℝ) - 1 / 2)]
  have hNVar : (∫ ω, ((N ω : ℝ) - μN) ^ 2 ∂μ) = σN2 := by
    have hv := integral_norm_sub_mean_sq μ (fun ω ↦ (N ω : ℝ)) hNint (by
      simpa only [Real.norm_eq_abs, sq_abs] using hN2)
    simp_rw [Real.norm_eq_abs, sq_abs] at hv
    exact hv
  have hσN2 : 0 ≤ σN2 := by
    rw [← hNVar]
    exact integral_nonneg fun ω ↦ sq_nonneg _
  have hμN : 0 ≤ μN := integral_nonneg fun ω ↦ Nat.cast_nonneg _
  have hYVar : (∫ ω, (Y 0 ω - m) ^ 2 ∂μ) = s - m ^ 2 := by
    have hv := integral_norm_sub_mean_sq μ (Y 0) (hYint 0) (by
      simpa only [Real.norm_eq_abs, sq_abs] using hYsq 0)
    simp_rw [Real.norm_eq_abs, sq_abs] at hv
    exact hv
  have hClaimsMean : (∫ ω, Claims ω ∂μ) = μN * (∫ ω, Y 0 ω ∂μ) := hMom.1
  have hClaimsVar :
      (∫ ω, (Claims ω - ∫ z, Claims z ∂μ) ^ 2 ∂μ) =
      μN * (∫ ω, (Y 0 ω - ∫ z, Y 0 z ∂μ) ^ 2 ∂μ) +
        σN2 * (∫ ω, Y 0 ω ∂μ) ^ 2 := by
    rw [hYVar]
    exact hCVar
  have hXint : Integrable (X 0) μ := hX2.integrable (by norm_num)
  have hXsq : Integrable (fun ω ↦ ‖X 0 ω‖ ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hX2.integrable_sq
  have hFinal := reinsuranceRiskCost_le_of_random_sum_moments μ Claims (X 0)
    hμN hσN2 hα hγ hτ hXint hXsq (Filter.Eventually.of_forall (hXnonneg 0))
    hClaimsMean hClaimsVar
  simpa only [Claims, Y, μN, σN2] using hFinal

#print axioms reinsuranceRiskCost_le_of_iid

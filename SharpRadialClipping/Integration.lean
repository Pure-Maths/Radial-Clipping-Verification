import SharpRadialClipping.ClippingMeasure

/-!
# Integrated deterministic envelope

This module integrates the pointwise clipping theorem.  It is the measure
theoretic bridge used by the stochastic result.
-/

open MeasureTheory
open Real

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating the pointwise envelope requires a.e. strong measurability of
the input and integrability of its `p`-moment. -/
theorem integrated_radialClip_envelope
    (μ : Measure Ω) {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (X : Ω → E)
    (hXmeas : AEStronglyMeasurable X μ)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ) :
    (∫ ω,
        α * ‖X ω - radialClip τ (X ω)‖
          + (β / τ) * ‖radialClip τ (X ω)‖ ^ 2 ∂μ)
      ≤ K_p α β p * τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ) := by
  let C : ℝ := K_p α β p * τ ^ (1 - p)
  have hnonneg :
      0 ≤ᵐ[μ] (fun ω =>
        α * ‖X ω - radialClip τ (X ω)‖
          + (β / τ) * ‖radialClip τ (X ω)‖ ^ 2) :=
    Filter.Eventually.of_forall fun _ => by positivity
  have hright : Integrable (fun ω => C * ‖X ω‖ ^ p) μ :=
    hXp.const_mul C
  have hYmeas :
      AEStronglyMeasurable (fun ω => radialClip τ (X ω)) μ :=
    aestronglyMeasurable_radialClip hXmeas hτ
  have hleftmeas :
      AEStronglyMeasurable (fun ω =>
        α * ‖X ω - radialClip τ (X ω)‖
          + (β / τ) * ‖radialClip τ (X ω)‖ ^ 2) μ := by
    exact ((hXmeas.sub hYmeas).norm.const_mul α).add
      ((hYmeas.norm.pow 2).const_mul (β / τ))
  have hpoint :
      (fun ω =>
        α * ‖X ω - radialClip τ (X ω)‖
          + (β / τ) * ‖radialClip τ (X ω)‖ ^ 2)
        ≤ᵐ[μ] (fun ω => C * ‖X ω‖ ^ p) :=
    Filter.Eventually.of_forall fun ω => by
      dsimp [C]
      exact radialClip_envelope hα hβ hp hp2 hτ (X ω)
  have hleft :
      Integrable (fun ω =>
        α * ‖X ω - radialClip τ (X ω)‖
          + (β / τ) * ‖radialClip τ (X ω)‖ ^ 2) μ := by
    apply hright.mono hleftmeas
    filter_upwards [hnonneg, hpoint] with ω hleftω hpointω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleftω,
      abs_of_nonneg (hleftω.trans hpointω)]
    exact hpointω
  have hint := integral_mono_ae hleft hright hpoint
  simpa [C, integral_const_mul, mul_assoc] using hint

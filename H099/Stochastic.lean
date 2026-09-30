import H099.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Stochastic clipping envelope

This module begins the Hilbert-space stochastic lift.  The main theorem below
is stated with explicit integrability hypotheses; later modules discharge
those hypotheses from the `L^p` assumption.
-/

open MeasureTheory
open Real

noncomputable section

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert variance identity for a Bochner-integrable random vector with an
integrable squared norm on a probability space. -/
theorem integral_norm_sub_mean_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → H) (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ) :
    (∫ ω, ‖Y ω - ∫ z, Y z ∂μ‖ ^ 2 ∂μ)
      = (∫ ω, ‖Y ω‖ ^ 2 ∂μ) - ‖∫ z, Y z ∂μ‖ ^ 2 := by
  let b : H := ∫ z, Y z ∂μ
  have hinner : Integrable (fun ω => inner ℝ (Y ω) b) μ :=
    hY.inner_const b
  have htwoinner : Integrable (fun ω => 2 * inner ℝ (Y ω) b) μ :=
    hinner.const_mul 2
  have hsub : Integrable (fun ω => ‖Y ω‖ ^ 2 - 2 * inner ℝ (Y ω) b) μ :=
    hYsq.sub htwoinner
  change (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
    = (∫ ω, ‖Y ω‖ ^ 2 ∂μ) - ‖b‖ ^ 2
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub (integrable_const (‖b‖ ^ 2))]
  rw [integral_sub hYsq htwoinner]
  rw [integral_const_mul]
  have hinner_mean : (∫ ω, inner ℝ (Y ω) b ∂μ) = ‖b‖ ^ 2 := by
    calc
      (∫ ω, inner ℝ (Y ω) b ∂μ)
          = ∫ ω, inner ℝ b (Y ω) ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => real_inner_comm _ _
      _ = inner ℝ b (∫ ω, Y ω ∂μ) := integral_inner hY b
      _ = inner ℝ b b := by rfl
      _ = ‖b‖ ^ 2 := by
        simp
  rw [hinner_mean, integral_const]
  simp
  ring

/-- Stochastic Hilbert envelope under explicit integrability hypotheses. -/
theorem stochastic_radialClip_envelope
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (X : Ω → H)
    (hX : Integrable X μ)
    (hY : Integrable (fun ω => radialClip τ (X ω)) μ)
    (hYsq : Integrable (fun ω => ‖radialClip τ (X ω)‖ ^ 2) μ)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ) :
    let Y : Ω → H := fun ω => radialClip τ (X ω)
    let m : H := ∫ ω, X ω ∂μ
    let b : H := ∫ ω, Y ω ∂μ
    α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
      ≤ K_p α β p * τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ) := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let m : H := ∫ ω, X ω ∂μ
  let b : H := ∫ ω, Y ω ∂μ
  have hbias :
      ‖b - m‖ ≤ ∫ ω, ‖X ω - Y ω‖ ∂μ := by
    have hsubint : Integrable (fun ω => Y ω - X ω) μ := hY.sub hX
    calc
      ‖b - m‖ = ‖∫ ω, Y ω - X ω ∂μ‖ := by
        rw [integral_sub hY hX]
      _ ≤ ∫ ω, ‖Y ω - X ω‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω - Y ω‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => norm_sub_rev _ _
  have hvar :
      (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
        = (∫ ω, ‖Y ω‖ ^ 2 ∂μ) - ‖b‖ ^ 2 := by
    exact integral_norm_sub_mean_sq μ Y hY hYsq
  have hintegrated :=
    integrated_radialClip_envelope μ hα hβ hp hp2 hτ X hX.1 hXp
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ :=
    (hX.sub hY).norm
  rw [integral_add (hres.const_mul α) (hYsq.const_mul (β / τ)),
    integral_const_mul, integral_const_mul] at hintegrated
  change
    α * ‖b - m‖ + β / τ * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
      ≤ K_p α β p * τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ)
  calc
    α * ‖b - m‖ + β / τ * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
        ≤ α * (∫ ω, ‖X ω - Y ω‖ ∂μ)
            + β / τ * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) := by
          rw [hvar]
          have hβτ : 0 ≤ β / τ := div_nonneg hβ hτ.le
          nlinarith [sq_nonneg ‖b‖]
    _ ≤ K_p α β p * τ ^ (1 - p) *
          (∫ ω, ‖X ω‖ ^ p ∂μ) := by
      simpa [Y] using hintegrated

/-- The stochastic Hilbert envelope in the article's natural formulation:
the sole moment hypothesis is `X ∈ L^p`. -/
theorem stochastic_radialClip_envelope_of_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (X : Ω → H)
    (hLp : MemLp X (ENNReal.ofReal p) μ) :
    let Y : Ω → H := fun ω => radialClip τ (X ω)
    let m : H := ∫ ω, X ω ∂μ
    let b : H := ∫ ω, Y ω ∂μ
    α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
      ≤ K_p α β p * τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ) := by
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hY : Integrable (fun ω => radialClip τ (X ω)) μ :=
    integrable_radialClip hLp.1 hτ
  have hYsq : Integrable (fun ω => ‖radialClip τ (X ω)‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hLp.1 hτ
  have hXp0 :=
    hLp.integrable_norm_rpow'
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hXp0
  exact stochastic_radialClip_envelope μ hα hβ hp hp2 hτ X hX hY hYsq hXp

import H099.Deterministic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurability and integrability of radial clipping

This module records the analytic facts needed to pass the deterministic
clipping envelope under a Bochner integral.
-/

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A denominator-free representation of radial clipping, useful for
measurability and continuity. -/
lemma radialClip_eq_div_max_smul (x : E) (τ : ℝ) (hτ : 0 < τ) :
    radialClip τ x = (τ / max ‖x‖ τ) • x := by
  unfold radialClip
  by_cases h : ‖x‖ ≤ τ
  · rw [if_pos h, max_eq_right h, div_self hτ.ne', one_smul]
  · rw [if_neg h, max_eq_left (not_le.mp h).le]

/-- Radial clipping at a positive radius is continuous. -/
lemma continuous_radialClip (τ : ℝ) (hτ : 0 < τ) :
    Continuous (fun x : E => radialClip τ x) := by
  have h_eq :
      (fun x : E => radialClip τ x) =
        fun x : E => (τ / max ‖x‖ τ) • x := by
    funext x
    exact radialClip_eq_div_max_smul x τ hτ
  rw [h_eq]
  exact
    (continuous_const.div (continuous_norm.max continuous_const)
      fun x => (lt_of_lt_of_le hτ (le_max_right _ _)).ne').smul continuous_id

/-- Radial clipping preserves almost-everywhere strong measurability. -/
lemma aestronglyMeasurable_radialClip
    {μ : Measure Ω} {τ : ℝ} {X : Ω → E}
    (hX : AEStronglyMeasurable X μ) (hτ : 0 < τ) :
    AEStronglyMeasurable (fun ω => radialClip τ (X ω)) μ :=
  (continuous_radialClip τ hτ).comp_aestronglyMeasurable hX

omit [MeasurableSpace Ω] in
/-- Radial clipping with a strongly measurable random threshold and input is
strongly measurable. -/
lemma stronglyMeasurable_variable_radialClip
    {m : MeasurableSpace Ω} {X : Ω → E} {τ : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) (hτ : StronglyMeasurable[m] τ) :
    StronglyMeasurable[m] (fun ω => radialClip (τ ω) (X ω)) := by
  classical
  have hs : MeasurableSet[m] {ω | ‖X ω‖ ≤ τ ω} :=
    hX.norm.measurableSet_le hτ
  apply StronglyMeasurable.ite hs hX
  exact (hτ.div hX.norm).smul hX

omit [MeasurableSpace Ω] in
/-- The a.e.-strongly-measurable version needed for conditional
expectations. -/
lemma aestronglyMeasurable_variable_radialClip
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) {X : Ω → E} {τ : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hτ : StronglyMeasurable[m] τ) :
    AEStronglyMeasurable
      (fun ω => radialClip (τ ω) (X ω)) μ := by
  let X' : Ω → E := hX.mk X
  have hX' : StronglyMeasurable X' := hX.stronglyMeasurable_mk
  have hτ' : StronglyMeasurable τ := hτ.mono hm
  have hclip' :
      StronglyMeasurable (fun ω => radialClip (τ ω) (X' ω)) :=
    stronglyMeasurable_variable_radialClip hX' hτ'
  apply hclip'.aestronglyMeasurable.congr
  filter_upwards [hX.ae_eq_mk] with ω hω
  exact congrArg (radialClip (τ ω)) hω.symm

omit [MeasurableSpace Ω] in
/-- A real power of an a.e. positive strongly measurable function is a.e.
strongly measurable, including for negative exponents. -/
lemma aestronglyMeasurable_rpow_of_stronglyMeasurable_pos
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω) (q : ℝ) :
    AEStronglyMeasurable[m] (fun ω => (τ ω) ^ q) μ := by
  by_cases hq : 0 ≤ q
  · exact
      ((Real.continuous_rpow_const hq).comp_stronglyMeasurable hτ)
        |>.aestronglyMeasurable
  · have hnq : 0 ≤ -q := neg_nonneg.mpr (le_of_not_ge hq)
    have hpow :
        StronglyMeasurable[m] (fun ω => (τ ω) ^ (-q)) :=
      (Real.continuous_rpow_const hnq).comp_stronglyMeasurable hτ
    apply hpow.inv₀.aestronglyMeasurable.congr
    filter_upwards [hτpos] with ω hω
    calc
      ((τ ω) ^ (-q))⁻¹ = (τ ω) ^ (-(-q)) :=
        (Real.rpow_neg hω.le (-q)).symm
      _ = (τ ω) ^ q := by ring_nf

/-- On a finite measure space, a positive-radius radial clipping is
Bochner-integrable as soon as the input is a.e. strongly measurable. -/
lemma integrable_radialClip
    {μ : Measure Ω} [IsFiniteMeasure μ] {τ : ℝ} {X : Ω → E}
    (hX : AEStronglyMeasurable X μ) (hτ : 0 < τ) :
    Integrable (fun ω => radialClip τ (X ω)) μ := by
  refine Integrable.mono' (integrable_const τ)
    (aestronglyMeasurable_radialClip hX hτ) ?_
  filter_upwards with ω
  rw [norm_radialClip hτ]
  exact min_le_right _ _

/-- The squared norm of a positive-radius radial clipping is integrable on a
finite measure space. -/
lemma integrable_sq_norm_radialClip
    {μ : Measure Ω} [IsFiniteMeasure μ] {τ : ℝ} {X : Ω → E}
    (hX : AEStronglyMeasurable X μ) (hτ : 0 < τ) :
    Integrable (fun ω => ‖radialClip τ (X ω)‖ ^ 2) μ := by
  have hYmeas :=
    (aestronglyMeasurable_radialClip hX hτ).norm.pow 2
  refine Integrable.mono_nonneg (integrable_const (τ ^ 2)) hYmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) ?_
  filter_upwards with ω
  rw [norm_radialClip hτ]
  gcongr
  exact min_le_right _ _

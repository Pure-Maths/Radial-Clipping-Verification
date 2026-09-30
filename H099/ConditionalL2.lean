import H099.Stochastic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional Hilbert-space variance at the global `L²` level

This module proves the conditional variance identity used by H099 when the
clipped random vector is globally square-integrable.  The fully localized
version for an unbounded random clipping threshold is deliberately separated
from this theorem.
-/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {Ω H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Conditional Hilbert variance identity for a globally square-integrable
random vector. -/
theorem condExp_hilbert_variance_identity
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (Y : Ω → H) (hY2 : MemLp Y 2 μ) :
    μ[(fun ω => ‖Y ω - μ[Y | m] ω‖ ^ 2) | m]
      =ᵐ[μ]
        μ[(fun ω => ‖Y ω‖ ^ 2) | m]
          - (fun ω => ‖μ[Y | m] ω‖ ^ 2) := by
  let b : Ω → H := μ[Y | m]
  have hYint : Integrable Y μ := hY2.integrable one_le_two
  have hb2 : MemLp b 2 μ := MemLp.condExp one_le_two hY2
  have hbint : Integrable b μ := hb2.integrable one_le_two
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    hY2.integrable_norm_pow'
  have hbsq : Integrable (fun ω => ‖b ω‖ ^ 2) μ :=
    hb2.integrable_norm_pow'
  have hcross : Integrable (fun ω => ⟪b ω, Y ω⟫_ℝ) μ := by
    exact memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1 hb2 hY2)
  have htwocross : Integrable (fun ω => 2 * ⟪b ω, Y ω⟫_ℝ) μ :=
    hcross.const_mul 2
  have hdiff :
      Integrable (fun ω => ‖Y ω‖ ^ 2 - 2 * ⟪b ω, Y ω⟫_ℝ) μ :=
    hYsq.sub htwocross
  have hbmeas : AEStronglyMeasurable[m] b μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable
  have hpull :
      μ[(fun ω => ⟪b ω, Y ω⟫_ℝ) | m]
        =ᵐ[μ] (fun ω => ⟪b ω, b ω⟫_ℝ) := by
    have hpull0 :=
      condExp_bilin_of_aestronglyMeasurable_left
        (innerSL ℝ) hbmeas hcross hYint
    calc
      μ[(fun ω => ⟪b ω, Y ω⟫_ℝ) | m]
          =ᵐ[μ]
            μ[(fun ω => (innerSL ℝ) (b ω) (Y ω)) | m] := by
              apply condExp_congr_ae
              filter_upwards with ω
              exact (innerSL_apply_apply (𝕜 := ℝ) (b ω) (Y ω)).symm
      _ =ᵐ[μ] (fun ω => (innerSL ℝ) (b ω) (μ[Y | m] ω)) := hpull0
      _ =ᵐ[μ] (fun ω => ⟪b ω, b ω⟫_ℝ) := by
        filter_upwards with ω
        rw [innerSL_apply_apply]
  have htwopull :
      μ[(fun ω => 2 * ⟪b ω, Y ω⟫_ℝ) | m]
        =ᵐ[μ] (fun ω => 2 * ⟪b ω, b ω⟫_ℝ) := by
    have hsmul :=
      condExp_smul (μ := μ) (2 : ℝ)
        (fun ω => ⟪b ω, Y ω⟫_ℝ) m
    have hin :
        (2 : ℝ) • (fun ω => ⟪b ω, Y ω⟫_ℝ)
          = (fun ω => 2 * ⟪b ω, Y ω⟫_ℝ) := by
      ext ω
      simp
    have hout :
        (2 : ℝ) • μ[(fun ω => ⟪b ω, Y ω⟫_ℝ) | m]
          = (fun ω => 2 * μ[(fun ω => ⟪b ω, Y ω⟫_ℝ) | m] ω) := by
      ext ω
      simp
    rw [hin, hout] at hsmul
    have hsmul' :
        μ[(fun ω => 2 * ⟪b ω, Y ω⟫_ℝ) | m]
          =ᵐ[μ]
            (fun ω => 2 * μ[(fun ω => ⟪b ω, Y ω⟫_ℝ) | m] ω) :=
      hsmul
    filter_upwards [hsmul', hpull] with ω hsmulω hpullω
    simpa using hsmulω.trans (congrArg (fun z : ℝ => 2 * z) hpullω)
  have hbself :
      μ[(fun ω => ‖b ω‖ ^ 2) | m]
        = (fun ω => ‖b ω‖ ^ 2) := by
    exact condExp_of_stronglyMeasurable hm
      (stronglyMeasurable_condExp.norm.pow 2) hbsq
  calc
    μ[(fun ω => ‖Y ω - μ[Y | m] ω‖ ^ 2) | m]
        =ᵐ[μ]
          μ[(fun ω =>
            (‖Y ω‖ ^ 2 - 2 * ⟪b ω, Y ω⟫_ℝ) + ‖b ω‖ ^ 2) | m] := by
            apply condExp_congr_ae
            filter_upwards with ω
            simp only [b, norm_sub_sq_real]
            rw [real_inner_comm]
    _ =ᵐ[μ]
          μ[(fun ω => ‖Y ω‖ ^ 2 - 2 * ⟪b ω, Y ω⟫_ℝ) | m]
            + μ[(fun ω => ‖b ω‖ ^ 2) | m] :=
      condExp_add hdiff hbsq m
    _ =ᵐ[μ]
          (μ[(fun ω => ‖Y ω‖ ^ 2) | m]
            - μ[(fun ω => 2 * ⟪b ω, Y ω⟫_ℝ) | m])
              + μ[(fun ω => ‖b ω‖ ^ 2) | m] :=
      (condExp_sub hYsq htwocross m).add (Filter.EventuallyEq.rfl)
    _ =ᵐ[μ]
          μ[(fun ω => ‖Y ω‖ ^ 2) | m]
            - (fun ω => ‖b ω‖ ^ 2) := by
      filter_upwards [htwopull] with ω htwoω
      rw [hbself]
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [htwoω, real_inner_self_eq_norm_sq]
      ring

/-- Conditional H099 envelope for a deterministic clipping radius.  This is
the global-`L²` core of the fully localized random-threshold theorem. -/
theorem conditional_radialClip_envelope_const
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (X : Ω → H)
    (hLp : MemLp X (ENNReal.ofReal p) μ) :
    let Y : Ω → H := fun ω => radialClip τ (X ω)
    let mX : Ω → H := μ[X | m]
    let b : Ω → H := μ[Y | m]
    (fun ω =>
        α * ‖b ω - mX ω‖
          + (β / τ) * μ[(fun z => ‖Y z - b z‖ ^ 2) | m] ω)
      ≤ᵐ[μ]
        (fun ω =>
          K_p α β p * τ ^ (1 - p) *
            μ[(fun z => ‖X z‖ ^ p) | m] ω) := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let mX : Ω → H := μ[X | m]
  let b : Ω → H := μ[Y | m]
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hXp0 := hLp.integrable_norm_rpow'
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hXp0
  have hY : Integrable Y μ :=
    integrable_radialClip hLp.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hLp.1 hτ
  have hY2 : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq_norm hY.1).2 hYsq
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ :=
    (hX.sub hY).norm
  have hleft :
      Integrable (fun ω =>
        α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2) μ :=
    (hres.const_mul α).add (hYsq.const_mul (β / τ))
  let C : ℝ := K_p α β p * τ ^ (1 - p)
  have hright : Integrable (fun ω => C * ‖X ω‖ ^ p) μ :=
    hXp.const_mul C
  have hpoint :
      (fun ω => α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2)
        ≤ᵐ[μ] (fun ω => C * ‖X ω‖ ^ p) :=
    Filter.Eventually.of_forall fun ω => by
      dsimp [Y, C]
      exact radialClip_envelope hα hβ hp hp2 hτ (X ω)
  have hmono :
      μ[(fun ω => α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2) | m]
        ≤ᵐ[μ] μ[(fun ω => C * ‖X ω‖ ^ p) | m] :=
    condExp_mono hleft hright hpoint
  have hbias :
      (fun ω => ‖b ω - mX ω‖)
        ≤ᵐ[μ] μ[(fun z => ‖X z - Y z‖) | m] := by
    have hsub := condExp_sub hY hX m
    have hnorm := norm_condExp_le (μ := μ) (m := m) (Y - X)
    filter_upwards [hsub, hnorm] with ω hsubω hnormω
    have hsubω' : μ[Y - X | m] ω = b ω - mX ω := by
      simpa only [b, mX, Pi.sub_apply] using hsubω
    rw [← hsubω']
    simpa only [Pi.sub_apply, norm_sub_rev] using hnormω
  have hvar :=
    condExp_hilbert_variance_identity (μ := μ) hm Y hY2
  have hvarle :
      μ[(fun z => ‖Y z - b z‖ ^ 2) | m]
        ≤ᵐ[μ] μ[(fun z => ‖Y z‖ ^ 2) | m] := by
    filter_upwards [hvar] with ω hvarω
    rw [hvarω]
    exact sub_le_self _ (sq_nonneg _)
  have hsplit :
      μ[(fun ω => α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2) | m]
        =ᵐ[μ]
          (fun ω =>
            α * μ[(fun z => ‖X z - Y z‖) | m] ω
              + (β / τ) * μ[(fun z => ‖Y z‖ ^ 2) | m] ω) := by
    change
      μ[((fun ω => α * ‖X ω - Y ω‖) +
          (fun ω => (β / τ) * ‖Y ω‖ ^ 2)) | m]
        =ᵐ[μ]
          (fun ω =>
            α * μ[(fun z => ‖X z - Y z‖) | m] ω
              + (β / τ) * μ[(fun z => ‖Y z‖ ^ 2) | m] ω)
    have hadd :=
      condExp_add (hres.const_mul α) (hYsq.const_mul (β / τ)) m
    have hαpull :=
      condExp_smul (μ := μ) α (fun z => ‖X z - Y z‖) m
    have hβpull :=
      condExp_smul (μ := μ) (β / τ) (fun z => ‖Y z‖ ^ 2) m
    filter_upwards [hadd, hαpull, hβpull] with ω haddω hαω hβω
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using
      haddω.trans (congrArg₂ (· + ·) hαω hβω)
  have hrightpull :
      μ[(fun ω => C * ‖X ω‖ ^ p) | m]
        =ᵐ[μ] (fun ω => C * μ[(fun z => ‖X z‖ ^ p) | m] ω) := by
    have hCpull :=
      condExp_smul (μ := μ) C (fun z => ‖X z‖ ^ p) m
    change
      μ[C • (fun z => ‖X z‖ ^ p) | m]
        =ᵐ[μ] C • μ[(fun z => ‖X z‖ ^ p) | m]
    exact hCpull
  filter_upwards [hbias, hvarle, hsplit, hrightpull, hmono] with
    ω hbiasω hvarω hsplitω hrightω hmonoω
  rw [hsplitω, hrightω] at hmonoω
  have hβτ : 0 ≤ β / τ := div_nonneg hβ hτ.le
  calc
    α * ‖b ω - mX ω‖
          + β / τ * μ[(fun z => ‖Y z - b z‖ ^ 2) | m] ω
        ≤ α * μ[(fun z => ‖X z - Y z‖) | m] ω
          + β / τ * μ[(fun z => ‖Y z‖ ^ 2) | m] ω :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbiasω hα)
        (mul_le_mul_of_nonneg_left hvarω hβτ)
    _ ≤ C * μ[(fun z => ‖X z‖ ^ p) | m] ω := hmonoω
    _ = K_p α β p * τ ^ (1 - p) *
          μ[(fun z => ‖X z‖ ^ p) | m] ω := by rfl

/-- Conditional H099 envelope with a random `𝒢`-measurable threshold at the
global-`L²` level.  The two weighted integrability assumptions are exactly
what the later localization argument must discharge. -/
theorem conditional_radialClip_envelope_variable_L2
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (τ : Ω → ℝ) (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hβscale :
      AEStronglyMeasurable[m] (fun ω => β / τ ω) μ)
    (hKscale :
      AEStronglyMeasurable[m]
        (fun ω => K_p α β p * (τ ω) ^ (1 - p)) μ)
    (hY2 : MemLp (fun ω => radialClip (τ ω) (X ω)) 2 μ)
    (hweightedY :
      Integrable
        (fun ω => (β / τ ω) *
          ‖radialClip (τ ω) (X ω)‖ ^ 2) μ)
    (hweightedX :
      Integrable
        (fun ω => (K_p α β p * (τ ω) ^ (1 - p)) *
          ‖X ω‖ ^ p) μ) :
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    let mX : Ω → H := μ[X | m]
    let b : Ω → H := μ[Y | m]
    (fun ω =>
        α * ‖b ω - mX ω‖
          + (β / τ ω) *
              μ[(fun z => ‖Y z - b z‖ ^ 2) | m] ω)
      ≤ᵐ[μ]
        (fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) *
            μ[(fun z => ‖X z‖ ^ p) | m] ω) := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  let mX : Ω → H := μ[X | m]
  let b : Ω → H := μ[Y | m]
  change MemLp Y 2 μ at hY2
  change
    Integrable (fun ω => (β / τ ω) * ‖Y ω‖ ^ 2) μ
    at hweightedY
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hXp0 := hLp.integrable_norm_rpow'
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hXp0
  have hY : Integrable Y μ := hY2.integrable one_le_two
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    hY2.integrable_norm_pow'
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ :=
    (hX.sub hY).norm
  have hleft :
      Integrable (fun ω =>
        α * ‖X ω - Y ω‖ + (β / τ ω) * ‖Y ω‖ ^ 2) μ :=
    (hres.const_mul α).add hweightedY
  have hpoint :
      (fun ω => α * ‖X ω - Y ω‖ + (β / τ ω) * ‖Y ω‖ ^ 2)
        ≤ᵐ[μ]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p)) * ‖X ω‖ ^ p) := by
    filter_upwards [hτpos] with ω hτω
    dsimp [Y]
    exact radialClip_envelope hα hβ hp hp2 hτω (X ω)
  have hmono :
      μ[(fun ω =>
          α * ‖X ω - Y ω‖ + (β / τ ω) * ‖Y ω‖ ^ 2) | m]
        ≤ᵐ[μ]
          μ[(fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p)) * ‖X ω‖ ^ p) | m] :=
    condExp_mono hleft hweightedX hpoint
  have hbias :
      (fun ω => ‖b ω - mX ω‖)
        ≤ᵐ[μ] μ[(fun z => ‖X z - Y z‖) | m] := by
    have hsub := condExp_sub hY hX m
    have hnorm := norm_condExp_le (μ := μ) (m := m) (Y - X)
    filter_upwards [hsub, hnorm] with ω hsubω hnormω
    have hsubω' : μ[Y - X | m] ω = b ω - mX ω := by
      simpa only [b, mX, Pi.sub_apply] using hsubω
    rw [← hsubω']
    simpa only [Pi.sub_apply, norm_sub_rev] using hnormω
  have hvar :=
    condExp_hilbert_variance_identity (μ := μ) hm Y hY2
  have hvarle :
      μ[(fun z => ‖Y z - b z‖ ^ 2) | m]
        ≤ᵐ[μ] μ[(fun z => ‖Y z‖ ^ 2) | m] := by
    filter_upwards [hvar] with ω hvarω
    rw [hvarω]
    exact sub_le_self _ (sq_nonneg _)
  have hsplit :
      μ[(fun ω =>
          α * ‖X ω - Y ω‖ + (β / τ ω) * ‖Y ω‖ ^ 2) | m]
        =ᵐ[μ]
          (fun ω =>
            α * μ[(fun z => ‖X z - Y z‖) | m] ω
              + (β / τ ω) *
                  μ[(fun z => ‖Y z‖ ^ 2) | m] ω) := by
    change
      μ[((fun ω => α * ‖X ω - Y ω‖) +
          (fun ω => (β / τ ω) * ‖Y ω‖ ^ 2)) | m]
        =ᵐ[μ]
          (fun ω =>
            α * μ[(fun z => ‖X z - Y z‖) | m] ω
              + (β / τ ω) *
                  μ[(fun z => ‖Y z‖ ^ 2) | m] ω)
    have hadd :=
      condExp_add (hres.const_mul α) hweightedY m
    have hαpull :=
      condExp_smul (μ := μ) α (fun z => ‖X z - Y z‖) m
    have hβpull :=
      condExp_mul_of_aestronglyMeasurable_left
        hβscale hweightedY hYsq
    filter_upwards [hadd, hαpull, hβpull] with ω haddω hαω hβω
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using
      haddω.trans (congrArg₂ (· + ·) hαω hβω)
  have hrightpull :
      μ[(fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) * ‖X ω‖ ^ p) | m]
        =ᵐ[μ]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p)) *
              μ[(fun z => ‖X z‖ ^ p) | m] ω) :=
    condExp_mul_of_aestronglyMeasurable_left
      hKscale hweightedX hXp
  filter_upwards [hbias, hvarle, hsplit, hrightpull, hmono, hτpos] with
    ω hbiasω hvarω hsplitω hrightω hmonoω hτω
  rw [hsplitω, hrightω] at hmonoω
  have hβτ : 0 ≤ β / τ ω := div_nonneg hβ hτω.le
  calc
    α * ‖b ω - mX ω‖
          + (β / τ ω) *
              μ[(fun z => ‖Y z - b z‖ ^ 2) | m] ω
        ≤ α * μ[(fun z => ‖X z - Y z‖) | m] ω
          + (β / τ ω) *
              μ[(fun z => ‖Y z‖ ^ 2) | m] ω :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbiasω hα)
        (mul_le_mul_of_nonneg_left hvarω hβτ)
    _ ≤ (K_p α β p * (τ ω) ^ (1 - p)) *
          μ[(fun z => ‖X z‖ ^ p) | m] ω := hmonoω

/-- The preceding random-threshold theorem with the two conditional
measurability hypotheses discharged from strong `𝒢`-measurability and
positivity of the threshold. -/
theorem conditional_radialClip_envelope_variable_L2_of_stronglyMeasurable
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (τ : Ω → ℝ) (hτmeas : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hY2 : MemLp (fun ω => radialClip (τ ω) (X ω)) 2 μ)
    (hweightedY :
      Integrable
        (fun ω => (β / τ ω) *
          ‖radialClip (τ ω) (X ω)‖ ^ 2) μ)
    (hweightedX :
      Integrable
        (fun ω => (K_p α β p * (τ ω) ^ (1 - p)) *
          ‖X ω‖ ^ p) μ) :
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    let mX : Ω → H := μ[X | m]
    let b : Ω → H := μ[Y | m]
    (fun ω =>
        α * ‖b ω - mX ω‖
          + (β / τ ω) *
              μ[(fun z => ‖Y z - b z‖ ^ 2) | m] ω)
      ≤ᵐ[μ]
        (fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) *
            μ[(fun z => ‖X z‖ ^ p) | m] ω) := by
  have hβscaleStrong :
      StronglyMeasurable[m] (fun ω => β / τ ω) :=
    stronglyMeasurable_const.div hτmeas
  have hβscale :
      AEStronglyMeasurable[m] (fun ω => β / τ ω) μ :=
    hβscaleStrong.aestronglyMeasurable
  have hpow :
      AEStronglyMeasurable[m] (fun ω => (τ ω) ^ (1 - p)) μ :=
    aestronglyMeasurable_rpow_of_stronglyMeasurable_pos
      hτmeas hτpos (1 - p)
  have hKscale :
      AEStronglyMeasurable[m]
        (fun ω => K_p α β p * (τ ω) ^ (1 - p)) μ :=
    hpow.const_mul (K_p α β p)
  exact
    conditional_radialClip_envelope_variable_L2 μ hm
      hα hβ hp hp2 τ hτpos X hLp hβscale hKscale
      hY2 hweightedY hweightedX

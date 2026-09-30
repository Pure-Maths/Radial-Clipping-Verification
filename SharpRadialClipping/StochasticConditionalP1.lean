import SharpRadialClipping.ConditionalExtended
import SharpRadialClipping.DeterministicP1

/-! The `p = 1` endpoint of the stochastic and conditional clipping envelopes. -/

open MeasureTheory Real
open scoped ENNReal

noncomputable section

variable {Ω H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1 at `p=1`, with its exact first-moment hypothesis. -/
theorem stochastic_radialClip_envelope_p1
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (X : Ω → H) (hX : Integrable X μ) :
    let Y : Ω → H := fun ω => radialClip τ (X ω)
    let m : H := ∫ ω, X ω ∂μ
    let b : H := ∫ ω, Y ω ∂μ
    α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
      ≤ K_p α β 1 * τ ^ (1 - (1 : ℝ)) * (∫ ω, ‖X ω‖ ^ (1 : ℝ) ∂μ) := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let m : H := ∫ ω, X ω ∂μ
  let b : H := ∫ ω, Y ω ∂μ
  have hY : Integrable Y μ := integrable_radialClip hX.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hX.1 hτ
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ :=
    (hX.sub hY).norm
  have hbias : ‖b - m‖ ≤ ∫ ω, ‖X ω - Y ω‖ ∂μ := by
    calc
      ‖b - m‖ = ‖∫ ω, Y ω - X ω ∂μ‖ := by
        rw [integral_sub hY hX]
      _ ≤ ∫ ω, ‖Y ω - X ω‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω - Y ω‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => norm_sub_rev _ _
  have hvar := integral_norm_sub_mean_sq μ Y hY hYsq
  have hpoint : ∀ ω,
      α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2
        ≤ K_p α β 1 * ‖X ω‖ := by
    intro ω
    simpa [Y] using radialClip_envelope_p1_article hα hβ hτ (X ω)
  have hleft : Integrable
      (fun ω => α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2) μ :=
    (hres.const_mul α).add (hYsq.const_mul (β / τ))
  have hright : Integrable (fun ω => K_p α β 1 * ‖X ω‖) μ :=
    hX.norm.const_mul _
  have hint := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall hpoint)
  rw [integral_add (hres.const_mul α) (hYsq.const_mul (β / τ)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have hβτ : 0 ≤ β / τ := div_nonneg hβ hτ.le
  have hvarle :
      ∫ ω, ‖Y ω - b‖ ^ 2 ∂μ ≤ ∫ ω, ‖Y ω‖ ^ 2 ∂μ := by
    rw [hvar]
    exact sub_le_self _ (sq_nonneg _)
  have hcalc :
      α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)
        ≤ K_p α β 1 * (∫ ω, ‖X ω‖ ∂μ) := by
    calc
      _ ≤ α * (∫ ω, ‖X ω - Y ω‖ ∂μ)
            + (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) :=
        add_le_add (mul_le_mul_of_nonneg_left hbias hα)
          (mul_le_mul_of_nonneg_left hvarle hβτ)
      _ ≤ K_p α β 1 * (∫ ω, ‖X ω‖ ∂μ) := hint
  simpa using hcalc

theorem conditional_radialClip_envelope_variable_L2_p1
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : p = 1)
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
  subst p
  dsimp only
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  let mX : Ω → H := μ[X | m]
  let b : Ω → H := μ[Y | m]
  change MemLp Y 2 μ at hY2
  change
    Integrable (fun ω => (β / τ ω) * ‖Y ω‖ ^ 2) μ
    at hweightedY
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr le_rfl)
  have hXp0 := hLp.integrable_norm_rpow'
  have hp0 : 0 ≤ (1 : ℝ) := zero_le_one
  have hXp : Integrable (fun ω => ‖X ω‖ ^ (1 : ℝ)) μ := by
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
            (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) * ‖X ω‖ ^ (1 : ℝ)) := by
    filter_upwards [hτpos] with ω hτω
    dsimp [Y]
    exact radialClip_envelope_p1_article hα hβ hτω (X ω)
  have hmono :
      μ[(fun ω =>
          α * ‖X ω - Y ω‖ + (β / τ ω) * ‖Y ω‖ ^ 2) | m]
        ≤ᵐ[μ]
          μ[(fun ω =>
            (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) * ‖X ω‖ ^ (1 : ℝ)) | m] :=
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
          (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) * ‖X ω‖ ^ (1 : ℝ)) | m]
        =ᵐ[μ]
          (fun ω =>
            (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) *
              μ[(fun z => ‖X z‖ ^ (1 : ℝ)) | m] ω) :=
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
    _ ≤ (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) *
          μ[(fun z => ‖X z‖ ^ (1 : ℝ)) | m] ω := hmonoω

theorem conditional_radialClip_envelope_on_thresholdBand_p1
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : p = 1)
    (τ : Ω → ℝ) (hτ : StronglyMeasurable[m] τ)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (n : ℕ) :
    let A := thresholdBand τ n
    let μA := μ.restrict A
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    let mX : Ω → H := μA[X | m]
    let b : Ω → H := μA[Y | m]
    (fun ω =>
        α * ‖b ω - mX ω‖
          + (β / τ ω) *
              μA[(fun z => ‖Y z - b z‖ ^ 2) | m] ω)
      ≤ᵐ[μA]
        (fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) *
            μA[(fun z => ‖X z‖ ^ p) | m] ω) := by
  subst p
  dsimp only
  let A := thresholdBand τ n
  have hA : MeasurableSet[mΩ] A :=
    hm _ (measurableSet_thresholdBand hτ n)
  have hτposA : ∀ᵐ ω ∂μ.restrict A, 0 < τ ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    exact (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
  have hβscaleA :
      AEStronglyMeasurable[m] (fun ω => β / τ ω) (μ.restrict A) :=
    (stronglyMeasurable_const.div hτ).aestronglyMeasurable
  have hpowA :
      AEStronglyMeasurable[m] (fun ω => (τ ω) ^ (1 - (1 : ℝ)))
        (μ.restrict A) :=
    aestronglyMeasurable_rpow_of_stronglyMeasurable_pos
      hτ hτposA (1 - (1 : ℝ))
  have hKscaleA :
      AEStronglyMeasurable[m]
        (fun ω => K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ)))
        (μ.restrict A) :=
    hpowA.const_mul (K_p α β (1 : ℝ))
  have hLpA :
      MemLp X (ENNReal.ofReal (1 : ℝ)) (μ.restrict A) :=
    hLp.restrict A
  have hY2A :
      MemLp (fun ω => radialClip (τ ω) (X ω)) 2
        (μ.restrict A) :=
    memLp_two_variable_radialClip_restrict_thresholdBand
      hm hτ hLp.1 n
  have hweightedYA :
      Integrable
        (fun ω => (β / τ ω) *
          ‖radialClip (τ ω) (X ω)‖ ^ 2)
        (μ.restrict A) :=
    integrable_weightedY_restrict_thresholdBand
      hm hτ hLp.1 β n
  have hweightedXA :
      Integrable
        (fun ω =>
          (K_p α β (1 : ℝ) * (τ ω) ^ (1 - (1 : ℝ))) * ‖X ω‖ ^ (1 : ℝ))
        (μ.restrict A) := by
    have hXnorm : Integrable (fun ω => ‖X ω‖) (μ.restrict A) :=
      (hLpA.integrable (ENNReal.one_le_ofReal.mpr le_rfl)).norm
    simpa using (hXnorm.const_mul (K_p α β 1))
  exact
    conditional_radialClip_envelope_variable_L2_p1
      (μ.restrict A) hm hα hβ rfl τ hτposA X hLpA
      hβscaleA hKscaleA hY2A hweightedYA hweightedXA

theorem conditional_radialClip_envelope_variable_full_p1
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : p = 1)
    (τ : Ω → ℝ) (hτmeas : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ) :
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    (∀ᵐ ω ∂μ, condVarENN (m := m) μ Y ω ≠ ∞)
      ∧
      ((fun ω =>
          α * ‖μ[Y | m] ω - μ[X | m] ω‖
            + (β / τ ω) * condVarReal (m := m) μ Y ω)
        ≤ᵐ[μ]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p))
              * μ[(fun z => ‖X z‖ ^ p) | m] ω)) := by
  subst p
  dsimp only
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr le_rfl)
  have hYmeas : AEStronglyMeasurable Y μ := by
    exact aestronglyMeasurable_variable_radialClip hm hLp.1 hτmeas
  have hY : Integrable Y μ := by
    apply hX.mono hYmeas
    filter_upwards [hτpos] with ω hτω
    dsimp [Y]
    rw [norm_radialClip hτω]
    exact min_le_left _ _
  have hp0 : 0 ≤ (1 : ℝ) := zero_le_one
  have hXp : Integrable (fun ω => ‖X ω‖ ^ (1 : ℝ)) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hLp.integrable_norm_rpow'
  let sets : ℕ → Set Ω := thresholdBand τ
  have hsets : ∀ n, MeasurableSet[m] (sets n) :=
    fun n => measurableSet_thresholdBand hτmeas n
  have hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n := by
    simpa [sets] using ae_iUnion_thresholdBand hτpos
  have henergy : ∀ n,
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict (sets n)) := by
    intro n
    let A := sets n
    have hY2A : MemLp Y 2 (μ.restrict A) := by
      simpa [Y, A, sets] using
        memLp_two_variable_radialClip_restrict_thresholdBand
          (μ := μ) hm hτmeas hLp.1 n
    have hb2A :
        MemLp ((μ.restrict A)[Y | m]) 2 (μ.restrict A) :=
      MemLp.condExp one_le_two hY2A
    have hrestrict :
        (μ.restrict A)[Y | m] =ᵐ[μ.restrict A] μ[Y | m] :=
      condExp_restrict_ae_eq_restrict hm (hsets n) hY
    have hb2global : MemLp (μ[Y | m]) 2 (μ.restrict A) :=
      MemLp.ae_eq hrestrict hb2A
    exact (hY2A.sub hb2global).integrable_norm_pow'
  apply fullConditionalReal_of_local
    (μ := μ) hm τ X Y sets hsets hcover henergy
  intro n
  let A := sets n
  have hband :=
    conditional_radialClip_envelope_on_thresholdBand_p1
      μ hm hα hβ rfl τ hτmeas X hLp n
  have hXrestrict :
      (μ.restrict A)[X | m] =ᵐ[μ.restrict A] μ[X | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hX
  have hYrestrict :
      (μ.restrict A)[Y | m] =ᵐ[μ.restrict A] μ[Y | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hY
  have hXprestrict :
      (μ.restrict A)[(fun z => ‖X z‖ ^ (1 : ℝ)) | m]
        =ᵐ[μ.restrict A]
          μ[(fun z => ‖X z‖ ^ (1 : ℝ)) | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hXp
  have hcenter :
      (μ.restrict A)[
          (fun z =>
            ‖Y z - (μ.restrict A)[Y | m] z‖ ^ 2) | m]
        =ᵐ[μ.restrict A]
          (μ.restrict A)[
            (fun z => ‖Y z - μ[Y | m] z‖ ^ 2) | m] := by
    apply condExp_congr_ae
    filter_upwards [hYrestrict] with z hz
    rw [hz]
  filter_upwards [hband, hXrestrict, hYrestrict, hXprestrict, hcenter] with
    ω hbandω hXω hYω hXpω hcenterω
  simp only [A, sets, Y] at hXω hYω hXpω hcenterω ⊢
  rw [hXω, hYω, hXpω, hcenterω] at hbandω
  simpa only using hbandω

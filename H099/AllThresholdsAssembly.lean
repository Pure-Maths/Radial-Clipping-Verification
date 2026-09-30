import H099.AllThresholdsQuantization

/-!
# Radial domination for the finite approximants

Every spatial realization of a radially rounded source inherits a uniform
tail bound from the unrounded source.  This is the compactness input for the
final all-thresholds passage.
-/

open MeasureTheory Filter Topology

noncomputable section

local instance : MeasurableSpace H099R3 := borel H099R3
local instance : BorelSpace H099R3 := ⟨rfl⟩

/-- A spatial probability law with the same radii as the `n`th radial
quantization is uniformly dominated, in norm tails, by the source law. -/
theorem quantized_radial_law_tail_le_source
    {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (ν : ProbabilityMeasure E) (n : ℕ)
    (hradial : Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E) =
      Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω))
    (R : ℝ) :
    (ν : Measure E) {z | R < ‖z‖} ≤
      (μ : Measure Ω) {ω | R < ‖X ω‖} := by
  have hleft : (ν : Measure E) {z | R < ‖z‖} =
      (Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E)) (Set.Ioi R) := by
    rw [Measure.map_apply measurable_norm measurableSet_Ioi]
    rfl
  have hright : (Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖)
      (μ : Measure Ω)) (Set.Ioi R) =
      (μ : Measure Ω) {ω | R < radialGrid n ‖X ω‖} := by
    have hm : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖) :=
      (measurable_radialGrid n).comp hXm.norm
    rw [Measure.map_apply hm measurableSet_Ioi]
    rfl
  rw [hleft, hradial, hright]
  apply measure_mono
  intro ω hω
  exact lt_of_lt_of_le hω (radialGrid_le n (norm_nonneg (X ω)))

/-- Any sequence of three-dimensional realizations of the quantized radial
laws has a single weakly convergent subsequence. -/
theorem exists_weak_limit_of_quantized_radial_laws
    {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (νs : ℕ → ProbabilityMeasure E)
    (hradial : ∀ n, Measure.map (fun z : E ↦ ‖z‖) (νs n : Measure E) =
      Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω)) :
    ∃ ν : ProbabilityMeasure E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (nhds ν) := by
  let ρ : Measure ℝ := Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω)
  have hρprob : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map hXm.norm.aemeasurable
  letI : IsProbabilityMeasure ρ := hρprob
  apply exists_weakly_convergent_subseq_of_radial_tail_domination ρ νs
  intro n R hR
  calc
    (νs n : Measure E) {z | R < ‖z‖} ≤
        (μ : Measure Ω) {ω | R < ‖X ω‖} :=
      quantized_radial_law_tail_le_source μ X hXm (νs n) n (hradial n) R
    _ = ρ (Set.Ioi R) := by
      rw [Measure.map_apply hXm.norm measurableSet_Ioi]
      rfl

/-- The extracted law has exactly the original radial distribution, not just
the distribution of one finite approximation. -/
theorem radial_law_of_quantized_weak_limit
    {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (νs : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak : Tendsto (νs ∘ φ) atTop (nhds ν))
    (hradial : ∀ n, Measure.map (fun z : E ↦ ‖z‖) (νs n : Measure E) =
      Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω)) :
    Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E) =
      Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω) := by
  let ρn : ℕ → ProbabilityMeasure ℝ := fun n ↦
    ⟨Measure.map (fun ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω),
      Measure.isProbabilityMeasure_map
        ((measurable_radialGrid n).comp hXm.norm).aemeasurable⟩
  let ρ : ProbabilityMeasure ℝ :=
    ⟨Measure.map (fun ω ↦ ‖X ω‖) (μ : Measure Ω),
      Measure.isProbabilityMeasure_map hXm.norm.aemeasurable⟩
  have hρ : Tendsto ρn atTop (nhds ρ) :=
    tendsto_radial_law_radialQuantized μ X hXm
  have hρsub : Tendsto (ρn ∘ φ) atTop (nhds ρ) :=
    hρ.comp hφ.tendsto_atTop
  have hmaps : ∀ n, (νs (φ n)).map continuous_norm.measurable.aemeasurable =
      ρn (φ n) := by
    intro n
    apply Subtype.ext
    exact hradial (φ n)
  have hradialTendsto : Tendsto
      (fun n ↦ (νs (φ n)).map continuous_norm.measurable.aemeasurable)
      atTop (nhds ρ) := by
    convert hρsub using 1
    funext n
    exact hmaps n
  have hlim := radial_law_of_weak_limit_of_radial_law_tendsto
    ρ (νs ∘ φ) ν hweak hradialTendsto
  exact congrArg (fun θ : ProbabilityMeasure ℝ ↦ (θ : Measure ℝ)) hlim

/-- Integrability of the radius transfers to an arbitrary spatial law with
that radial distribution. -/
theorem integrable_spatial_id_of_integrable_radial_law
    {H : Type*} [NormedAddCommGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ν : ProbabilityMeasure H) (ρ : Measure ℝ)
    (hradial : Measure.map (fun z : H ↦ ‖z‖) (ν : Measure H) = ρ)
    (hρ : Integrable (fun r : ℝ ↦ r) ρ) :
    Integrable (fun z : H ↦ z) (ν : Measure H) := by
  apply (integrable_norm_iff measurable_id.aestronglyMeasurable).mp
  have hmap : Integrable (fun r : ℝ ↦ r)
      (Measure.map (fun z : H ↦ ‖z‖) (ν : Measure H)) := by
    rw [hradial]
    exact hρ
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    measurable_norm.aemeasurable).mp hmap

/-- Integrability of each quantized radial law follows from the original
first moment. -/
theorem integrable_quantized_radial_law
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω)) (n : ℕ) :
    Integrable (fun r : ℝ ↦ r)
      (Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω)) := by
  have hm : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖) :=
    (measurable_radialGrid n).comp hXm.norm
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    hm.aemeasurable).mpr
  convert (integrable_radialQuantized_comp (μ : Measure Ω) X hXm hX n).norm using 1
  funext ω
  exact (norm_radialQuantized n (X ω)).symm

/-- The expected excess beyond every positive threshold of a quantized
realization is bounded by that of the original source. -/
theorem quantized_radial_excess_le_source
    {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (ν : ProbabilityMeasure E) (n : ℕ)
    (hradial : Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E) =
      Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω))
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ z, max (‖z‖ - τ) 0 ∂(ν : Measure E)) ≤
      ∫ ω, max (‖X ω‖ - τ) 0 ∂(μ : Measure Ω) := by
  have hexcess : ∀ r : ℝ, 0 ≤ r → 0 ≤ max (r - τ) 0 ∧ max (r - τ) 0 ≤ r := by
    intro r hr
    constructor
    · exact le_max_right _ _
    · exact max_le (by linarith) hr
  have hsourceInt : Integrable (fun ω ↦ max (‖X ω‖ - τ) 0)
      (μ : Measure Ω) := by
    apply hX.norm.mono' (by fun_prop)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hexcess _ (norm_nonneg (X ω))).1]
    exact (hexcess _ (norm_nonneg (X ω))).2
  have hquantInt : Integrable (fun ω ↦ max (radialGrid n ‖X ω‖ - τ) 0)
      (μ : Measure Ω) := by
    have hXn := (integrable_radialQuantized_comp (μ : Measure Ω) X hXm hX n).norm
    have hm : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖) :=
      (measurable_radialGrid n).comp hXm.norm
    apply hXn.mono' (by exact (hm.sub measurable_const).max measurable_const |>.aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hexcess _ (radialGrid_nonneg n ‖X ω‖)).1]
    simpa [norm_radialQuantized] using
      (hexcess _ (radialGrid_nonneg n ‖X ω‖)).2
  have hpoint : ∀ ω, max (radialGrid n ‖X ω‖ - τ) 0 ≤
      max (‖X ω‖ - τ) 0 := by
    intro ω
    exact max_le_max_right 0 (sub_le_sub_right
      (radialGrid_le n (norm_nonneg (X ω))) τ)
  have hmono : (∫ ω, max (radialGrid n ‖X ω‖ - τ) 0 ∂(μ : Measure Ω)) ≤
      ∫ ω, max (‖X ω‖ - τ) 0 ∂(μ : Measure Ω) :=
    integral_mono hquantInt hsourceInt hpoint
  have hf : AEStronglyMeasurable (fun r : ℝ ↦ max (r - τ) 0)
      (Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E)) := by
    fun_prop
  calc
    (∫ z, max (‖z‖ - τ) 0 ∂(ν : Measure E)) =
        ∫ r, max (r - τ) 0 ∂Measure.map (fun z : E ↦ ‖z‖) (ν : Measure E) := by
      rw [integral_map measurable_norm.aemeasurable hf]
    _ = ∫ ω, max (radialGrid n ‖X ω‖ - τ) 0 ∂(μ : Measure Ω) := by
      rw [hradial]
      have hm : AEMeasurable (fun ω : Ω ↦ radialGrid n ‖X ω‖)
          (μ : Measure Ω) := ((measurable_radialGrid n).comp hXm.norm).aemeasurable
      rw [integral_map hm (by fun_prop)]
    _ ≤ _ := hmono

/-- The complete compactness/limit passage.  Its only geometric input is a
three-dimensional realization for each finite radial quantization.  The
finite-support construction is deliberately left as an explicit hypothesis
here, rather than silently assumed. -/
theorem exists_all_thresholds_realization_of_quantized_realizations
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (νs : ℕ → ProbabilityMeasure H099R3)
    (hradial : ∀ n, Measure.map (fun z : H099R3 ↦ ‖z‖)
      (νs n : Measure H099R3) =
      Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω))
    (hbias : ∀ n τ, 0 < τ →
      ‖(∫ ω, radialClip τ (radialQuantized n (X ω)) ∂(μ : Measure Ω)) -
          ∫ ω, radialQuantized n (X ω) ∂(μ : Measure Ω)‖ =
        ‖(∫ z, radialClip τ z ∂(νs n : Measure H099R3)) -
          ∫ z, z ∂(νs n : Measure H099R3)‖)
    (henergy : ∀ n τ, 0 < τ →
      (∫ ω, ‖radialClip τ (radialQuantized n (X ω)) -
        ∫ ξ, radialClip τ (radialQuantized n (X ξ)) ∂(μ : Measure Ω)‖ ^ 2
          ∂(μ : Measure Ω)) =
      (∫ z, ‖radialClip τ z -
        ∫ y, radialClip τ y ∂(νs n : Measure H099R3)‖ ^ 2
          ∂(νs n : Measure H099R3))) :
    ∃ ν : ProbabilityMeasure H099R3,
      Measure.map (fun z : H099R3 ↦ ‖z‖) (ν : Measure H099R3) =
        Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω) ∧
      ∀ τ : ℝ, 0 < τ →
        ‖(∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)) -
          ∫ ω, X ω ∂(μ : Measure Ω)‖ =
          ‖(∫ z, radialClip τ z ∂(ν : Measure H099R3)) -
            ∫ z, z ∂(ν : Measure H099R3)‖ ∧
        (∫ ω, ‖radialClip τ (X ω) -
          ∫ ξ, radialClip τ (X ξ) ∂(μ : Measure Ω)‖ ^ 2
            ∂(μ : Measure Ω)) =
          (∫ z, ‖radialClip τ z -
            ∫ y, radialClip τ y ∂(ν : Measure H099R3)‖ ^ 2
              ∂(ν : Measure H099R3)) := by
  obtain ⟨ν, φ, hφ, hweak⟩ :=
    exists_weak_limit_of_quantized_radial_laws μ X hXm νs hradial
  have hradialLim := radial_law_of_quantized_weak_limit μ X hXm νs ν φ hφ hweak hradial
  let ρ : Measure ℝ := Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω)
  have hρInt : Integrable (fun r : ℝ ↦ r) ρ := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable
      hXm.norm.aemeasurable).mpr
    exact hX.norm
  have hId (n : ℕ) : Integrable (fun z : H099R3 ↦ z)
      (νs n : Measure H099R3) := by
    apply integrable_spatial_id_of_integrable_radial_law (νs n)
      (Measure.map (fun ω : Ω ↦ radialGrid n ‖X ω‖) (μ : Measure Ω))
    · exact hradial n
    · exact integrable_quantized_radial_law μ X hXm hX n
  have hIdLim : Integrable (fun z : H099R3 ↦ z) (ν : Measure H099R3) :=
    integrable_spatial_id_of_integrable_radial_law ν ρ hradialLim hρInt
  have hsourceExcess (τ : ℝ) :
      (∫ ω, max (‖X ω‖ - τ) 0 ∂(μ : Measure Ω)) =
        ∫ r, max (r - τ) 0 ∂ρ := by
    rw [integral_map hXm.norm.aemeasurable (by fun_prop)]
  have hdom (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
      (∫ z, max (‖z‖ - τ) 0 ∂(νs (φ n) : Measure H099R3)) ≤
        ∫ r, max (r - τ) 0 ∂ρ := by
    rw [← hsourceExcess]
    exact quantized_radial_excess_le_source μ X hXm hX (νs (φ n)) (φ n)
      (hradial (φ n)) τ hτ
  have hmean := tendsto_integral_id_of_weak_of_radial_tail_domination
    (νs ∘ φ) ν ρ hρInt hweak (fun n ↦ hId (φ n)) hIdLim
    hdom hradialLim
  have hconv := all_thresholds_bias_energy_of_weak_limit
    (νs ∘ φ) ν hweak hmean
    (fun τ ↦ ‖(∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)) -
      ∫ ω, X ω ∂(μ : Measure Ω)‖)
    (fun τ ↦ ∫ ω, ‖radialClip τ (X ω) -
      ∫ ξ, radialClip τ (X ξ) ∂(μ : Measure Ω)‖ ^ 2
        ∂(μ : Measure Ω))
    (fun n τ ↦ ‖(∫ ω, radialClip τ (radialQuantized (φ n) (X ω))
      ∂(μ : Measure Ω)) -
        ∫ ω, radialQuantized (φ n) (X ω) ∂(μ : Measure Ω)‖)
    (fun n τ ↦ ∫ ω, ‖radialClip τ (radialQuantized (φ n) (X ω)) -
      ∫ ξ, radialClip τ (radialQuantized (φ n) (X ξ))
        ∂(μ : Measure Ω)‖ ^ 2 ∂(μ : Measure Ω))
    (by intro τ hτ; exact (tendsto_bias_radialQuantized
      (μ : Measure Ω) X hXm hX hτ).comp hφ.tendsto_atTop)
    (by intro τ hτ; exact (tendsto_centered_energy_radialQuantized
      (μ : Measure Ω) X hXm hX hτ).comp hφ.tendsto_atTop)
    (by intro n τ hτ; exact hbias (φ n) τ hτ)
    (by intro n τ hτ; exact henergy (φ n) τ hτ)
  exact ⟨ν, hradialLim, hconv⟩

end

import H099.Sharpness

/-!
# Admissible random vectors and their bias--energy coordinates

This small interface packages an arbitrary probability space and an
`L^p`-integrable Hilbert-valued random vector. It is shared by the geometric
support and the `p = 1` attainable-set developments.
-/

open MeasureTheory

universe u v

noncomputable section

/-- An admissible random vector with finite positive `p`th norm moment. -/
structure RandomVectorLaw (H : Type v)
    [MeasurableSpace H] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (p : ℝ) where
  Ω : Type u
  mΩ : MeasurableSpace Ω
  μ : @Measure Ω mΩ
  probability : @IsProbabilityMeasure Ω mΩ μ
  X : Ω → H
  memLp : @MemLp Ω H mΩ _ _ X (ENNReal.ofReal p) μ
  moment_pos :
    0 < @integral Ω ℝ _ _ mΩ μ (fun ω => ‖X ω‖ ^ p)

/-- The normalized coordinates `(energy, bias)` of an admissible law. -/
def RandomVectorLaw.biasEnergyPair
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {p : ℝ} (law : RandomVectorLaw H p) (τ : ℝ) : ℝ × ℝ := by
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  exact (stochasticClippingRatio law.μ 0 1 p τ law.X,
    stochasticClippingRatio law.μ 1 0 p τ law.X)

/-- Lift a finite `Bool` law to any sample-space universe without changing
its probability law or moment. This lets finite extremizers inhabit the
universe-polymorphic attainable set. -/
def RandomVectorLaw.liftBool
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {p : ℝ} (law : RandomVectorLaw.{0, v} H p) :
    RandomVectorLaw.{u, v} H p := by
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  let e : law.Ω ≃ᵐ ULift.{u, 0} law.Ω := (MeasurableEquiv.ulift).symm
  let μ' : Measure (ULift.{u, 0} law.Ω) := law.μ.map e
  haveI : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  let X' : ULift.{u, 0} law.Ω → H := fun x => law.X (e.symm x)
  refine
    { Ω := ULift.{u, 0} law.Ω
      mΩ := inferInstance
      μ := μ'
      probability := inferInstance
      X := X'
      memLp := ?_
      moment_pos := ?_ }
  · apply (e.memLp_map_measure_iff).2
    simpa [X', Function.comp_def] using law.memLp
  rw [MeasureTheory.integral_map_equiv e
    (fun x : ULift.{u, 0} law.Ω => ‖law.X (e.symm x)‖ ^ p)]
  simpa [X', e] using law.moment_pos

/-- Normalized clipping ratios are invariant under a measurable equivalence of
sample spaces equipped with the transported probability measure. -/
lemma stochasticClippingRatio_map_equiv
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace H] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : Ω ≃ᵐ Ω') (μ : Measure Ω)
    [IsProbabilityMeasure μ] {α β p τ : ℝ} (X : Ω → H) :
    stochasticClippingRatio (μ.map e) α β p τ (fun y => X (e.symm y)) =
      stochasticClippingRatio μ α β p τ X := by
  letI : IsProbabilityMeasure (μ.map e) :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  simp [stochasticClippingRatio, MeasureTheory.integral_map_equiv]

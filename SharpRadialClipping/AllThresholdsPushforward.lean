import SharpRadialClipping.AllThresholdsFiniteShell

/-!
# Spatial push-forward of a finite signed-atom sample

The signed-atom construction is initially a random vector on a finite sample
space.  The limiting argument uses probability measures on `ℝ³`; these lemmas
transport the relevant integrals under the push-forward by that vector.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

local instance : MeasurableSpace SharpRadialClippingR3 := borel SharpRadialClippingR3
local instance : BorelSpace SharpRadialClippingR3 := ⟨rfl⟩

def spatialPushforward
    {A : Type*} [MeasurableSpace A]
    (ν : ProbabilityMeasure A) (Z : A → SharpRadialClippingR3) (hZm : Measurable Z) :
    ProbabilityMeasure SharpRadialClippingR3 := ν.map hZm.aemeasurable

theorem integral_spatialPushforward
    {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : ProbabilityMeasure A) (Z : A → SharpRadialClippingR3) (hZm : Measurable Z)
    (f : SharpRadialClippingR3 → E) (hf : AEStronglyMeasurable f
      (spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) :
    (∫ z, f z ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) =
      ∫ a, f (Z a) ∂(ν : Measure A) := by
  change (∫ z, f z ∂Measure.map Z (ν : Measure A)) =
    ∫ a, f (Z a) ∂(ν : Measure A)
  exact integral_map hZm.aemeasurable hf

theorem radial_law_spatialPushforward
    {A : Type*} [MeasurableSpace A]
    (ν : ProbabilityMeasure A) (Z : A → SharpRadialClippingR3) (hZm : Measurable Z) :
    Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖)
      (spatialPushforward ν Z hZm : Measure SharpRadialClippingR3) =
      Measure.map (fun a : A ↦ ‖Z a‖) (ν : Measure A) := by
  change Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖)
      (Measure.map Z (ν : Measure A)) =
      Measure.map (fun a : A ↦ ‖Z a‖) (ν : Measure A)
  rw [Measure.map_map measurable_norm hZm]
  rfl

/-- Passing from a random vector on its original sample space to its law
on Euclidean three-space preserves clipping bias and centered energy at
every positive threshold. -/
theorem bias_energy_spatialPushforward
    {A : Type*} [MeasurableSpace A]
    (ν : ProbabilityMeasure A) (Z : A → SharpRadialClippingR3) (hZm : Measurable Z) :
    ∀ τ : ℝ, 0 < τ →
      ‖(∫ z, radialClip τ z ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) -
          ∫ z, z ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)‖ =
        ‖(∫ a, radialClip τ (Z a) ∂(ν : Measure A)) -
          ∫ a, Z a ∂(ν : Measure A)‖ ∧
      (∫ z, ‖radialClip τ z -
          ∫ y, radialClip τ y ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)‖ ^ 2
            ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) =
        ∫ a, ‖radialClip τ (Z a) -
          ∫ b, radialClip τ (Z b) ∂(ν : Measure A)‖ ^ 2
            ∂(ν : Measure A) := by
  intro τ hτ
  have hId :
      (∫ z, z ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) =
        ∫ a, Z a ∂(ν : Measure A) :=
    integral_spatialPushforward ν Z hZm _ measurable_id.aestronglyMeasurable
  have hClip :
      (∫ z, radialClip τ z ∂(spatialPushforward ν Z hZm : Measure SharpRadialClippingR3)) =
        ∫ a, radialClip τ (Z a) ∂(ν : Measure A) :=
    integral_spatialPushforward ν Z hZm _
      (continuous_radialClip τ hτ).measurable.aestronglyMeasurable
  constructor
  · rw [hId, hClip]
  · rw [hClip]
    apply integral_spatialPushforward ν Z hZm
    have hc : Continuous (fun z : SharpRadialClippingR3 ↦
        ‖radialClip τ z - ∫ b, radialClip τ (Z b) ∂(ν : Measure A)‖ ^ 2) := by
      exact (((continuous_radialClip τ hτ).sub continuous_const).norm).pow 2
    exact hc.measurable.aestronglyMeasurable

/-- A finite signed-atom random vector whose residual-path geometry has
already been established gives a genuine probability law on `ℝ³`.  This
is the exact output shape required by the compactness theorem. -/
theorem exists_spatial_signedAtom_law_of_geometry
    {Ω H ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace (Option (ι × Bool))]
    [MeasurableSingletonClass (Option (ι × Bool))]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hX : Integrable X (μ : Measure Ω))
    (q0 : ℝ) (q r : ι → ℝ) (v e : ι → SharpRadialClippingR3)
    (hq0 : 0 ≤ q0) (hv : ∀ i, ‖v i‖ ≤ q i)
    (hsum : q0 + ∑ i, q i = 1)
    (hr : ∀ i, 0 < r i) (he : ∀ i, ‖e i‖ = 1)
    (hve : ∀ i, ‖v i‖ • e i = v i)
    (hXtest : ∀ f : ℝ →ᵇ ℝ,
      (∫ ω, f ‖X ω‖ ∂(μ : Measure Ω)) = q0 * f 0 +
        ∑ i, q i * f (r i))
    (hresidualGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖∑ i, max (r i - τ) 0 • v i‖)
    (hclippedGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖(∑ i, r i • v i) - ∑ i, max (r i - τ) 0 • v i‖) :
    ∃ ν : ProbabilityMeasure SharpRadialClippingR3,
      Measure.map (fun ω ↦ ‖X ω‖) (μ : Measure Ω) =
        Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) ∧
      ∀ τ : ℝ, 0 < τ →
        ‖(∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)) -
          ∫ ω, X ω ∂(μ : Measure Ω)‖ =
          ‖(∫ z, radialClip τ z ∂(ν : Measure SharpRadialClippingR3)) -
            ∫ z, z ∂(ν : Measure SharpRadialClippingR3)‖ ∧
        (∫ ω, ‖radialClip τ (X ω) -
          ∫ ξ, radialClip τ (X ξ) ∂(μ : Measure Ω)‖ ^ 2
            ∂(μ : Measure Ω)) =
          (∫ z, ‖radialClip τ z -
            ∫ y, radialClip τ y ∂(ν : Measure SharpRadialClippingR3)‖ ^ 2
              ∂(ν : Measure SharpRadialClippingR3)) := by
  let p : PMF (Option (ι × Bool)) := signedAtomPMF q0 q v hq0 hv hsum
  let Z : Option (ι × Bool) → SharpRadialClippingR3 := signedAtomRV r e
  have hZm : Measurable Z := measurable_of_finite _
  let ν₀ : ProbabilityMeasure (Option (ι × Bool)) := ⟨p.toMeasure, inferInstance⟩
  let ν : ProbabilityMeasure SharpRadialClippingR3 := spatialPushforward ν₀ Z hZm
  obtain ⟨hradius, htrajectory⟩ := signedAtomRV_realizes_all_thresholds_of_geometry
    (μ : Measure Ω) X hX q0 q r v e hq0 hv hsum hr he hve
    hXtest hresidualGeometry hclippedGeometry
  refine ⟨ν, ?_, ?_⟩
  · calc
      Measure.map (fun ω ↦ ‖X ω‖) (μ : Measure Ω) =
          Measure.map (fun a ↦ ‖Z a‖) p.toMeasure := hradius
      _ = Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) := by
        exact (radial_law_spatialPushforward ν₀ Z hZm).symm
  · intro τ hτ
    obtain ⟨hb, he⟩ := htrajectory τ hτ
    obtain ⟨hbpush, hepush⟩ := bias_energy_spatialPushforward ν₀ Z hZm τ hτ
    exact ⟨hb.trans hbpush.symm, he.trans hepush.symm⟩

end

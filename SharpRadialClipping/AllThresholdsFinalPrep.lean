import SharpRadialClipping.AllThresholdsAssembly
import SharpRadialClipping.AllThresholdsFiniteAssembly

/-!
# All-threshold three-dimensional realization

The analytic limit passage is already proved in `AllThresholdsAssembly`.
This module first states the reduction to finite-radius laws, then discharges
that intermediate hypothesis using `AllThresholdsFiniteAssembly` and proves
the unrestricted theorem below.
-/

open MeasureTheory

noncomputable section

local instance finalPrepMeasurableSpace : MeasurableSpace SharpRadialClippingR3 := borel SharpRadialClippingR3
local instance finalPrepBorelSpace : BorelSpace SharpRadialClippingR3 := ⟨rfl⟩

theorem exists_all_thresholds_realization_from_finite_radius
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (hfinite : ∀ (Y : Ω → H), Measurable Y →
      Integrable Y (μ : Measure Ω) →
      (Set.range fun ω : Ω ↦ ‖Y ω‖).Finite →
      ∃ ν : ProbabilityMeasure SharpRadialClippingR3,
        Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) =
          Measure.map (fun ω : Ω ↦ ‖Y ω‖) (μ : Measure Ω) ∧
        ∀ τ : ℝ, 0 < τ →
          ‖(∫ ω, radialClip τ (Y ω) ∂(μ : Measure Ω)) -
              ∫ ω, Y ω ∂(μ : Measure Ω)‖ =
            ‖(∫ z, radialClip τ z ∂(ν : Measure SharpRadialClippingR3)) -
              ∫ z, z ∂(ν : Measure SharpRadialClippingR3)‖ ∧
          (∫ ω, ‖radialClip τ (Y ω) -
            ∫ ξ, radialClip τ (Y ξ) ∂(μ : Measure Ω)‖ ^ 2
              ∂(μ : Measure Ω)) =
            (∫ z, ‖radialClip τ z -
              ∫ y, radialClip τ y ∂(ν : Measure SharpRadialClippingR3)‖ ^ 2
                ∂(ν : Measure SharpRadialClippingR3))) :
    ∃ ν : ProbabilityMeasure SharpRadialClippingR3,
      Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) =
        Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω) ∧
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
  classical
  have hfiniteQuant (n : ℕ) :
      (Set.range fun ω : Ω ↦ ‖radialQuantized n (X ω)‖).Finite := by
    exact (finite_range_norm_radialQuantized (H := H) n).subset
      (by rintro _ ⟨ω, rfl⟩; exact ⟨X ω, rfl⟩)
  have hreal (n : ℕ) := hfinite
    (fun ω ↦ radialQuantized n (X ω))
    ((measurable_radialQuantized n).comp hXm)
    (integrable_radialQuantized_comp (μ : Measure Ω) X hXm hX n)
    (hfiniteQuant n)
  let νs : ℕ → ProbabilityMeasure SharpRadialClippingR3 := fun n ↦ (hreal n).choose
  have hspec (n : ℕ) := (hreal n).choose_spec
  apply exists_all_thresholds_realization_of_quantized_realizations
    μ X hXm hX νs
  · intro n
    have h := (hspec n).1
    simpa only [νs, norm_radialQuantized] using h
  · intro n τ hτ
    exact (hspec n).2 τ hτ |>.1
  · intro n τ hτ
    exact (hspec n).2 τ hτ |>.2

/-- Article Theorem 4.5: one probability law in three dimensions reproduces
the source radial law, clipping bias, and centered clipping energy at every
positive threshold. -/
theorem exists_all_thresholds_three_dimensional_realization
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω)) :
    ∃ ν : ProbabilityMeasure SharpRadialClippingR3,
      Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) =
        Measure.map (fun ω : Ω ↦ ‖X ω‖) (μ : Measure Ω) ∧
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
  exact exists_all_thresholds_realization_from_finite_radius μ X hXm hX
    (fun Y hYm hY hfinite =>
      exists_spatial_law_of_finite_radius_source μ Y hYm hY hfinite)

end

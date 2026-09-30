import H099.AllThresholdsPushforward

/-!
# The finite-radius spatial law from geometric coefficients

The source radial shells supply atom masses.  Once the folding construction
provides three-dimensional coefficients of no larger norm and the two
residual-path distance identities, the signed-atom construction yields an
actual probability law on `ℝ³`.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

local instance : MeasurableSpace H099R3 := borel H099R3
local instance : BorelSpace H099R3 := ⟨rfl⟩

theorem exists_spatial_law_of_finite_shell_geometry
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (s : Finset ℝ) (h0 : 0 ∉ s)
    (hr : ∀ r ∈ s, 0 < r)
    (hcover : ∀ ω, ‖X ω‖ ∈ insert 0 s)
    (v : s → H099R3)
    (hv : ∀ i : s, ‖v i‖ ≤
      (μ : Measure Ω).real {ω | ‖X ω‖ = (i : ℝ)})
    (hresidualGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖∑ i : s, max ((i : ℝ) - τ) 0 • v i‖)
    (hclippedGeometry : ∀ τ : ℝ, 0 < τ →
      ‖∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖(∑ i : s, (i : ℝ) • v i) -
          ∑ i : s, max ((i : ℝ) - τ) 0 • v i‖) :
    ∃ ν : ProbabilityMeasure H099R3,
      Measure.map (fun ω ↦ ‖X ω‖) (μ : Measure Ω) =
        Measure.map (fun z : H099R3 ↦ ‖z‖) (ν : Measure H099R3) ∧
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
  classical
  letI : MeasurableSpace (Option (s × Bool)) := ⊤
  letI : MeasurableSingletonClass (Option (s × Bool)) := ⟨fun _ ↦ trivial⟩
  let q0 : ℝ := (μ : Measure Ω).real {ω | ‖X ω‖ = 0}
  let q : s → ℝ := fun i ↦
    (μ : Measure Ω).real {ω | ‖X ω‖ = (i : ℝ)}
  let r : s → ℝ := fun i ↦ (i : ℝ)
  let e : s → H099R3 := fun i ↦ (exists_unit_direction (v i)).choose
  have he : ∀ i : s, ‖e i‖ = 1 := fun i ↦
    (exists_unit_direction (v i)).choose_spec.1
  have hve : ∀ i : s, ‖v i‖ • e i = v i := fun i ↦
    (exists_unit_direction (v i)).choose_spec.2
  have hsum : q0 + ∑ i, q i = 1 := by
    have h := zero_shell_mass_add_positive_shell_masses μ X hXm s h0 hcover
    rw [← Finset.sum_coe_sort s
      (fun r : ℝ ↦ (μ : Measure Ω).real {ω | ‖X ω‖ = r})] at h
    simpa only [q0, q] using h
  have hXtest : ∀ f : ℝ →ᵇ ℝ,
      (∫ ω, f ‖X ω‖ ∂(μ : Measure Ω)) =
        q0 * f 0 + ∑ i, q i * f (r i) := by
    intro f
    have h := finite_radius_radial_test_formula μ X hXm s h0 hcover f
    rw [← Finset.sum_coe_sort s
      (fun r : ℝ ↦ (μ : Measure Ω).real {ω | ‖X ω‖ = r} * f r)] at h
    simpa only [q0, q, r] using h
  exact exists_spatial_signedAtom_law_of_geometry μ X hX q0 q r v e
    (measureReal_nonneg) hv hsum (fun i ↦ hr i i.property)
    he hve hXtest hresidualGeometry hclippedGeometry

end

import SharpRadialClipping.AllThresholds
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Compactness bridge for simultaneous clipping realization

The finite-support construction in `AllThresholds` must be passed to a weak
limit.  A fixed radial distribution provides tightness of all its spatial
realizations in a proper normed space.
-/

open MeasureTheory

noncomputable section

/-- A uniform tail bound by one finite scalar measure makes a family of
probability laws tight in a proper normed space. -/
theorem tight_of_radial_tail_domination
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (S : Set (ProbabilityMeasure E))
    (htail : ∀ ν ∈ S, ∀ R : ℝ, 0 ≤ R →
      (ν : Measure E) {x | R < ‖x‖} ≤ ρ (Set.Ioi R)) :
    IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} := by
  have hρ : IsTightMeasureSet ({ρ} : Set (Measure ℝ)) :=
    isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hρ ⊢
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := hρ ε hε
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max C 0
  have hRC : C ≤ R := le_max_left C 0
  have hR0 : 0 ≤ R := le_max_right C 0
  refine ⟨Metric.closedBall (0 : E) R, isCompact_closedBall _ _, ?_⟩
  intro μ hμ
  rcases hμ with ⟨ν, hν, rfl⟩
  have hρtail : ρ (Set.Ioi R) ≤ ε := by
    have hsub : Set.Ioi R ⊆ Kᶜ := by
      intro r hr hrK
      have hbound := hC r hrK
      exact (not_le_of_gt hr) ((le_abs_self r).trans (hbound.trans hRC))
    exact (measure_mono hsub).trans (hKε ρ (by simp))
  have hmeasure :
      (ν : Measure E) (Metric.closedBall (0 : E) R)ᶜ =
        (ν : Measure E) {x | R < ‖x‖} := by
    congr 1
    ext x
    simp [Metric.mem_closedBall]
  rw [hmeasure]
  exact (htail ν hν R hR0).trans hρtail

/-- Probability laws on a proper normed space sharing one fixed radial law
form a tight family. This is the compactness input for the Prokhorov step. -/
theorem tight_of_same_radial_law
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (S : Set (ProbabilityMeasure E))
    (hS : ∀ ν ∈ S,
      Measure.map (fun x : E ↦ ‖x‖) (ν : Measure E) = ρ) :
    IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ S} := by
  have hρ : IsTightMeasureSet ({ρ} : Set (Measure ℝ)) :=
    isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hρ ⊢
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := hρ ε hε
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max C 0
  have hRC : C ≤ R := le_max_left C 0
  refine ⟨Metric.closedBall (0 : E) R, isCompact_closedBall _ _, ?_⟩
  intro μ hμ
  rcases hμ with ⟨ν, hν, rfl⟩
  have hρtail : ρ (Set.Ioi R) ≤ ε := by
    have hsub : Set.Ioi R ⊆ Kᶜ := by
      intro r hr hrK
      have hbound := hC r hrK
      have hrle : r ≤ ‖r‖ := le_abs_self r
      exact (not_le_of_gt hr) (hrle.trans (hbound.trans hRC))
    exact (measure_mono hsub).trans (hKε ρ (by simp))
  have hmeasure :
      (ν : Measure E) (Metric.closedBall (0 : E) R)ᶜ =
        ρ (Set.Ioi R) := by
    have hmap := congrArg (fun m : Measure ℝ ↦ m (Set.Ioi R)) (hS ν hν)
    rw [Measure.map_apply measurable_norm measurableSet_Ioi] at hmap
    simpa [Metric.closedBall, dist_zero_right, Set.preimage,
      Set.compl_setOf, not_le] using hmap
  exact hmeasure.le.trans hρtail

/-- Prokhorov provides one weakly convergent subsequence of any sequence of
probability laws having a common radial distribution. -/
theorem exists_weakly_convergent_subseq_of_same_radial_law
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (ν : ℕ → ProbabilityMeasure E)
    (hν : ∀ n, Measure.map (fun x : E ↦ ‖x‖) (ν n : Measure E) = ρ) :
    ∃ νlim : ProbabilityMeasure E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (ν ∘ φ) Filter.atTop (nhds νlim) := by
  let S : Set (ProbabilityMeasure E) := Set.range ν
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := by
    apply tight_of_same_radial_law ρ S
    rintro μ ⟨n, rfl⟩
    exact hν n
  have hcomp : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨νlim, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := ν) (fun n ↦
    subset_closure (Set.mem_range_self n))
  exact ⟨νlim, φ, hφ, hlim⟩

/-- Prokhorov extraction for approximate radial laws, uniformly dominated
by the tail of one finite reference measure. -/
theorem exists_weakly_convergent_subseq_of_radial_tail_domination
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (ν : ℕ → ProbabilityMeasure E)
    (htail : ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      (ν n : Measure E) {x | R < ‖x‖} ≤ ρ (Set.Ioi R)) :
    ∃ νlim : ProbabilityMeasure E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (ν ∘ φ) Filter.atTop (nhds νlim) := by
  let S : Set (ProbabilityMeasure E) := Set.range ν
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S} := by
    apply tight_of_radial_tail_domination ρ S
    rintro μ ⟨n, rfl⟩ R hR
    exact htail n R hR
  have hcomp : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨νlim, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := ν) (fun n ↦
    subset_closure (Set.mem_range_self n))
  exact ⟨νlim, φ, hφ, hlim⟩

/-- Equality of radial distributions survives weak convergence because the
norm map is continuous. -/
theorem same_radial_law_of_weak_limit
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (ρ : ProbabilityMeasure ℝ) (ν : ℕ → ProbabilityMeasure E)
    (νlim : ProbabilityMeasure E)
    (hlim : Filter.Tendsto ν Filter.atTop (nhds νlim))
    (hν : ∀ n,
      (ν n).map continuous_norm.measurable.aemeasurable = ρ) :
    νlim.map continuous_norm.measurable.aemeasurable = ρ := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    ν νlim hlim continuous_norm
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ ρ) Filter.atTop (nhds ρ) :=
    tendsto_const_nhds
  simp_rw [hν] at hmap
  exact tendsto_nhds_unique hmap hconst

/-- The radial distribution of a weak limit is the limit of the radial
distributions of the approximating laws.  This is the version needed when
the input norms are discretized rather than kept fixed. -/
theorem radial_law_of_weak_limit_of_radial_law_tendsto
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (ρ : ProbabilityMeasure ℝ) (ν : ℕ → ProbabilityMeasure E)
    (νlim : ProbabilityMeasure E)
    (hlim : Filter.Tendsto ν Filter.atTop (nhds νlim))
    (hradial : Filter.Tendsto
      (fun n ↦ (ν n).map continuous_norm.measurable.aemeasurable)
      Filter.atTop (nhds ρ)) :
    νlim.map continuous_norm.measurable.aemeasurable = ρ := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    ν νlim hlim continuous_norm
  exact tendsto_nhds_unique hmap hradial

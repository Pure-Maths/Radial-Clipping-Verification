import SharpRadialClipping.AllThresholdsAssembly

/-!
# Finite radial-shell decomposition

The finite-radius stage splits an integrable vector into its contributions
from each level set of the norm.  This file isolates that measure-theoretic
step from the folding geometry.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

/-- An integrable function can be integrated shell by shell when a measurable
scalar statistic takes its values in a finite set. -/
theorem integral_eq_sum_finite_radius_shells
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (f : Ω → E) (r : Ω → ℝ)
    (hr : Measurable r) (hf : Integrable f μ)
    (s : Finset ℝ) (hcover : ∀ ω, r ω ∈ s) :
    (∫ ω, f ω ∂μ) =
      ∑ a ∈ s, ∫ ω in {ω | r ω = a}, f ω ∂μ := by
  let shell : ℝ → Set Ω := fun a ↦ {ω | r ω = a}
  have hset : (⋃ a ∈ s, {ω : Ω | r ω = a}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨r ω, hcover ω, rfl⟩
  have hdisjoint : Set.Pairwise (↑s) (fun a b ↦ Disjoint (shell a) (shell b)) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro ω hωa hωb
    exact hab (hωa.symm.trans hωb)
  rw [← setIntegral_univ, ← hset]
  exact integral_biUnion_finset s
    (by intro a ha; exact hr (measurableSet_singleton a))
    hdisjoint
    (by intro a ha; exact hf.integrableOn)

/-- Extract precisely the positive radii from a finite-valued norm,
leaving zero as a separate shell. -/
theorem exists_positive_radius_finset_of_finite_range
    {Ω H : Type*} [NormedAddCommGroup H] (X : Ω → H)
    (hfinite : (Set.range fun ω : Ω ↦ ‖X ω‖).Finite) :
    ∃ s : Finset ℝ, 0 ∉ s ∧ (∀ r ∈ s, 0 < r) ∧
      ∀ ω, ‖X ω‖ ∈ insert 0 s := by
  classical
  let s : Finset ℝ := hfinite.toFinset.erase 0
  refine ⟨s, by simp [s], ?_, ?_⟩
  · intro r hr
    have hmem : r ∈ hfinite.toFinset := (Finset.mem_erase.mp hr).2
    obtain ⟨ω, hω⟩ : r ∈ Set.range (fun ω : Ω ↦ ‖X ω‖) :=
      hfinite.mem_toFinset.mp hmem
    have hrne : r ≠ 0 := (Finset.mem_erase.mp hr).1
    subst r
    exact lt_of_le_of_ne (norm_nonneg (X ω)) (Ne.symm hrne)
  · intro ω
    by_cases hzero : ‖X ω‖ = 0
    · simp [hzero]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨hzero, hfinite.mem_toFinset.mpr ⟨ω, rfl⟩⟩

/-- The vector coefficient on a positive shell has norm at most that shell's
probability mass. -/
theorem norm_shell_direction_mean_le_mass
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (r : ℝ) (hr : 0 < r) :
    ‖∫ ω in {ω | ‖X ω‖ = r}, (r⁻¹) • X ω ∂(μ : Measure Ω)‖ ≤
      ∫ _ω in {ω | ‖X ω‖ = r}, (1 : ℝ) ∂(μ : Measure Ω) := by
  let shell : Set Ω := {ω | ‖X ω‖ = r}
  have hs : MeasurableSet shell := hXm.norm (measurableSet_singleton r)
  calc
    ‖∫ ω in shell, (r⁻¹) • X ω ∂(μ : Measure Ω)‖ ≤
        ∫ ω in shell, ‖(r⁻¹) • X ω‖ ∂(μ : Measure Ω) :=
      norm_integral_le_integral_norm _
    _ = ∫ _ω in shell, (1 : ℝ) ∂(μ : Measure Ω) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hs] with ω hω
      have hnorm : ‖X ω‖ = r := hω
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hnorm]
      exact inv_mul_cancel₀ hr.ne'

/-- On one positive radial shell, the residual mean is its direction-mean
coefficient times the positive-part excess beyond the threshold. -/
theorem integral_shell_residual_eq_coefficient
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    (∫ ω in {ω | ‖X ω‖ = r}, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) =
      max (r - τ) 0 •
        ∫ ω in {ω | ‖X ω‖ = r}, (r⁻¹) • X ω ∂(μ : Measure Ω) := by
  let shell : Set Ω := {ω | ‖X ω‖ = r}
  have hs : MeasurableSet shell := hXm.norm (measurableSet_singleton r)
  have hnorm : ∀ᵐ ω ∂(μ : Measure Ω).restrict shell, ‖X ω‖ = r :=
    ae_restrict_mem hs
  calc
    (∫ ω in shell, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) =
        (max (r - τ) 0 / r) •
          ∫ ω in shell, X ω ∂(μ : Measure Ω) :=
      integral_residual_of_ae_constant_norm ((μ : Measure Ω).restrict shell) X hr hτ hnorm
    _ = max (r - τ) 0 •
        ∫ ω in shell, (r⁻¹) • X ω ∂(μ : Measure Ω) := by
      rw [integral_smul]
      simp only [div_eq_mul_inv, smul_smul]

/-- A shell coefficient, with the zero-radius shell assigned coefficient
zero. -/
def radialShellCoefficient
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) (X : Ω → H) (r : ℝ) : H :=
  if r = 0 then 0 else
    ∫ ω in {ω | ‖X ω‖ = r}, (r⁻¹) • X ω ∂μ

/-- The zero shell makes no contribution to the clipping residual. -/
theorem integral_zero_shell_residual
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ ω in {ω | ‖X ω‖ = 0}, X ω - radialClip τ (X ω)
      ∂(μ : Measure Ω)) = 0 := by
  let shell : Set Ω := {ω | ‖X ω‖ = 0}
  change (∫ ω in shell, X ω - radialClip τ (X ω)
    ∂(μ : Measure Ω)) = 0
  have hs : MeasurableSet shell := hXm.norm (measurableSet_singleton 0)
  have hzero : ∀ᵐ ω ∂(μ : Measure Ω).restrict shell, X ω = 0 :=
    (ae_restrict_mem hs).mono fun ω hω ↦ norm_eq_zero.mp hω
  have heq : (∫ ω in shell, X ω - radialClip τ (X ω)
      ∂(μ : Measure Ω)) = ∫ _ω in shell, (0 : H) ∂(μ : Measure Ω) := by
    apply integral_congr_ae
    filter_upwards [hzero] with ω hω
    simp [hω, radialClip_zero hτ.le]
  simpa using heq

/-- Uniform shell identity, including radius zero. -/
theorem integral_shell_residual_eq_coefficient_all
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (r τ : ℝ) (hr : 0 ≤ r) (hτ : 0 < τ) :
    (∫ ω in {ω | ‖X ω‖ = r}, X ω - radialClip τ (X ω)
      ∂(μ : Measure Ω)) = max (r - τ) 0 •
        radialShellCoefficient (μ : Measure Ω) X r := by
  by_cases hr0 : r = 0
  · subst r
    simp only [radialShellCoefficient, ↓reduceIte, smul_zero]
    exact integral_zero_shell_residual μ X hXm τ hτ
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    simpa [radialShellCoefficient, hr0] using
      integral_shell_residual_eq_coefficient μ X hXm r τ hrpos hτ

/-- Finite radial support yields the piecewise-linear residual-mean path
with one vector coefficient per shell. -/
theorem finite_radius_residual_path_formula
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (s : Finset ℝ) (hcover : ∀ ω, ‖X ω‖ ∈ s)
    (hr : ∀ r ∈ s, 0 ≤ r)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) =
      ∑ r ∈ s, max (r - τ) 0 •
        radialShellCoefficient (μ : Measure Ω) X r := by
  have hclip : Integrable (fun ω ↦ radialClip τ (X ω)) (μ : Measure Ω) :=
    integrable_radialClip hX.1 hτ
  rw [integral_eq_sum_finite_radius_shells (μ : Measure Ω)
    (fun ω ↦ X ω - radialClip τ (X ω)) (fun ω ↦ ‖X ω‖)
    hXm.norm (hX.sub hclip) s hcover]
  apply Finset.sum_congr rfl
  intro r hrs
  exact integral_shell_residual_eq_coefficient_all μ X hXm r τ
    (hr r hrs) hτ

/-- The zero-shell mass plus the masses of all positive shells is one. -/
theorem zero_shell_mass_add_positive_shell_masses
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (s : Finset ℝ) (h0 : 0 ∉ s)
    (hcover : ∀ ω, ‖X ω‖ ∈ insert 0 s) :
    (μ : Measure Ω).real {ω | ‖X ω‖ = 0} +
      ∑ r ∈ s, (μ : Measure Ω).real {ω | ‖X ω‖ = r} = 1 := by
  have hpartition := integral_eq_sum_finite_radius_shells
    (μ : Measure Ω) (fun _ : Ω ↦ (1 : ℝ)) (fun ω ↦ ‖X ω‖)
    hXm.norm (integrable_const 1) (insert 0 s) hcover
  simp only [setIntegral_one_eq_measureReal] at hpartition
  rw [Finset.sum_insert h0] at hpartition
  simpa using hpartition.symm

/-- The finite radial law is exactly the atomic law with its shell masses;
the statement uses bounded continuous tests, matching the signed-atom
realization interface. -/
theorem finite_radius_radial_test_formula
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (s : Finset ℝ) (h0 : 0 ∉ s)
    (hcover : ∀ ω, ‖X ω‖ ∈ insert 0 s)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω, f ‖X ω‖ ∂(μ : Measure Ω)) =
      (μ : Measure Ω).real {ω | ‖X ω‖ = 0} * f 0 +
        ∑ r ∈ s, (μ : Measure Ω).real {ω | ‖X ω‖ = r} * f r := by
  have hfi : Integrable (fun ω ↦ f ‖X ω‖) (μ : Measure Ω) := by
    apply (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp hXm.norm).aestronglyMeasurable
    filter_upwards [] with ω
    exact f.norm_coe_le_norm _
  have hpartition := integral_eq_sum_finite_radius_shells
    (μ : Measure Ω) (fun ω ↦ f ‖X ω‖) (fun ω ↦ ‖X ω‖)
    hXm.norm hfi (insert 0 s) hcover
  have hshell (r : ℝ) :
      (∫ ω in {ω | ‖X ω‖ = r}, f ‖X ω‖ ∂(μ : Measure Ω)) =
        (μ : Measure Ω).real {ω | ‖X ω‖ = r} * f r := by
    let shell : Set Ω := {ω | ‖X ω‖ = r}
    have hs : MeasurableSet shell := hXm.norm (measurableSet_singleton r)
    calc
      (∫ ω in shell, f ‖X ω‖ ∂(μ : Measure Ω)) =
          ∫ _ω in shell, f r ∂(μ : Measure Ω) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hs] with ω hω
        rw [hω]
      _ = (μ : Measure Ω).real shell * f r := by simp
  rw [Finset.sum_insert h0] at hpartition
  simp_rw [hshell] at hpartition
  exact hpartition

/-- The finite signed-atom coefficients satisfy precisely the probability
budget on every positive radial shell. -/
theorem norm_radialShellCoefficient_le_measureReal
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (r : ℝ) (hr : 0 < r) :
    ‖radialShellCoefficient (μ : Measure Ω) X r‖ ≤
      (μ : Measure Ω).real {ω | ‖X ω‖ = r} := by
  simp only [radialShellCoefficient, ne_of_gt hr, ↓reduceIte]
  simpa only [setIntegral_one_eq_measureReal] using
    norm_shell_direction_mean_le_mass μ X hXm r hr

/-- The original vector mean on a shell is radius times its direction-mean
coefficient, including the zero shell. -/
theorem integral_shell_vector_eq_radius_coefficient
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H) (hXm : Measurable X)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ ω in {ω | ‖X ω‖ = r}, X ω ∂(μ : Measure Ω)) =
      r • radialShellCoefficient (μ : Measure Ω) X r := by
  by_cases hr0 : r = 0
  · subst r
    have hs : MeasurableSet {ω : Ω | ‖X ω‖ = 0} :=
      hXm.norm (measurableSet_singleton 0)
    have hzero : ∀ᵐ ω ∂(μ : Measure Ω).restrict {ω | ‖X ω‖ = 0}, X ω = 0 :=
      (ae_restrict_mem hs).mono fun ω hω ↦ norm_eq_zero.mp hω
    have hInt : (∫ ω in {ω | ‖X ω‖ = 0}, X ω ∂(μ : Measure Ω)) = 0 := by
      calc
        (∫ ω in {ω | ‖X ω‖ = 0}, X ω ∂(μ : Measure Ω)) =
            ∫ _ω in {ω | ‖X ω‖ = 0}, (0 : H) ∂(μ : Measure Ω) := by
          apply integral_congr_ae
          exact hzero
        _ = 0 := by simp
    simpa using hInt
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    simp only [radialShellCoefficient, hr0, ↓reduceIte]
    rw [integral_smul, smul_smul]
    simp [hr0]

/-- For finite radial support the initial residual-path vertex is the
radius-weighted sum of the shell coefficients. -/
theorem finite_radius_mean_formula
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (s : Finset ℝ) (hcover : ∀ ω, ‖X ω‖ ∈ s)
    (hr : ∀ r ∈ s, 0 ≤ r) :
    (∫ ω, X ω ∂(μ : Measure Ω)) =
      ∑ r ∈ s, r • radialShellCoefficient (μ : Measure Ω) X r := by
  rw [integral_eq_sum_finite_radius_shells (μ : Measure Ω) X
    (fun ω ↦ ‖X ω‖) hXm.norm hX s hcover]
  apply Finset.sum_congr rfl
  intro r hrs
  exact integral_shell_vector_eq_radius_coefficient μ X hXm r (hr r hrs)

/-- All measure-theoretic data required by the finite signed-atom
construction is extracted from a source with finitely many possible norms. -/
theorem exists_finite_source_shell_data
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (hfinite : (Set.range fun ω : Ω ↦ ‖X ω‖).Finite) :
    ∃ s : Finset ℝ, 0 ∉ s ∧
      (∀ r ∈ s, 0 < r) ∧
      ((μ : Measure Ω).real {ω | ‖X ω‖ = 0} +
        ∑ r ∈ s, (μ : Measure Ω).real {ω | ‖X ω‖ = r} = 1) ∧
      (∀ r ∈ s, ‖radialShellCoefficient (μ : Measure Ω) X r‖ ≤
        (μ : Measure Ω).real {ω | ‖X ω‖ = r}) ∧
      (∀ f : ℝ →ᵇ ℝ,
        (∫ ω, f ‖X ω‖ ∂(μ : Measure Ω)) =
          (μ : Measure Ω).real {ω | ‖X ω‖ = 0} * f 0 +
          ∑ r ∈ s, (μ : Measure Ω).real {ω | ‖X ω‖ = r} * f r) ∧
      (∀ τ : ℝ, 0 < τ →
        (∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) =
          ∑ r ∈ s, max (r - τ) 0 •
            radialShellCoefficient (μ : Measure Ω) X r) ∧
      (∫ ω, X ω ∂(μ : Measure Ω)) =
        ∑ r ∈ s, r • radialShellCoefficient (μ : Measure Ω) X r := by
  obtain ⟨s, h0, hr, hcover⟩ :=
    exists_positive_radius_finset_of_finite_range X hfinite
  refine ⟨s, h0, hr,
    zero_shell_mass_add_positive_shell_masses μ X hXm s h0 hcover,
    (fun r hrs ↦ norm_radialShellCoefficient_le_measureReal μ X hXm r (hr r hrs)),
    finite_radius_radial_test_formula μ X hXm s h0 hcover, ?_, ?_⟩
  · intro τ hτ
    have hform := finite_radius_residual_path_formula μ X hXm hX
      (insert 0 s) hcover (by
        intro r hrs
        rcases Finset.mem_insert.mp hrs with rfl | hmem
        · exact le_refl 0
        · exact (hr r hmem).le) τ hτ
    rw [Finset.sum_insert h0] at hform
    simpa [radialShellCoefficient] using hform
  · have hform := finite_radius_mean_formula μ X hXm hX
      (insert 0 s) hcover (by
        intro r hrs
        rcases Finset.mem_insert.mp hrs with rfl | hmem
        · exact le_refl 0
        · exact (hr r hmem).le)
    rw [Finset.sum_insert h0] at hform
    simpa using hform

end

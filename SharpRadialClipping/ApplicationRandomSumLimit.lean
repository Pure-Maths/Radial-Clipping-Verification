import SharpRadialClipping.ApplicationRandomSum

/-!
# Truncation of a random sum of bounded nonnegative claims

For retained losses, every summand lies in `[0, τ]`.  These pointwise facts
prepare dominated convergence from a bounded count to an arbitrary count with
finite second moment.
-/

open MeasureTheory

noncomputable section

def retainedClaims {Ω : Type*} (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (N ω), Y i ω

def truncatedRetainedClaims {Ω : Type*} (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (M : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range M, (if i < N ω then (1 : ℝ) else 0) * Y i ω

theorem truncatedRetainedClaims_eq_sum_min {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (M : ℕ) (ω : Ω) :
    truncatedRetainedClaims N Y M ω =
      ∑ i ∈ Finset.range (min M (N ω)), Y i ω := by
  classical
  unfold truncatedRetainedClaims
  have hterm (i : ℕ) :
      (if i < N ω then (1 : ℝ) else 0) * Y i ω =
        if i < N ω then Y i ω else 0 := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem truncatedRetainedClaims_eq_of_count_le {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (M : ℕ) (ω : Ω) (hN : N ω ≤ M) :
    truncatedRetainedClaims N Y M ω = retainedClaims N Y ω := by
  rw [truncatedRetainedClaims_eq_sum_min, min_eq_right hN]
  rfl

theorem retainedClaims_nonneg_and_bound {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (τ : ℝ)
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ) (ω : Ω) :
    0 ≤ retainedClaims N Y ω ∧
      retainedClaims N Y ω ≤ (N ω : ℝ) * τ := by
  unfold retainedClaims
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact (hY i ω).1
  · calc
      (∑ i ∈ Finset.range (N ω), Y i ω) ≤
          ∑ i ∈ Finset.range (N ω), τ := by
            apply Finset.sum_le_sum
            intro i hi
            exact (hY i ω).2
      _ = (N ω : ℝ) * τ := by simp

theorem truncatedRetainedClaims_nonneg_and_bound {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (τ : ℝ)
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ) (M : ℕ) (ω : Ω) :
    0 ≤ truncatedRetainedClaims N Y M ω ∧
      truncatedRetainedClaims N Y M ω ≤ (N ω : ℝ) * τ := by
  rw [truncatedRetainedClaims_eq_sum_min]
  have h := retainedClaims_nonneg_and_bound
    (fun _ : Ω ↦ min M (N ω)) Y τ hY ω
  constructor
  · exact h.1
  · exact h.2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast min_le_right M (N ω)) (by
        have := (hY 0 ω).1
        have := (hY 0 ω).2
        linarith))

theorem measurable_truncatedRetainedClaims {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hN : Measurable N) (hY : ∀ i, Measurable (Y i)) :
    Measurable (truncatedRetainedClaims N Y M) := by
  unfold truncatedRetainedClaims
  apply Finset.measurable_sum
  intro i hi
  have hSet : MeasurableSet {ω : Ω | i < N ω} :=
    measurableSet_lt measurable_const hN
  exact (measurable_const.ite hSet measurable_const).mul (hY i)

theorem tendsto_truncatedRetainedClaims {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (ω : Ω) :
    Filter.Tendsto (fun M ↦ truncatedRetainedClaims N Y M ω)
      Filter.atTop (nhds (retainedClaims N Y ω)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (N ω)] with M hM
  exact (truncatedRetainedClaims_eq_of_count_le N Y M ω hM).symm

theorem tendsto_truncatedRetainedClaims_sq {Ω : Type*} (N : Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (ω : Ω) :
    Filter.Tendsto (fun M ↦ (truncatedRetainedClaims N Y M ω) ^ 2)
      Filter.atTop (nhds ((retainedClaims N Y ω) ^ 2)) := by
  exact (tendsto_truncatedRetainedClaims N Y ω).pow 2

theorem measurable_retainedClaims {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ i, Measurable (Y i)) :
    Measurable (retainedClaims N Y) := by
  exact measurable_of_tendsto_metrizable
    (fun M ↦ measurable_truncatedRetainedClaims N Y M hN hY)
    (tendsto_pi_nhds.mpr (fun ω ↦ tendsto_truncatedRetainedClaims N Y ω))

theorem tendsto_integral_truncatedRetainedClaims
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (τ : ℝ)
    (hN : Measurable N) (hYmeas : ∀ i, Measurable (Y i))
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ) :
    Filter.Tendsto
      (fun M ↦ ∫ ω, truncatedRetainedClaims N Y M ω ∂μ)
      Filter.atTop (nhds (∫ ω, retainedClaims N Y ω ∂μ)) := by
  let B : Ω → ℝ := fun ω ↦ 1 + τ ^ 2 * (N ω : ℝ) ^ 2
  have hB : Integrable B μ := by
    have h := (integrable_const (1 : ℝ)).add (hN2.const_mul (τ ^ 2))
    simpa [B, Pi.add_apply] using h
  apply tendsto_integral_of_dominated_convergence B
  · intro M
    exact (measurable_truncatedRetainedClaims N Y M hN hYmeas).aestronglyMeasurable
  · exact hB
  · intro M
    filter_upwards with ω
    have hc := truncatedRetainedClaims_nonneg_and_bound N Y τ hY M ω
    have hτ : 0 ≤ τ := le_trans (hY 0 ω).1 (hY 0 ω).2
    rw [Real.norm_eq_abs, abs_of_nonneg hc.1]
    dsimp [B]
    have hn : 0 ≤ (N ω : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (τ * (N ω : ℝ) - 1 / 2)]
  · filter_upwards with ω
    exact tendsto_truncatedRetainedClaims N Y ω

theorem tendsto_integral_truncatedRetainedClaims_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (τ : ℝ)
    (hN : Measurable N) (hYmeas : ∀ i, Measurable (Y i))
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ) :
    Filter.Tendsto
      (fun M ↦ ∫ ω, (truncatedRetainedClaims N Y M ω) ^ 2 ∂μ)
      Filter.atTop (nhds (∫ ω, (retainedClaims N Y ω) ^ 2 ∂μ)) := by
  let B : Ω → ℝ := fun ω ↦ τ ^ 2 * (N ω : ℝ) ^ 2
  have hB : Integrable B μ := by
    simpa only [B] using hN2.const_mul (τ ^ 2)
  apply tendsto_integral_of_dominated_convergence B
  · intro M
    exact ((measurable_truncatedRetainedClaims N Y M hN hYmeas).pow_const 2)
      |>.aestronglyMeasurable
  · exact hB
  · intro M
    filter_upwards with ω
    have hc := truncatedRetainedClaims_nonneg_and_bound N Y τ hY M ω
    have hτ : 0 ≤ τ := le_trans (hY 0 ω).1 (hY 0 ω).2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp [B]
    have hn : 0 ≤ (N ω : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (by nlinarith :
      0 ≤ τ * (N ω : ℝ) + truncatedRetainedClaims N Y M ω)]
  · filter_upwards with ω
    exact tendsto_truncatedRetainedClaims_sq N Y ω

theorem tendsto_integral_min_count
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ) :
    Filter.Tendsto
      (fun (M : ℕ) ↦ ∫ ω, ((min (N ω) M : ℕ) : ℝ) ∂μ)
      Filter.atTop (nhds (∫ ω, (N ω : ℝ) ∂μ)) := by
  let B : Ω → ℝ := fun ω ↦ 1 + (N ω : ℝ) ^ 2
  have hB : Integrable B μ := by
    simpa [B, Pi.add_apply] using (integrable_const (1 : ℝ)).add hN2
  apply tendsto_integral_of_dominated_convergence B
  · intro M
    have hm : Measurable (fun ω : Ω ↦ ((min (N ω) M : ℕ) : ℝ)) := by fun_prop
    exact hm.aestronglyMeasurable
  · exact hB
  · intro M
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hm : ((min (N ω) M : ℕ) : ℝ) ≤ (N ω : ℝ) := by
      exact_mod_cast min_le_left (N ω) M
    have hn : 0 ≤ (N ω : ℝ) := Nat.cast_nonneg _
    dsimp [B]
    nlinarith [sq_nonneg ((N ω : ℝ) - 1 / 2)]
  · filter_upwards with ω
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (N ω)] with M hM
    rw [min_eq_left hM]

theorem tendsto_integral_min_count_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ) :
    Filter.Tendsto
      (fun (M : ℕ) ↦ ∫ ω, (((min (N ω) M : ℕ) : ℝ)) ^ 2 ∂μ)
      Filter.atTop (nhds (∫ ω, (N ω : ℝ) ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω ↦ (N ω : ℝ) ^ 2)
  · intro M
    have hm : Measurable (fun ω : Ω ↦ ((min (N ω) M : ℕ) : ℝ)) := by fun_prop
    exact (hm.pow_const 2).aestronglyMeasurable
  · exact hN2
  · intro M
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm : ((min (N ω) M : ℕ) : ℝ) ≤ (N ω : ℝ) := by
      exact_mod_cast min_le_left (N ω) M
    have hp : 0 ≤ ((min (N ω) M : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · filter_upwards with ω
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (N ω)] with M hM
    rw [min_eq_left hM]

end

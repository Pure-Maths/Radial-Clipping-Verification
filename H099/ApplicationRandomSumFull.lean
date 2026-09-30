import H099.ApplicationRandomSumLimit
import H099.ApplicationRandomSumVariance

/-!
# First and second moments of a random sum with an unbounded count

The bounded-count identities are passed to the limit using the clipped-loss
bound and the second moment of the count.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

private theorem boundedRandomClaims_min_eq_truncated
    {Ω : Type*} (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ) (ω : Ω) :
    boundedRandomClaims (fun ω ↦ min (N ω) M) Y M ω =
      truncatedRetainedClaims N Y M ω := by
  classical
  unfold boundedRandomClaims truncatedRetainedClaims
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i < M := Finset.mem_range.mp hi
  by_cases hiN : i < N ω
  · have hmin : i < min (N ω) M := lt_min hiN hiM
    simp [hiN, hmin]
  · have hmin : ¬i < min (N ω) M := by omega
    simp [hiN, hmin]

theorem random_sum_mean_and_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (τ m s : ℝ)
    (hN : Measurable N)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ)
    (hYint : ∀ i, Integrable (Y i) μ)
    (hYsq : ∀ i, Integrable (fun ω ↦ Y i ω ^ 2) μ)
    (hMean : ∀ i, (∫ ω, Y i ω ∂μ) = m)
    (hSecond : ∀ i, (∫ ω, Y i ω ^ 2 ∂μ) = s)
    (hPair : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω ↦ fun n : ℕ ↦ Y n ω) μ) :
    (∫ ω, retainedClaims N Y ω ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * m ∧
    (∫ ω, (retainedClaims N Y ω) ^ 2 ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * s +
        ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) -
          (∫ ω, (N ω : ℝ) ∂μ)) * m ^ 2 := by
  have hmeanM (M : ℕ) :
      (∫ ω, truncatedRetainedClaims N Y M ω ∂μ) =
        (∫ ω, ((min (N ω) M : ℕ) : ℝ) ∂μ) * m := by
    let NM : Ω → ℕ := fun ω ↦ min (N ω) M
    have hNM : Measurable NM := hN.min measurable_const
    have hNseqM : IndepFun NM (fun ω : Ω ↦ fun n : ℕ ↦ Y n ω) μ :=
      indepFun_min_count_sequence μ N Y M hNseq
    have hNY (i : ℕ) (_hi : i < M) : IndepFun NM (Y i) μ := by
      have hψ : Measurable (fun y : ℕ → ℝ ↦ y i) := by fun_prop
      simpa only [Function.comp_def, id_eq] using
        hNseqM.comp (measurable_id : Measurable (id : ℕ → ℕ)) hψ
    have h := integral_bounded_random_sum_eq_count_mul_mean
      μ NM Y M m hNM (fun ω ↦ min_le_right (N ω) M)
      (fun i _ ↦ hYint i) hNY (fun i _ ↦ hMean i)
    calc
      (∫ ω, truncatedRetainedClaims N Y M ω ∂μ) =
          ∫ ω, boundedRandomClaims NM Y M ω ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            exact (boundedRandomClaims_min_eq_truncated N Y M ω).symm
      _ = _ := h
  have hsecondM (M : ℕ) :
      (∫ ω, (truncatedRetainedClaims N Y M ω) ^ 2 ∂μ) =
        (∫ ω, ((min (N ω) M : ℕ) : ℝ) ∂μ) * s +
        ((∫ ω, ((min (N ω) M : ℕ) : ℝ) ^ 2 ∂μ) -
          (∫ ω, ((min (N ω) M : ℕ) : ℝ) ∂μ)) * m ^ 2 := by
    let NM : Ω → ℕ := fun ω ↦ min (N ω) M
    have hNM : Measurable NM := hN.min measurable_const
    have hNseqM : IndepFun NM (fun ω : Ω ↦ fun n : ℕ ↦ Y n ω) μ :=
      indepFun_min_count_sequence μ N Y M hNseq
    have h := integral_boundedRandomClaims_sq
      μ NM Y M m s hNM (fun ω ↦ min_le_right (N ω) M)
      (fun i _ ↦ hYint i) (fun i _ ↦ hYsq i)
      (fun i _ ↦ hMean i) (fun i _ ↦ hSecond i)
      (fun i _ j _ hij ↦ hPair i j hij) hNseqM
    simpa only [NM, boundedRandomClaims_min_eq_truncated] using h
  have hcount := tendsto_integral_min_count μ N hN hN2
  have hcountSq := tendsto_integral_min_count_sq μ N hN hN2
  have hlimMean := tendsto_integral_truncatedRetainedClaims
    μ N Y τ hN hYmeas hYbound hN2
  have hlimSq := tendsto_integral_truncatedRetainedClaims_sq
    μ N Y τ hN hYmeas hYbound hN2
  constructor
  · have hR := hcount.mul_const m
    have hR' : Filter.Tendsto
        (fun M ↦ ∫ ω, truncatedRetainedClaims N Y M ω ∂μ)
        Filter.atTop (nhds ((∫ ω, (N ω : ℝ) ∂μ) * m)) := by
      convert hR using 1
      ext M
      exact hmeanM M
    exact tendsto_nhds_unique hlimMean hR'
  · have hR := (hcount.mul_const s).add
      ((hcountSq.sub hcount).mul_const (m ^ 2))
    have hR' : Filter.Tendsto
        (fun M ↦ ∫ ω, (truncatedRetainedClaims N Y M ω) ^ 2 ∂μ)
        Filter.atTop
          (nhds ((∫ ω, (N ω : ℝ) ∂μ) * s +
            ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) -
              (∫ ω, (N ω : ℝ) ∂μ)) * m ^ 2)) := by
      convert hR using 1
      ext M
      exact hsecondM M
    exact tendsto_nhds_unique hlimSq hR'

theorem random_sum_centered_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (τ m s : ℝ)
    (hN : Measurable N)
    (hN2 : Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ τ)
    (hYint : ∀ i, Integrable (Y i) μ)
    (hYsq : ∀ i, Integrable (fun ω ↦ Y i ω ^ 2) μ)
    (hMean : ∀ i, (∫ ω, Y i ω ∂μ) = m)
    (hSecond : ∀ i, (∫ ω, Y i ω ^ 2 ∂μ) = s)
    (hPair : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω ↦ fun n : ℕ ↦ Y n ω) μ) :
    (∫ ω, (retainedClaims N Y ω -
        ∫ z, retainedClaims N Y z ∂μ) ^ 2 ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * (s - m ^ 2) +
        ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) -
          (∫ ω, (N ω : ℝ) ∂μ) ^ 2) * m ^ 2 := by
  have hMom := random_sum_mean_and_second_moment μ N Y τ m s hN hN2
    hYmeas hYbound hYint hYsq hMean hSecond hPair hNseq
  have hCmeas := measurable_retainedClaims N Y hN hYmeas
  let B : Ω → ℝ := fun ω ↦ 1 + τ ^ 2 * (N ω : ℝ) ^ 2
  have hB : Integrable B μ := by
    simpa [B, Pi.add_apply] using (integrable_const (1 : ℝ)).add
      (hN2.const_mul (τ ^ 2))
  have hC : Integrable (retainedClaims N Y) μ := by
    apply Integrable.mono' hB hCmeas.aestronglyMeasurable
    filter_upwards with ω
    have hc := retainedClaims_nonneg_and_bound N Y τ hYbound ω
    rw [Real.norm_eq_abs, abs_of_nonneg hc.1]
    dsimp [B]
    nlinarith [sq_nonneg (τ * (N ω : ℝ) - 1 / 2)]
  have hCsq : Integrable (fun ω ↦ ‖retainedClaims N Y ω‖ ^ 2) μ := by
    apply Integrable.mono' (hN2.const_mul (τ ^ 2))
      ((hCmeas.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards with ω
    have hc := retainedClaims_nonneg_and_bound N Y τ hYbound ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖retainedClaims N Y ω‖)),
      Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.2)
      (by nlinarith : 0 ≤ τ * (N ω : ℝ) + retainedClaims N Y ω)]
  have hVar := integral_norm_sub_mean_sq μ (retainedClaims N Y) hC hCsq
  simp_rw [Real.norm_eq_abs, sq_abs] at hVar
  calc
    _ = (∫ ω, retainedClaims N Y ω ^ 2 ∂μ) -
        (∫ ω, retainedClaims N Y ω ∂μ) ^ 2 := hVar
    _ = _ := by rw [hMom.1, hMom.2]; ring

end

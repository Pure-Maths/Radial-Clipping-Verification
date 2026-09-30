import H099.ApplicationReinsurance
import Mathlib.Probability.Independence.Integration

/-!
# A bounded random-sum mean bridge

These lemmas begin the independence-to-moment step needed for reinsurance.
The variance identity for an unbounded random count is not asserted here.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Pointwise finite tail-count identity. -/
theorem finite_tail_indicator_sum (n M : ℕ) (hn : n ≤ M) :
    (∑ i ∈ Finset.range M, if i < n then (1 : ℝ) else 0) = n := by
  classical
  calc
    (∑ i ∈ Finset.range M, if i < n then (1 : ℝ) else 0) =
        ∑ i ∈ (Finset.range M).filter (fun i => i < n), (1 : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.range n, (1 : ℝ) := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    _ = n := by simp

/-- A retained-claim indicator and a loss remain independent when the event
is determined by an independent claim count. -/
theorem independent_claim_indicator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : Ω → ℝ) (i : ℕ)
    (hNY : IndepFun N Y μ) :
    IndepFun (fun ω => if i < N ω then (1 : ℝ) else 0) Y μ := by
  have hφ : Measurable (fun n : ℕ => if i < n then (1 : ℝ) else 0) := by
    fun_prop
  simpa only [Function.comp_def, id_eq] using
    hNY.comp hφ (measurable_id : Measurable (id : ℝ → ℝ))

/-- Independence of the entire loss sequence from the count yields
independence of a count event from any pairwise loss product. -/
theorem independent_claim_indicator_pair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (k i j : ℕ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    IndepFun (fun ω => if k < N ω then (1 : ℝ) else 0)
      (fun ω => Y i ω * Y j ω) μ := by
  have hφ : Measurable (fun n : ℕ => if k < n then (1 : ℝ) else 0) := by
    fun_prop
  have hψ : Measurable (fun y : ℕ → ℝ => y i * y j) := by
    fun_prop
  simpa only [Function.comp_def] using hNseq.comp hφ hψ

/-- The corresponding mixed second-moment factorization. -/
theorem integral_independent_claim_indicator_pair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (k i j : ℕ)
    (hN : Measurable N)
    (hPairProduct : Integrable (fun ω => Y i ω * Y j ω) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, (if k < N ω then (1 : ℝ) else 0) * (Y i ω * Y j ω) ∂μ) =
      (∫ ω, if k < N ω then (1 : ℝ) else 0 ∂μ) *
        (∫ ω, Y i ω * Y j ω ∂μ) := by
  have hInd := independent_claim_indicator_pair μ N Y k i j hNseq
  have hSet : MeasurableSet {ω : Ω | k < N ω} :=
    measurableSet_lt measurable_const hN
  have hMeas : Measurable (fun ω => if k < N ω then (1 : ℝ) else 0) :=
    measurable_const.ite hSet measurable_const
  exact hInd.integral_fun_mul_eq_mul_integral
    hMeas.aestronglyMeasurable hPairProduct.1

/-- The off-diagonal factorization used when expanding the square of the
random sum. The hypothesis `hNseq` is independence from the whole sequence,
not merely from each loss separately. -/
theorem integral_off_diagonal_bounded_random_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (k i j : ℕ) (m : ℝ)
    (hN : Measurable N)
    (hYi : Integrable (Y i) μ) (hYj : Integrable (Y j) μ)
    (hYiMean : (∫ ω, Y i ω ∂μ) = m)
    (hYjMean : (∫ ω, Y j ω ∂μ) = m)
    (hij : IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, (if k < N ω then (1 : ℝ) else 0) * (Y i ω * Y j ω) ∂μ) =
      (∫ ω, if k < N ω then (1 : ℝ) else 0 ∂μ) * m ^ 2 := by
  have hprod : Integrable (fun ω => Y i ω * Y j ω) μ :=
    hij.integrable_mul hYi hYj
  rw [integral_independent_claim_indicator_pair μ N Y k i j hN hprod hNseq]
  rw [hij.integral_fun_mul_eq_mul_integral hYi.1 hYj.1,
    hYiMean, hYjMean]
  ring

/-- Independence factors the expectation of one count-selected loss. -/
theorem integral_independent_claim_indicator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : Ω → ℝ) (i : ℕ)
    (hN : Measurable N) (hY : Integrable Y μ)
    (hNY : IndepFun N Y μ) :
    (∫ ω, (if i < N ω then (1 : ℝ) else 0) * Y ω ∂μ) =
      (∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) *
        (∫ ω, Y ω ∂μ) := by
  have hInd := independent_claim_indicator μ N Y i hNY
  have hSet : MeasurableSet {ω : Ω | i < N ω} :=
    measurableSet_lt measurable_const hN
  have hMeas : Measurable (fun ω => if i < N ω then (1 : ℝ) else 0) :=
    measurable_const.ite hSet measurable_const
  have hA : AEStronglyMeasurable (fun ω => if i < N ω then (1 : ℝ) else 0) μ := by
    exact hMeas.aestronglyMeasurable
  exact hInd.integral_fun_mul_eq_mul_integral hA hY.1

/-- For a finite horizon, the expected selected sum is the sum of the
factorized expectations. This is the first random-sum identity before the
tail-count identity converts the right-hand side to `E[N] E[Y₀]`. -/
theorem integral_bounded_random_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hN : Measurable N)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hNY : ∀ i < M, IndepFun N (Y i) μ) :
    (∫ ω, ∑ i ∈ Finset.range M,
      (if i < N ω then (1 : ℝ) else 0) * Y i ω ∂μ) =
      ∑ i ∈ Finset.range M,
        (∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) *
          (∫ ω, Y i ω ∂μ) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_independent_claim_indicator μ N (Y i) i
      hN (hY i (Finset.mem_range.mp hi)) (hNY i (Finset.mem_range.mp hi))
  · intro i hi
    have hInd := independent_claim_indicator μ N (Y i) i
      (hNY i (Finset.mem_range.mp hi))
    have hA : Integrable (fun ω => if i < N ω then (1 : ℝ) else 0) μ := by
      have hSet : MeasurableSet {ω : Ω | i < N ω} :=
        measurableSet_lt measurable_const hN
      have hB : Measurable (fun ω => if i < N ω then (1 : ℝ) else 0) :=
        measurable_const.ite hSet measurable_const
      exact Integrable.of_bound hB.aestronglyMeasurable 1 (by
        filter_upwards with ω
        split_ifs <;> simp)
    exact hInd.integrable_mul hA (hY i (Finset.mem_range.mp hi))

/-- The expected value of a bounded random sum of independent losses with a
common mean is the expected count times that mean. -/
theorem integral_bounded_random_sum_eq_count_mul_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ) (m : ℝ)
    (hN : Measurable N) (hBound : ∀ ω, N ω ≤ M)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hNY : ∀ i < M, IndepFun N (Y i) μ)
    (hMean : ∀ i < M, (∫ ω, Y i ω ∂μ) = m) :
    (∫ ω, ∑ i ∈ Finset.range M,
      (if i < N ω then (1 : ℝ) else 0) * Y i ω ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * m := by
  rw [integral_bounded_random_sum μ N Y M hN hY hNY]
  have hsum :
      (∑ i ∈ Finset.range M,
        (∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) *
          (∫ ω, Y i ω ∂μ)) =
      ∑ i ∈ Finset.range M,
        (∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) * m := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hMean i (Finset.mem_range.mp hi)]
  rw [hsum]
  rw [← Finset.sum_mul]
  have hA (i : ℕ) (hi : i < M) :
      Integrable (fun ω => if i < N ω then (1 : ℝ) else 0) μ := by
    have hSet : MeasurableSet {ω : Ω | i < N ω} :=
      measurableSet_lt measurable_const hN
    have hB : Measurable (fun ω => if i < N ω then (1 : ℝ) else 0) :=
      measurable_const.ite hSet measurable_const
    exact Integrable.of_bound hB.aestronglyMeasurable 1 (by
      filter_upwards with ω
      split_ifs <;> simp)
  have hI :
      (∑ i ∈ Finset.range M,
        ∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) =
        ∫ ω, ∑ i ∈ Finset.range M,
          if i < N ω then (1 : ℝ) else 0 ∂μ := by
    rw [integral_finsetSum]
    intro i hi
    exact hA i (Finset.mem_range.mp hi)
  rw [hI]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  exact finite_tail_indicator_sum (N ω) M (hBound ω)

#print axioms integral_bounded_random_sum_eq_count_mul_mean
#print axioms integral_off_diagonal_bounded_random_sum

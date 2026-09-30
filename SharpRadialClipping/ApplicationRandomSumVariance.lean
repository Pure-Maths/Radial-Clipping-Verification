import SharpRadialClipping.ApplicationRandomSum

/-!
# Second moment of a bounded random sum

The central algebra here uses tail indicators. Independence of the claim
count from the *entire* sequence is retained explicitly.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Truncating the count preserves independence from the entire claim
sequence. -/
lemma indepFun_min_count_sequence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    IndepFun (fun ω => min (N ω) M)
      (fun ω : Ω => fun n : ℕ => Y n ω) μ := by
  have hφ : Measurable (fun n : ℕ => min n M) := by fun_prop
  simpa only [Function.comp_def, id_eq] using
    hNseq.comp hφ (measurable_id : Measurable (id : (ℕ → ℝ) → (ℕ → ℝ)))

/-- Claims retained when the random number of events is at most `M`. -/
def boundedRandomClaims {Ω : Type*} (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (M : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range M, (if i < N ω then (1 : ℝ) else 0) * Y i ω

private lemma integrable_tail_indicator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (i : ℕ) (hN : Measurable N) :
    Integrable (fun ω => if i < N ω then (1 : ℝ) else 0) μ := by
  have hSet : MeasurableSet {ω : Ω | i < N ω} :=
    measurableSet_lt measurable_const hN
  have hB : Measurable (fun ω => if i < N ω then (1 : ℝ) else 0) :=
    measurable_const.ite hSet measurable_const
  exact Integrable.of_bound hB.aestronglyMeasurable 1 (by
    filter_upwards with ω
    split_ifs <;> simp)

/-- The product of two tail indicators is the later tail indicator. -/
lemma tail_indicator_mul (n i j : ℕ) :
    (if i < n then (1 : ℝ) else 0) * (if j < n then (1 : ℝ) else 0) =
      if max i j < n then (1 : ℝ) else 0 := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [hi, hj]

/-- Factoring a diagonal second-moment term from the entire-sequence
independence hypothesis. -/
theorem integral_diagonal_bounded_random_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (i : ℕ)
    (hN : Measurable N)
    (hYiSq : Integrable (fun ω => Y i ω ^ 2) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, (if i < N ω then (1 : ℝ) else 0) * Y i ω ^ 2 ∂μ) =
      (∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) *
        (∫ ω, Y i ω ^ 2 ∂μ) := by
  have hφ : Measurable (fun n : ℕ => if i < n then (1 : ℝ) else 0) := by
    fun_prop
  have hψ : Measurable (fun y : ℕ → ℝ => y i ^ 2) := by
    fun_prop
  have hInd : IndepFun (fun ω => if i < N ω then (1 : ℝ) else 0)
      (fun ω => Y i ω ^ 2) μ := by
    simpa only [Function.comp_def] using hNseq.comp hφ hψ
  have hSet : MeasurableSet {ω : Ω | i < N ω} :=
    measurableSet_lt measurable_const hN
  have hMeas : Measurable (fun ω => if i < N ω then (1 : ℝ) else 0) :=
    measurable_const.ite hSet measurable_const
  exact hInd.integral_fun_mul_eq_mul_integral
    hMeas.aestronglyMeasurable hYiSq.1

/-- A single entry in the double-sum expansion of the second moment. -/
theorem integral_pair_bounded_random_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (i j : ℕ) (m s : ℝ)
    (hN : Measurable N)
    (hYi : Integrable (Y i) μ) (hYj : Integrable (Y j) μ)
    (hYiMean : (∫ ω, Y i ω ∂μ) = m)
    (hYjMean : (∫ ω, Y j ω ∂μ) = m)
    (hYiSq : Integrable (fun ω => Y i ω ^ 2) μ)
    (hYiSecond : (∫ ω, Y i ω ^ 2 ∂μ) = s)
    (hij : i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
      ((if j < N ω then (1 : ℝ) else 0) * Y j ω) ∂μ) =
      (∫ ω, if max i j < N ω then (1 : ℝ) else 0 ∂μ) *
        (if i = j then s else m ^ 2) := by
  have hpoint (ω : Ω) :
      ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
        ((if j < N ω then (1 : ℝ) else 0) * Y j ω) =
        (if max i j < N ω then (1 : ℝ) else 0) * (Y i ω * Y j ω) := by
    rw [← tail_indicator_mul (N ω) i j]
    ring
  simp_rw [hpoint]
  by_cases heq : i = j
  · subst j
    simp only [max_self, ite_true]
    have hdiag := integral_diagonal_bounded_random_sum μ N Y i hN hYiSq hNseq
    simpa only [← pow_two, hYiSecond] using hdiag
  · simp only [heq, ite_false]
    exact integral_off_diagonal_bounded_random_sum μ N Y (max i j) i j m
      hN hYi hYj hYiMean hYjMean (hij heq) hNseq

/-- Integrability of each term of the double-sum expansion. -/
theorem integrable_pair_bounded_random_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (i j : ℕ)
    (hN : Measurable N)
    (hYi : Integrable (Y i) μ) (hYj : Integrable (Y j) μ)
    (hYiSq : Integrable (fun ω => Y i ω ^ 2) μ)
    (hij : i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    Integrable (fun ω => ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
      ((if j < N ω then (1 : ℝ) else 0) * Y j ω)) μ := by
  have hprod : Integrable (fun ω => Y i ω * Y j ω) μ := by
    by_cases heq : i = j
    · subst j
      simpa only [← pow_two] using hYiSq
    · exact (hij heq).integrable_mul hYi hYj
  have hInd := independent_claim_indicator_pair μ N Y (max i j) i j hNseq
  have hInt := hInd.integrable_mul
    (integrable_tail_indicator μ N (max i j) hN) hprod
  convert hInt using 1
  ext ω
  change ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
    ((if j < N ω then (1 : ℝ) else 0) * Y j ω) =
    (if max i j < N ω then (1 : ℝ) else 0) * (Y i ω * Y j ω)
  rw [← tail_indicator_mul (N ω) i j]
  ring

/-- Exact finite double-sum formula for the second moment of a bounded
random sum. -/
theorem integral_boundedRandomClaims_sq_double_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ) (m s : ℝ)
    (hN : Measurable N)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hYsq : ∀ i < M, Integrable (fun ω => Y i ω ^ 2) μ)
    (hMean : ∀ i < M, (∫ ω, Y i ω ∂μ) = m)
    (hSecond : ∀ i < M, (∫ ω, Y i ω ^ 2 ∂μ) = s)
    (hPair : ∀ i < M, ∀ j < M, i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, boundedRandomClaims N Y M ω ^ 2 ∂μ) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (∫ ω, if max i j < N ω then (1 : ℝ) else 0 ∂μ) *
          (if i = j then s else m ^ 2) := by
  have hpoint (ω : Ω) : boundedRandomClaims N Y M ω ^ 2 =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
          ((if j < N ω then (1 : ℝ) else 0) * Y j ω) := by
    simp only [boundedRandomClaims, pow_two, Finset.sum_mul_sum]
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact integral_pair_bounded_random_sum μ N Y i j m s hN
        (hY i (Finset.mem_range.mp hi)) (hY j (Finset.mem_range.mp hj))
        (hMean i (Finset.mem_range.mp hi)) (hMean j (Finset.mem_range.mp hj))
        (hYsq i (Finset.mem_range.mp hi)) (hSecond i (Finset.mem_range.mp hi))
        (hPair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) hNseq
    · intro j hj
      exact integrable_pair_bounded_random_sum μ N Y i j hN
        (hY i (Finset.mem_range.mp hi)) (hY j (Finset.mem_range.mp hj))
        (hYsq i (Finset.mem_range.mp hi))
        (hPair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) hNseq
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact integrable_pair_bounded_random_sum μ N Y i j hN
      (hY i (Finset.mem_range.mp hi)) (hY j (Finset.mem_range.mp hj))
      (hYsq i (Finset.mem_range.mp hi))
      (hPair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) hNseq

/-- Counting ordered pairs of active claims gives the square of the count. -/
lemma double_tail_indicator_sum (n M : ℕ) (hn : n ≤ M) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      if max i j < n then (1 : ℝ) else 0) = (n : ℝ) ^ 2 := by
  calc
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        if max i j < n then (1 : ℝ) else 0) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (if i < n then (1 : ℝ) else 0) *
          (if j < n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (tail_indicator_mul n i j).symm
    _ = (∑ i ∈ Finset.range M, if i < n then (1 : ℝ) else 0) *
          (∑ j ∈ Finset.range M, if j < n then (1 : ℝ) else 0) := by
      rw [Finset.sum_mul_sum]
    _ = (n : ℝ) ^ 2 := by
      rw [finite_tail_indicator_sum n M hn]
      ring

/-- The integrated double-tail count is the second moment of `N`. -/
theorem integral_count_sq_eq_double_tail_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (M : ℕ) (hN : Measurable N)
    (hBound : ∀ ω, N ω ≤ M) :
    (∫ ω, (N ω : ℝ) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        ∫ ω, if max i j < N ω then (1 : ℝ) else 0 ∂μ := by
  have hpoint (ω : Ω) : (N ω : ℝ) ^ 2 =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        if max i j < N ω then (1 : ℝ) else 0 :=
    (double_tail_indicator_sum (N ω) M (hBound ω)).symm
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    intro j hj
    exact integrable_tail_indicator μ N (max i j) hN
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact integrable_tail_indicator μ N (max i j) hN

theorem integral_count_eq_tail_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (M : ℕ) (hN : Measurable N)
    (hBound : ∀ ω, N ω ≤ M) :
    (∫ ω, (N ω : ℝ) ∂μ) =
      ∑ i ∈ Finset.range M,
        ∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ := by
  have hpoint (ω : Ω) : (N ω : ℝ) =
      ∑ i ∈ Finset.range M, if i < N ω then (1 : ℝ) else 0 :=
    (finite_tail_indicator_sum (N ω) M (hBound ω)).symm
  simp_rw [hpoint]
  rw [integral_finsetSum]
  intro i hi
  exact integrable_tail_indicator μ N i hN

/-- Pure finite algebra separating the diagonal of a symmetric second-moment
matrix from its off-diagonal baseline. -/
lemma double_sum_diagonal_correction
    (M : ℕ) (t : ℕ → ℝ) (m s : ℝ) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      t (max i j) * (if i = j then s else m ^ 2)) =
      (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        t (max i j)) * m ^ 2 +
      (∑ i ∈ Finset.range M, t i) * (s - m ^ 2) := by
  have hrow (i : ℕ) (hi : i ∈ Finset.range M) :
      (∑ j ∈ Finset.range M,
        t (max i j) * (if i = j then s else m ^ 2)) =
      (∑ j ∈ Finset.range M, t (max i j)) * m ^ 2 +
        t i * (s - m ^ 2) := by
    calc
      _ = ∑ j ∈ Finset.range M,
          (t (max i j) * m ^ 2 + if i = j then t i * (s - m ^ 2) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j
        · subst j
          simp
          ring
        · simp [hij]
      _ = (∑ j ∈ Finset.range M, t (max i j)) * m ^ 2 +
          ∑ j ∈ Finset.range M,
            if i = j then t i * (s - m ^ 2) else 0 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = _ := by
        simp [hi]
  calc
    _ = ∑ i ∈ Finset.range M,
        ((∑ j ∈ Finset.range M, t (max i j)) * m ^ 2 +
          t i * (s - m ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]

/-- Second moment of a bounded random sum with iid first two moments. -/
theorem integral_boundedRandomClaims_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ) (m s : ℝ)
    (hN : Measurable N) (hBound : ∀ ω, N ω ≤ M)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hYsq : ∀ i < M, Integrable (fun ω => Y i ω ^ 2) μ)
    (hMean : ∀ i < M, (∫ ω, Y i ω ∂μ) = m)
    (hSecond : ∀ i < M, (∫ ω, Y i ω ^ 2 ∂μ) = s)
    (hPair : ∀ i < M, ∀ j < M, i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, boundedRandomClaims N Y M ω ^ 2 ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * s +
      ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) -
        (∫ ω, (N ω : ℝ) ∂μ)) * m ^ 2 := by
  rw [integral_boundedRandomClaims_sq_double_sum μ N Y M m s
    hN hY hYsq hMean hSecond hPair hNseq]
  have hdiag := double_sum_diagonal_correction M
    (fun i => ∫ ω, if i < N ω then (1 : ℝ) else 0 ∂μ) m s
  have hfirst := integral_count_eq_tail_integrals μ N M hN hBound
  have hsecond := integral_count_sq_eq_double_tail_integrals μ N M hN hBound
  rw [hdiag, ← hsecond, ← hfirst]
  ring

#print axioms integral_boundedRandomClaims_sq

lemma integrable_boundedRandomClaims
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hN : Measurable N)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    Integrable (boundedRandomClaims N Y M) μ := by
  unfold boundedRandomClaims
  apply integrable_finsetSum
  intro i hi
  have hψ : Measurable (fun y : ℕ → ℝ => y i) := by fun_prop
  have hNYi : IndepFun N (Y i) μ := by
    simpa only [Function.comp_def, id_eq] using
      hNseq.comp (measurable_id : Measurable (id : ℕ → ℕ)) hψ
  have hInd := independent_claim_indicator μ N (Y i) i hNYi
  exact hInd.integrable_mul (integrable_tail_indicator μ N i hN)
    (hY i (Finset.mem_range.mp hi))

lemma integrable_boundedRandomClaims_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hN : Measurable N)
    (hY : ∀ i < M, Integrable (Y i) μ)
    (hYsq : ∀ i < M, Integrable (fun ω => Y i ω ^ 2) μ)
    (hPair : ∀ i < M, ∀ j < M, i ≠ j → IndepFun (Y i) (Y j) μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n => Y n ω) μ) :
    Integrable (fun ω => boundedRandomClaims N Y M ω ^ 2) μ := by
  have hpoint (ω : Ω) : boundedRandomClaims N Y M ω ^ 2 =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        ((if i < N ω then (1 : ℝ) else 0) * Y i ω) *
          ((if j < N ω then (1 : ℝ) else 0) * Y j ω) := by
    simp only [boundedRandomClaims, pow_two, Finset.sum_mul_sum]
  simp_rw [hpoint]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact integrable_pair_bounded_random_sum μ N Y i j hN
    (hY i (Finset.mem_range.mp hi)) (hY j (Finset.mem_range.mp hj))
    (hYsq i (Finset.mem_range.mp hi))
    (hPair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) hNseq

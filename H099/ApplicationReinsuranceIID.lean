import H099.ApplicationRandomSumVariance
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.L2Space

/-!
# IID input for the reinsurance random-sum formula

Identical laws provide the common first and second moments, while
`iIndepFun` supplies each distinct-pair independence hypothesis.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Every loss in an identically distributed `L²` family has the same first
and second moment and is itself in `L²`. -/
theorem iid_l2_moment_data
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hIdent : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hL2 : MemLp (Y 0) 2 μ) :
    (∀ i, MemLp (Y i) 2 μ) ∧
      (∀ i, Integrable (Y i) μ) ∧
      (∀ i, Integrable (fun ω => Y i ω ^ 2) μ) ∧
      (∀ i, (∫ ω, Y i ω ∂μ) = (∫ ω, Y 0 ω ∂μ)) ∧
      (∀ i, (∫ ω, Y i ω ^ 2 ∂μ) = (∫ ω, Y 0 ω ^ 2 ∂μ)) := by
  have hAllL2 (i : ℕ) : MemLp (Y i) 2 μ :=
    (hIdent i).symm.memLp_snd hL2
  refine ⟨hAllL2, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hAllL2 i).integrable (by norm_num)
  · intro i
    exact (hAllL2 i).integrable_sq
  · intro i
    exact (hIdent i).integral_eq
  · intro i
    simpa only [Function.comp_def] using (hIdent i).sq.integral_eq

/-- The exact bounded random-sum second moment under IID `L²` hypotheses.
No common-moment assumptions remain: they are derived above from the laws. -/
theorem integral_boundedRandomClaims_sq_of_iid
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ) (M : ℕ)
    (hN : Measurable N) (hBound : ∀ ω, N ω ≤ M)
    (hIdent : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hL2 : MemLp (Y 0) 2 μ)
    (hIndep : iIndepFun Y μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => Y n ω) μ) :
    (∫ ω, boundedRandomClaims N Y M ω ^ 2 ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) * (∫ ω, Y 0 ω ^ 2 ∂μ) +
      ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) - (∫ ω, (N ω : ℝ) ∂μ)) *
        (∫ ω, Y 0 ω ∂μ) ^ 2 := by
  obtain ⟨hAllL2, hAllInt, hAllSq, hAllMean, hAllSecond⟩ :=
    iid_l2_moment_data μ Y hIdent hL2
  exact integral_boundedRandomClaims_sq μ N Y M
    (∫ ω, Y 0 ω ∂μ) (∫ ω, Y 0 ω ^ 2 ∂μ)
    hN hBound
    (fun i hi => hAllInt i) (fun i hi => hAllSq i)
    (fun i hi => hAllMean i) (fun i hi => hAllSecond i)
    (fun i hi j hj hij => hIndep.indepFun hij) hNseq

/-- Clipping preserves all three relevant law/independence hypotheses. -/
theorem clipped_iid_independence_data
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (X : ℕ → Ω → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hIndep : iIndepFun X μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => X n ω) μ) :
    (∀ i, IdentDistrib (fun ω => radialClip τ (X i ω))
      (fun ω => radialClip τ (X 0 ω)) μ μ) ∧
      iIndepFun (fun i ω => radialClip τ (X i ω)) μ ∧
      IndepFun N (fun ω : Ω => fun i : ℕ => radialClip τ (X i ω)) μ := by
  have hMeasClip : Measurable (radialClip τ : ℝ → ℝ) :=
    (continuous_radialClip τ hτ).measurable
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [Function.comp_def] using (hIdent i).comp hMeasClip
  · simpa only [Function.comp_def] using
      hIndep.comp (fun _ : ℕ => radialClip τ) (fun _ => hMeasClip)
  · have hψ : Measurable (fun y : ℕ → ℝ => fun i : ℕ => radialClip τ (y i)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact hMeasClip.comp (measurable_pi_apply i)
    simpa only [Function.comp_def, id_eq] using
      hNseq.comp (measurable_id : Measurable (id : ℕ → ℕ)) hψ

/-- Direct article-style bounded second-moment theorem from the original
IID un-clipped losses and independence from the entire loss sequence. -/
theorem integral_bounded_clipped_claims_sq_of_iid
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (X : ℕ → Ω → ℝ) (M : ℕ) (τ : ℝ)
    (hτ : 0 < τ) (hN : Measurable N) (hBound : ∀ ω, N ω ≤ M)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hL2 : MemLp (X 0) 2 μ)
    (hIndep : iIndepFun X μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => X n ω) μ) :
    (∫ ω, boundedRandomClaims N
      (fun i ω => radialClip τ (X i ω)) M ω ^ 2 ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) *
        (∫ ω, radialClip τ (X 0 ω) ^ 2 ∂μ) +
      ((∫ ω, (N ω : ℝ) ^ 2 ∂μ) - (∫ ω, (N ω : ℝ) ∂μ)) *
        (∫ ω, radialClip τ (X 0 ω) ∂μ) ^ 2 := by
  obtain ⟨hClipIdent, hClipIndep, hClipNseq⟩ :=
    clipped_iid_independence_data μ N X τ hτ hIdent hIndep hNseq
  have hClipL2 : MemLp (fun ω => radialClip τ (X 0 ω)) 2 μ :=
    MemLp.of_le hL2 (aestronglyMeasurable_radialClip hL2.1 hτ) (by
      filter_upwards with ω
      rw [norm_radialClip hτ]
      exact min_le_left _ _)
  exact integral_boundedRandomClaims_sq_of_iid μ N
    (fun i ω => radialClip τ (X i ω)) M hN hBound
    hClipIdent hClipL2 hClipIndep hClipNseq

/-- The matching bounded first-moment formula, also with no supplied
common-moment or termwise-independence hypotheses. -/
theorem integral_bounded_clipped_claims_of_iid
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (X : ℕ → Ω → ℝ) (M : ℕ) (τ : ℝ)
    (hτ : 0 < τ) (hN : Measurable N) (hBound : ∀ ω, N ω ≤ M)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hL2 : MemLp (X 0) 2 μ)
    (hIndep : iIndepFun X μ)
    (hNseq : IndepFun N (fun ω : Ω => fun n : ℕ => X n ω) μ) :
    (∫ ω, boundedRandomClaims N
      (fun i ω => radialClip τ (X i ω)) M ω ∂μ) =
      (∫ ω, (N ω : ℝ) ∂μ) *
        (∫ ω, radialClip τ (X 0 ω) ∂μ) := by
  obtain ⟨hClipIdent, hClipIndep, hClipNseq⟩ :=
    clipped_iid_independence_data μ N X τ hτ hIdent hIndep hNseq
  have hClipL2 : MemLp (fun ω => radialClip τ (X 0 ω)) 2 μ :=
    MemLp.of_le hL2 (aestronglyMeasurable_radialClip hL2.1 hτ) (by
      filter_upwards with ω
      rw [norm_radialClip hτ]
      exact min_le_left _ _)
  obtain ⟨hAllL2, hAllInt, hAllSq, hAllMean, hAllSecond⟩ :=
    iid_l2_moment_data μ (fun i ω => radialClip τ (X i ω))
      hClipIdent hClipL2
  have hTermIndep (i : ℕ) :
      IndepFun N (fun ω => radialClip τ (X i ω)) μ := by
    have hψ : Measurable (fun y : ℕ → ℝ => y i) := by fun_prop
    simpa only [Function.comp_def, id_eq] using
      hClipNseq.comp (measurable_id : Measurable (id : ℕ → ℕ)) hψ
  exact integral_bounded_random_sum_eq_count_mul_mean μ N
    (fun i ω => radialClip τ (X i ω)) M
    (∫ ω, radialClip τ (X 0 ω) ∂μ)
    hN hBound (fun i hi => hAllInt i)
    (fun i hi => hTermIndep i) (fun i hi => hAllMean i)

#print axioms integral_bounded_clipped_claims_of_iid

#print axioms integral_bounded_clipped_claims_sq_of_iid

#print axioms integral_boundedRandomClaims_sq_of_iid

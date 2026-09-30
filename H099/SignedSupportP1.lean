import H099.SignedSupport
import H099.AttainableP1

/-!
# Signed support of the `p = 1` attainable region

The exact triangular classification gives the support function for arbitrary
real coefficients.  The missing top vertex does not change the supremum.
-/

noncomputable section

universe u v

/-- Values of the signed linear functional on the article's `p = 1`
attainable energy--bias pairs. -/
def signedAttainableValuesP1 (H : Type v) [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (τ α β : ℝ) : Set ℝ :=
  (fun z : ℝ × ℝ => α * z.2 + β * z.1) '' articleAttainablePairs.{u, v} H 1 τ

/-- The signed support over the `p = 1` attainable region is the largest of
the values at the three vertices of its closed triangle. -/
theorem signedAttainableValuesP1_isLUB
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {τ α β : ℝ} (hτ : 0 < τ) :
    IsLUB (signedAttainableValuesP1.{u, v} H τ α β) (max 0 (max α β)) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    change z ∈ attainableBiasEnergyPairsP1.{u, v} H τ at hz
    have hzTri := attainableBiasEnergyPairsP1_subset_triangle H hτ hz
    exact simplex_linear_form_le_vertex_max hzTri.1 hzTri.2.1 hzTri.2.2.1
  · intro b hb
    have hzero : 0 ∈ signedAttainableValuesP1.{u, v} H τ α β := by
      refine ⟨(0, 0), ?_, ?_⟩
      · change (0, 0) ∈ articleAttainablePairs.{u, v} H 1 τ
        exact articleOrigin_mem hτ
      · simp
    have hb0 : 0 ≤ b := hb hzero
    have hbeta : β ≤ b := by
      have hβmem : β ∈ signedAttainableValuesP1.{u, v} H τ α β := by
        refine ⟨(1, 0), ?_, ?_⟩
        · exact articleEndpointPair_one_zero (p := 1) hτ
        · simp
      simpa using hb hβmem
    have halpha : α ≤ b := by
      by_cases hα0 : α ≤ 0
      · linarith
      · have hαpos : 0 < α := lt_of_not_ge hα0
        by_contra hnot
        have hba : b < α := lt_of_not_ge hnot
        let d : ℝ := (1 + b / α) / 2
        have hd0 : 0 ≤ d := by
          dsimp [d]
          positivity
        have hdlt : d < 1 := by
          dsimp [d]
          have hdiv : b / α < 1 := (div_lt_one hαpos).2 hba
          linarith
        have hz : (0, d) ∈ attainableBiasEnergyPairsP1.{u, v} H τ := by
          exact p1_strict_interior_mem_attainable hτ (le_rfl) hd0 (by simpa using hdlt)
        have hval : α * d > b := by
          dsimp [d]
          have hcalc : α * ((1 + b / α) / 2) = (α + b) / 2 := by
            field_simp [ne_of_gt hαpos]
          rw [hcalc]
          linarith
        have hmem : α * d ∈ signedAttainableValuesP1.{u, v} H τ α β := by
          refine ⟨(0, d), ?_, ?_⟩
          · change (0, d) ∈ articleAttainablePairs.{u, v} H 1 τ
            exact hz
          · simp
        linarith [hb hmem]
    change max 0 (max α β) ≤ b
    exact max_le_iff.mpr ⟨hb0, max_le_iff.mpr ⟨halpha, hbeta⟩⟩

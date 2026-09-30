import SharpRadialClipping.AttainableExact

/-!
# Inverting the exposed rare-shock boundary

The right branch of the rare-shock boundary spans all bias levels between
zero and the sharp bias constant. This is a scalar ingredient in the
two-atom realization theorem.
-/

noncomputable section

private lemma rareBias_continuousOn_Icc
    {p R : ℝ} :
    ContinuousOn (rareBias p) (Set.Icc 1 R) := by
  apply ContinuousOn.mul
  · exact continuousOn_id.sub continuousOn_const
  · intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr.1
    exact (Real.continuousAt_rpow_const r (-p) (.inl hrpos.ne')).continuousWithinAt

/-- Every bias level up to the sharp constant occurs on the exposed
right-hand branch of the rare-shock curve. -/
theorem exists_rareRadius_of_bias_le_c_p
    {p d : ℝ} (hp : 1 < p) (hd0 : 0 ≤ d) (hdc : d ≤ c_p p) :
    ∃ r : ℝ, 1 ≤ r ∧ r ≤ p / (p - 1) ∧ rareBias p r = d := by
  let R : ℝ := p / (p - 1)
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 1) hp
  have hRpos : 0 < R := div_pos hp0 hpm
  have hRone : 1 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ hpm).2 (by linarith)
  have hRstar : r_star 1 0 p = R := by
    simp [r_star, R]
  have hright : rareBias p R = c_p p := by
    have hF : F 1 0 p R = c_p p := by
      calc
        F 1 0 p R = criticalValue 1 0 p := by
          rw [← hRstar]
          exact F_at_r_star (by norm_num) hp (by nlinarith)
        _ = c_p p := by
          simpa using criticalValue_closed_form (α := 1) (β := 0)
            (p := p) (by norm_num) hp (by norm_num)
    have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := 0)
      (r := R) hRone
    simpa using hcurve.trans hF
  have hleft : rareBias p 1 = 0 := by simp [rareBias]
  have hdmem : d ∈ Set.Icc (rareBias p 1) (rareBias p R) := by
    rw [hleft, hright]
    exact ⟨hd0, hdc⟩
  have hcont : ContinuousOn (rareBias p) (Set.Icc 1 R) :=
    rareBias_continuousOn_Icc
  obtain ⟨r, hr, hre⟩ :=
    (intermediate_value_Icc hRone hcont) hdmem
  exact ⟨r, hr.1, hr.2, hre⟩

open MeasureTheory ProbabilityTheory

universe u v

/-- At a positive bias level below the maximum, any attainable energy is
strictly to the left of the exposed rare-shock boundary point. -/
theorem attainable_energy_lt_rareEnergy_of_bias_eq
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ r v₀ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hr1 : 1 < r) (hrR : r < p / (p - 1))
    (hmem : (v₀, rareBias p r) ∈ articleAttainablePairs.{u, v} H p τ) :
    v₀ < rareEnergy p r := by
  rcases hmem with ⟨law, hpair⟩
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hden : 0 < p - (p - 1) * r := by
    apply (lt_div_iff₀ hpm).mp at hrR
    nlinarith
  let α : ℝ := p / (p - (p - 1) * r)
  have hαpos : 0 < α := div_pos hp0 hden
  have hreg : p * 1 < α := by
    dsimp [α]
    apply (lt_div_iff₀ hden).2
    have hdenlt : p - (p - 1) * r < 1 := by
      nlinarith [mul_lt_mul_of_pos_left hr1 hpm]
    nlinarith
  have hrstar : r_star α 1 p = r := by
    dsimp [r_star, α]
    field_simp [ne_of_gt hp0, ne_of_gt hpm, ne_of_gt hden]
    ring
  have hF : F α 1 p r = K_p α 1 p := by
    rw [← hrstar, F_at_r_star (by norm_num) hp hreg,
      K_p_eq_criticalValue (by norm_num) hp hreg]
  have hsupport :
      α * rareBias p r + rareEnergy p r = K_p α 1 p := by
    have hcurve := rareCurve_support_eq_F (p := p) (α := α) (β := 1)
      (r := r) hr1.le
    rw [hF] at hcurve
    simpa [add_comm, mul_comm] using hcurve
  have hV :
      stochasticClippingRatio law.μ 0 1 p τ law.X = v₀ := by
    have := congrArg Prod.fst hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hD :
      stochasticClippingRatio law.μ 1 0 p τ law.X = rareBias p r := by
    have := congrArg Prod.snd hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hlin := stochasticClippingRatio_linear
    (μ := law.μ) (α := α) (β := 1) (p := p) (τ := τ) law.X
  have hstrict := stochasticClippingRatio_lt_K_p_second_regime_of_pos_energy
    law.μ hαpos.le (by norm_num) hp hp2 hreg hτ law.X law.memLp
    law.moment_pos
  have hstrict' : α * rareBias p r + v₀ < K_p α 1 p := by
    rw [← hlin, hD, hV] at hstrict
    simpa using hstrict
  linarith

/-- The scalar witness needed for two-atom realization at every strictly
intermediate positive bias level. -/
theorem exists_rareRadius_above_attainable_energy
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ v₀ d : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hd : 0 < d) (hdc : d < c_p p)
    (hmem : (v₀, d) ∈ articleAttainablePairs.{u, v} H p τ) :
    ∃ r : ℝ, 1 < r ∧ r < p / (p - 1) ∧
      rareBias p r = d ∧ v₀ < rareEnergy p r := by
  obtain ⟨r, hr1, hrR, hrd⟩ :=
    exists_rareRadius_of_bias_le_c_p hp hd.le hdc.le
  have hr1' : 1 < r := by
    rcases eq_or_lt_of_le hr1 with heq | hlt
    · rw [← heq] at hrd
      simp [rareBias] at hrd
      linarith
    · exact hlt
  have hrR' : r < p / (p - 1) := by
    rcases eq_or_lt_of_le hrR with heq | hlt
    · rw [heq] at hrd
      have hendpoint : rareBias p (p / (p - 1)) = c_p p := by
        have hp0 : 0 < p := zero_lt_one.trans hp
        have hpm : 0 < p - 1 := sub_pos.mpr hp
        have hRone : 1 ≤ p / (p - 1) :=
          (le_div_iff₀ hpm).2 (by linarith)
        have hRstar : r_star 1 0 p = p / (p - 1) := by
          simp [r_star]
        have hcurve := rareCurve_support_eq_F (p := p)
          (α := 1) (β := 0) (r := p / (p - 1)) hRone
        rw [← hRstar, F_at_r_star (by norm_num) hp (by norm_num)] at hcurve
        have hcrit := criticalValue_closed_form (α := 1) (β := 0)
          (p := p) (by norm_num) hp (by norm_num)
        simpa [hRstar] using hcurve.trans (by simpa using hcrit)
      linarith
    · exact hlt
  refine ⟨r, hr1', hrR', hrd, ?_⟩
  rw [← hrd] at hmem
  exact attainable_energy_lt_rareEnergy_of_bias_eq hp hp2 hτ hr1' hrR' hmem

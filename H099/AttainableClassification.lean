import H099.TwoAtom

/-!
# Parametric exact attainable set for `1 < p ≤ 2`

The exposed rare-shock arc parametrizes the right endpoint of each positive-bias
horizontal section.  The endpoint itself is excluded, whereas the bottom edge
is attained.  This is the exact-set part of Theorem 4.1.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

/-- The attainable region in rare-shock radius coordinates.  Coordinates are
`(energy, bias)`.  On every positive-bias horizontal section the right endpoint
is excluded. -/
def rareEnvelopeRegion (p : ℝ) : Set (ℝ × ℝ) :=
  {z | (z.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ 1) ∨
    ∃ r : ℝ, 1 < r ∧ r ≤ p / (p - 1) ∧
      rareBias p r = z.2 ∧ 0 ≤ z.1 ∧ z.1 < rareEnergy p r}

/-- The lower edge of the normalized region is attained in every nontrivial
Hilbert space, including its right endpoint. -/
theorem article_bottom_edge_mem
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ w : ℝ} (hp : 1 < p) (hτ : 0 < τ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (w, 0) ∈ articleAttainablePairs.{u, v} H p τ := by
  by_cases hw : w = 1
  · subst w
    have hcenter := rare_endpoint_mem_centeredBool (H := H) (p := p) hτ
    rcases hcenter with ⟨μ, hμ, X, hLp, _hmean, hm, hz⟩
    let law : RandomVectorLaw.{0, v} H p := {
      Ω := Bool
      mΩ := inferInstance
      μ := μ
      probability := hμ
      X := X
      memLp := hLp
      moment_pos := hm
    }
    have hpair : law.biasEnergyPair τ = (1, 0) := by
      simpa [law, RandomVectorLaw.biasEnergyPair,
        normalizedBiasEnergyPair, rareEnergy, rareBias] using hz.symm
    have hlift : law.liftBool.biasEnergyPair τ = law.biasEnergyPair τ := by
      letI : IsProbabilityMeasure law.μ := law.probability
      apply Prod.ext
      · exact stochasticClippingRatio_map_equiv
          (MeasurableEquiv.ulift.symm) law.μ law.X
      · exact stochasticClippingRatio_map_equiv
          (MeasurableEquiv.ulift.symm) law.μ law.X
    refine ⟨law.liftBool, ?_⟩
    change law.liftBool.biasEnergyPair τ = (1, 0)
    rw [hlift]
    exact hpair
  · have hwlt : w < 1 := lt_of_le_of_ne hw1 hw
    have hq : 0 < 1 - w := by linarith
    have hq1 : 1 - w ≤ 1 := by linarith
    have hpair := oneAtom_biasEnergyPair.{u, v} (H := H)
      (a := 1) (τ := τ) (q := 1 - w) (p := p)
      (by norm_num) hτ hq hq1 hp
    simpa using hpair

/-- Every attainable pair lies in the parametric region. -/
theorem articleAttainablePairs_subset_rareEnvelopeRegion
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ ⊆ rareEnvelopeRegion p := by
  intro z hz
  rcases z with ⟨w, d⟩
  have hnonneg := articleAttainablePair_nonneg hτ hz
  change 0 ≤ w ∧ 0 ≤ d at hnonneg
  have hdle : d ≤ c_p p := by
    rcases hz with ⟨law, hpair⟩
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    have hD : stochasticClippingRatio law.μ 1 0 p τ law.X = d := by
      have := congrArg Prod.snd hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
    have hbound := stochasticClippingRatio_le_K_p_of_memLp
      law.μ (α := 1) (β := 0) (by norm_num) (by norm_num)
      hp hp2 hτ law.X law.memLp law.moment_pos
    rw [hD] at hbound
    simpa [K_p, c_p, show ¬(1 : ℝ) ≤ 0 by norm_num] using hbound
  by_cases hd0 : d = 0
  · left
    refine ⟨hd0, hnonneg.1, ?_⟩
    rcases hz with ⟨law, hpair⟩
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    have hV : stochasticClippingRatio law.μ 0 1 p τ law.X = w := by
      have := congrArg Prod.fst hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
    have hbound := stochasticClippingRatio_le_K_p_of_memLp
      law.μ (α := 0) (β := 1) (by norm_num) (by norm_num)
      hp hp2 hτ law.X law.memLp law.moment_pos
    rw [hV] at hbound
    have hK : K_p 0 1 p = 1 := by
      unfold K_p
      rw [if_pos (by linarith : (0 : ℝ) ≤ p * 1)]
    simpa [hK] using hbound
  right
  have hdpos : 0 < d := lt_of_le_of_ne hnonneg.2 (Ne.symm hd0)
  by_cases hdmax : d = c_p p
  · let R : ℝ := p / (p - 1)
    have hpm : 0 < p - 1 := sub_pos.mpr hp
    have hR : 1 < R := by
      dsimp [R]
      exact (lt_div_iff₀ hpm).2 (by nlinarith)
    have hRbias : rareBias p R = c_p p := by
      have hRone : 1 ≤ R := hR.le
      have hRstar : r_star 1 0 p = R := by simp [r_star, R]
      have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := 0)
        (r := R) hRone
      rw [← hRstar, F_at_r_star (by norm_num) hp (by norm_num)] at hcurve
      have hcrit := criticalValue_closed_form (α := 1) (β := 0)
        (p := p) (by norm_num) hp (by norm_num)
      simpa [hRstar] using hcurve.trans (by simpa using hcrit)
    rcases hz with ⟨law, hpair⟩
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    have hD : stochasticClippingRatio law.μ 1 0 p τ law.X = c_p p := by
      have := congrArg Prod.snd hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair, hdmax] using this
    have hV : stochasticClippingRatio law.μ 0 1 p τ law.X = w := by
      have := congrArg Prod.fst hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
    have hwlt : w < rareEnergy p R := by
      rw [← hV]
      exact maxBias_energy_lt law.μ hp hp2 hτ law.X law.memLp law.moment_pos hD
    exact ⟨R, hR, le_refl _, by simpa [hdmax] using hRbias, hnonneg.1, hwlt⟩
  · have hdstrict : d < c_p p := lt_of_le_of_ne hdle hdmax
    obtain ⟨r, hr1, hrR, hrd, hwlt⟩ :=
      exists_rareRadius_above_attainable_energy hp hp2 hτ
        hdpos hdstrict hz
    exact ⟨r, hr1, hrR.le, hrd, hnonneg.1, hwlt⟩

/-- Every point in the parametric region is attained. -/
theorem rareEnvelopeRegion_subset_articleAttainablePairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hτ : 0 < τ) :
    rareEnvelopeRegion p ⊆ articleAttainablePairs.{u, v} H p τ := by
  intro z hz
  rcases hz with hbottom | ⟨r, hr1, _hrR, hrd, hw0, hwlt⟩
  · rcases z with ⟨w, d⟩
    rcases hbottom with ⟨hd, hw0, hw1⟩
    change d = 0 at hd
    subst d
    exact article_bottom_edge_mem hp hτ hw0 hw1
  · rcases z with ⟨w, d⟩
    change rareBias p r = d at hrd
    rw [← hrd]
    exact rareBoundary_leftSegment_mem_attainable hp hτ hr1.le hw0 hwlt

/-- The exact attainable set in a nontrivial Hilbert space, in radius
coordinates.  Together with the closed convex hull formula this is precisely
the article's Theorem 4.1. -/
theorem articleAttainablePairs_eq_rareEnvelopeRegion
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ = rareEnvelopeRegion p := by
  exact Set.Subset.antisymm
    (articleAttainablePairs_subset_rareEnvelopeRegion hp hp2 hτ)
    (rareEnvelopeRegion_subset_articleAttainablePairs hp hτ)

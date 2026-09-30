import H099.SignedSupport
import H099.AttainableClassification
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Closed convex hull of the attainable bias--energy set

The support inequalities determine the closed convex hull.  The explicit
boundary function is introduced here as a separate step.
-/

noncomputable section

open Set

universe u v

/-- The intersection of the article's signed support half-spaces. -/
def signedSupportRegion (p : ℝ) : Set (ℝ × ℝ) :=
  {z | ∀ α β : ℝ,
    α * z.2 + β * z.1 ≤ signedSupportFormula α β p}

/-- The transition energy coordinate in the explicit hull boundary. -/
def criticalEnergy (p : ℝ) : ℝ := ((p - 1) / p) ^ p

/-- The explicit upper boundary of the closed convex hull in `(energy,bias)`
coordinates. -/
def upperBoundaryF (p v : ℝ) : ℝ :=
  if v ≤ criticalEnergy p then c_p p else v ^ ((p - 1) / p) - v

/-- The explicit closed region bounded by the graph of `upperBoundaryF`. -/
def closedHullRegion (p : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ upperBoundaryF p z.1}

lemma rareEnergy_criticalRadius_eq {p : ℝ} (hp : 1 < p) :
    rareEnergy p (p / (p - 1)) = criticalEnergy p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hR : 0 < p / (p - 1) := div_pos hp0 hpm
  rw [rareEnergy, Real.rpow_neg hR.le]
  change ((p / (p - 1)) ^ p)⁻¹ = ((p - 1) / p) ^ p
  rw [Real.div_rpow hp0.le hpm.le, Real.div_rpow hpm.le hp0.le]
  field_simp

lemma rareBias_criticalRadius_eq {p : ℝ} (hp : 1 < p) :
    rareBias p (p / (p - 1)) = c_p p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hR : 1 ≤ p / (p - 1) := by
    apply (le_div_iff₀ hpm).2
    linarith
  have hRstar : r_star 1 0 p = p / (p - 1) := by
    simp [r_star]
  have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := 0)
    (r := p / (p - 1)) hR
  rw [← hRstar, F_at_r_star (by norm_num) hp (by norm_num)] at hcurve
  have hcrit := criticalValue_closed_form (α := 1) (β := 0) (p := p)
    (by norm_num) hp (by norm_num)
  simpa [hRstar] using hcurve.trans (by simpa using hcrit)

/-- The rare radius corresponding to an energy coordinate in the curved
branch. -/
def radiusOfEnergy (p v : ℝ) : ℝ := v ^ (-p)⁻¹

lemma rareEnergy_radiusOfEnergy {p v : ℝ} (hp : 1 < p) (hv : 0 < v) :
    rareEnergy p (radiusOfEnergy p v) = v := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  dsimp [rareEnergy, radiusOfEnergy]
  exact Real.rpow_inv_rpow hv.le (by linarith : -p ≠ 0)

lemma radiusOfEnergy_pos {p v : ℝ} (hp : 1 < p) (hv : 0 < v) :
    0 < radiusOfEnergy p v := by
  exact Real.rpow_pos_of_pos hv _

lemma one_le_radiusOfEnergy {p v : ℝ} (hp : 1 < p)
    (hv : 0 < v) (hv1 : v ≤ 1) : 1 ≤ radiusOfEnergy p v := by
  have hneg : (-p)⁻¹ < 0 := inv_neg''.2 (by linarith : -p < 0)
  have h := (Real.rpow_le_rpow_iff_of_neg (x := 1) (y := v)
    one_pos hv hneg).2 hv1
  simpa [radiusOfEnergy] using h

lemma radiusOfEnergy_le_criticalRadius {p v : ℝ} (hp : 1 < p)
    (hv : criticalEnergy p ≤ v) (hv0 : 0 < v) :
    radiusOfEnergy p v ≤ p / (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hR : 0 < p / (p - 1) := div_pos hp0 hpm
  have hRpow : (p / (p - 1)) ^ (-p) = criticalEnergy p := by
    simpa [rareEnergy] using rareEnergy_criticalRadius_eq hp
  have hrpow : (radiusOfEnergy p v) ^ (-p) = v := by
    simpa [rareEnergy] using rareEnergy_radiusOfEnergy hp hv0
  have hpow :
      (p / (p - 1)) ^ (-p) ≤ (radiusOfEnergy p v) ^ (-p) := by
    rw [hRpow, hrpow]
    exact hv
  exact (Real.rpow_le_rpow_iff_of_neg hR
    (radiusOfEnergy_pos hp hv0) (by linarith : -p < 0)).1 hpow

lemma rareBias_radiusOfEnergy {p v : ℝ} (hp : 1 < p) (hv : 0 < v) :
    rareBias p (radiusOfEnergy p v) =
      v ^ ((p - 1) / p) - v := by
  rw [rareBias_eq_energy_rpow_sub_energy (by linarith : 0 < p)
    (radiusOfEnergy_pos hp hv), rareEnergy_radiusOfEnergy hp hv]

lemma signedSupportFormula_eq_K_p {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    signedSupportFormula α β p = K_p α β p := by
  have hβn : ¬ β < 0 := not_lt_of_ge hβ
  by_cases hreg : α ≤ p * β
  · simp [signedSupportFormula, hβn, hreg, K_p]
  · simp [signedSupportFormula, hβn, hreg, K_p]

lemma criticalEnergy_lt_one {p : ℝ} (hp : 1 < p) : criticalEnergy p < 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq : 0 < (p - 1) / p := div_pos (sub_pos.mpr hp) hp0
  have hq1 : (p - 1) / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  dsimp [criticalEnergy]
  exact Real.rpow_lt_one hq.le hq1 hp0

lemma one_le_K_p_eq_signedSupportFormula {p : ℝ} (hp : 1 < p) :
    signedSupportFormula 1 (1 / p) p = 1 / p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hmul : p * (1 / p) = 1 := by field_simp [hp0.ne']
  have hreg : (1 : ℝ) ≤ p * (1 / p) := by rw [hmul]
  have hreg' : (1 : ℝ) ≤ p * p⁻¹ := by simpa [one_div] using hreg
  have hβ : 0 ≤ (1 / p : ℝ) := by positivity
  unfold signedSupportFormula
  rw [if_neg (not_lt_of_ge hβ), if_pos hreg]

lemma criticalRadius_support_eq
    {p α β : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    α * c_p p + β * criticalEnergy p ≤ K_p α β p := by
  by_cases hzero : α = 0 ∧ β = 0
  · simp [hzero.1, hzero.2, K_p]
  have hnonzero : 0 < α ∨ 0 < β := by
    by_cases hα0 : α = 0
    · right
      have hβ0 : β ≠ 0 := by
        intro hβ0
        exact hzero ⟨hα0, hβ0⟩
      exact lt_of_le_of_ne hβ (Ne.symm hβ0)
    · left
      exact lt_of_le_of_ne hα (Ne.symm hα0)
  have hmax := rareCurve_support_isGreatest hα hβ hp hp2 hnonzero
  have hR : 1 ≤ p / (p - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hp)).2
    linarith
  have hpoint :
      (β * rareEnergy p (p / (p - 1)) +
        α * rareBias p (p / (p - 1))) ∈
        (fun z : ℝ × ℝ => β * z.1 + α * z.2) '' rareCurve p := by
    refine ⟨(rareEnergy p (p / (p - 1)), rareBias p (p / (p - 1))), ?_, rfl⟩
    exact ⟨p / (p - 1), hR, rfl⟩
  have hle := hmax.2 hpoint
  rw [rareEnergy_criticalRadius_eq hp, rareBias_criticalRadius_eq hp] at hle
  nlinarith [hle]

/-- The continuous linear functional with coefficients in the article's
`(energy,bias)` coordinate order. -/
def biasEnergyFunctional (α β : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  α • ContinuousLinearMap.snd ℝ ℝ ℝ + β • ContinuousLinearMap.fst ℝ ℝ ℝ

lemma biasEnergyFunctional_apply (α β : ℝ) (z : ℝ × ℝ) :
    biasEnergyFunctional α β z = α * z.2 + β * z.1 := by
  simp [biasEnergyFunctional, smul_eq_mul]

lemma continuousLinearMap_prod_apply (f : ℝ × ℝ →L[ℝ] ℝ) (z : ℝ × ℝ) :
    f z = z.1 * f (1, 0) + z.2 * f (0, 1) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by
    ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

lemma upperBoundaryF_le_cp {p v : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : upperBoundaryF p v ≤ c_p p := by
  by_cases hflat : v ≤ criticalEnergy p
  · simp [upperBoundaryF, hflat]
  · have hvcrit : criticalEnergy p < v := lt_of_not_ge hflat
    have hcpos : 0 < criticalEnergy p := by
      dsimp [criticalEnergy]
      exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
        (zero_lt_one.trans hp)) _
    have hvpos : 0 < v := lt_trans hcpos hvcrit
    let r := radiusOfEnergy p v
    have hr1 : 1 ≤ r := one_le_radiusOfEnergy hp hvpos hv1
    have hrr : r ≤ p / (p - 1) :=
      radiusOfEnergy_le_criticalRadius hp hvcrit.le hvpos
    have hbias : rareBias p r = v ^ ((p - 1) / p) - v :=
      rareBias_radiusOfEnergy hp hvpos
    have hmax := rareCurve_support_isGreatest
      (p := p) (α := 1) (β := 0) (by norm_num) (by norm_num)
      hp hp2 (Or.inl (by norm_num))
    have hpoint : (0 * rareEnergy p r + 1 * rareBias p r) ∈
        ((fun z : ℝ × ℝ => 0 * z.1 + 1 * z.2) '' rareCurve p) := by
      refine ⟨(rareEnergy p r, rareBias p r), ⟨r, hr1, rfl⟩, ?_⟩
      ring
    have hle : rareBias p r ≤ K_p 1 0 p := by
      have h := hmax.2 hpoint
      simpa using h
    have hK : K_p 1 0 p = c_p p := by
      simp [K_p, c_p]
    rw [hK] at hle
    rw [upperBoundaryF, if_neg (not_le_of_gt hvcrit), ← hbias]
    exact hle

lemma radiusOfEnergy_curved_bounds {p v : ℝ} (hp : 1 < p)
    (hvcrit : criticalEnergy p < v) (hv1 : v < 1) :
    1 < radiusOfEnergy p v ∧ radiusOfEnergy p v ≤ p / (p - 1) := by
  have hvpos : 0 < v := by
    have hcpos : 0 < criticalEnergy p := by
      dsimp [criticalEnergy]
      exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
        (zero_lt_one.trans hp)) _
    exact lt_trans hcpos hvcrit
  have hr1 : 1 ≤ radiusOfEnergy p v := one_le_radiusOfEnergy hp hvpos hv1.le
  have hstrict : radiusOfEnergy p v ≠ 1 := by
    intro heq
    have he : rareEnergy p (radiusOfEnergy p v) = rareEnergy p 1 := by rw [heq]
    rw [rareEnergy_radiusOfEnergy hp hvpos] at he
    have : v = 1 := by simpa [rareEnergy] using he
    linarith
  refine ⟨lt_of_le_of_ne hr1 (Ne.symm hstrict), ?_⟩
  exact radiusOfEnergy_le_criticalRadius hp hvcrit.le hvpos

lemma curvedBoundary_has_supporting_direction {p v : ℝ}
    (hp : 1 < p) (hvcrit : criticalEnergy p < v)
    (hv1 : v < 1) :
    ∃ ell : ℝ, 0 ≤ ell ∧ p * ell < 1 ∧
      K_p 1 ell p = upperBoundaryF p v + ell * v := by
  have hvpos : 0 < v := by
    have hcpos : 0 < criticalEnergy p := by
      dsimp [criticalEnergy]
      exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
        (zero_lt_one.trans hp)) _
    exact lt_trans hcpos hvcrit
  let r := radiusOfEnergy p v
  have hrbounds := radiusOfEnergy_curved_bounds hp hvcrit hv1
  let ell := 1 - ((p - 1) / p) * r
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq : 0 < (p - 1) / p := div_pos (sub_pos.mpr hp) hp0
  have hqr : ((p - 1) / p) * r ≤ 1 := by
    calc
      ((p - 1) / p) * r ≤ ((p - 1) / p) * (p / (p - 1)) :=
        mul_le_mul_of_nonneg_left hrbounds.2 hq.le
      _ = 1 := by field_simp [hp0.ne', (sub_pos.mpr hp).ne']
  have hell : 0 ≤ ell := by dsimp [ell]; linarith
  have hpell : p * ell < 1 := by
    dsimp [ell]
    have hmul : p * ((p - 1) / p) = p - 1 := by field_simp [hp0.ne']
    rw [mul_sub, mul_one]
    rw [show p * ((p - 1) / p * r) = (p - 1) * r by
      rw [← mul_assoc, hmul]]
    nlinarith [hrbounds.1]
  have hstar : r_star 1 ell p = r := by
    dsimp [r_star, ell]
    field_simp [hp0.ne', (sub_pos.mpr hp).ne']
    ring
  have hF : F 1 ell p r = K_p 1 ell p := by
    rw [← hstar, F_at_r_star hell hp hpell, K_p_eq_criticalValue hell hp hpell]
  have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := ell)
    (r := r) hrbounds.1.le
  have henergy : rareEnergy p r = v := rareEnergy_radiusOfEnergy hp hvpos
  have hbias : rareBias p r = upperBoundaryF p v := by
    rw [rareBias_radiusOfEnergy hp hvpos]
    simp [upperBoundaryF, not_le_of_gt hvcrit]
  rw [hF] at hcurve
  rw [henergy, hbias] at hcurve
  refine ⟨ell, hell, hpell, ?_⟩
  nlinarith [hcurve]

lemma signedSupportRegion_subset_closedHullRegion {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) :
    signedSupportRegion p ⊆ closedHullRegion p := by
  intro z hz
  have hd0 : 0 ≤ z.2 := by
    have h := hz (-1) 0
    norm_num [signedSupportFormula] at h ⊢
    linarith
  have hv0 : 0 ≤ z.1 := by
    have h := hz 0 (-1)
    norm_num [signedSupportFormula] at h ⊢
    linarith
  have hv1 : z.1 ≤ 1 := by
    have h := hz 0 1
    have hform : signedSupportFormula 0 1 p = 1 := by
      simp [signedSupportFormula, show (0 : ℝ) ≤ p by linarith]
    rw [hform] at h
    simpa using h
  have hdc : z.2 ≤ c_p p := by
    have h := hz 1 0
    have hform : signedSupportFormula 1 0 p = c_p p := by
      have hp0 : 0 < p := zero_lt_one.trans hp
      simp [signedSupportFormula, K_p, c_p, hp0.le]
    rw [hform] at h
    simpa using h
  have hdb : z.2 ≤ upperBoundaryF p z.1 := by
    by_cases hflat : z.1 ≤ criticalEnergy p
    · simpa [upperBoundaryF, hflat] using hdc
    · have hvcrit : criticalEnergy p < z.1 := lt_of_not_ge hflat
      by_cases hvend : z.1 = 1
      · have hsupport := hz 1 (1 / p)
        rw [one_le_K_p_eq_signedSupportFormula hp] at hsupport
        rw [hvend] at hsupport
        have hv0p : 0 < p := zero_lt_one.trans hp
        have hvform : upperBoundaryF p 1 = 0 := by
          simp [upperBoundaryF, criticalEnergy_lt_one hp]
        have hdz : z.2 ≤ 0 := by nlinarith [hsupport]
        simpa [hvend, hvform] using hdz
      · have hvlt : z.1 < 1 := by
          rcases lt_or_eq_of_le hv1 with hlt | heq
          · exact hlt
          · exact False.elim (hvend heq)
        obtain ⟨ell, hell, hpell, hK⟩ :=
          curvedBoundary_has_supporting_direction (p := p) (v := z.1)
            hp hvcrit hvlt
        have hsupport := hz 1 ell
        have hform : signedSupportFormula 1 ell p = K_p 1 ell p := by
          apply signedSupportFormula_eq_K_p (by norm_num) hell
        rw [hform, hK] at hsupport
        nlinarith
  exact ⟨hv0, hv1, hd0, hdb⟩

lemma closedHullRegion_subset_signedSupportRegion {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) :
    closedHullRegion p ⊆ signedSupportRegion p := by
  intro z hz α β
  rcases hz with ⟨hv0, hv1, hd0, hdf⟩
  have hdc : z.2 ≤ c_p p :=
    (hdf.trans (upperBoundaryF_le_cp hp hp2 hv0 hv1))
  have henv : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * z.2 + b * z.1 ≤ K_p a b p := by
    intro a b ha hb
    by_cases hzero : a = 0 ∧ b = 0
    · simp [hzero.1, hzero.2]
    · by_cases hflat : z.1 ≤ criticalEnergy p
      · have hcritical := criticalRadius_support_eq hp hp2 ha hb
        have hterms : a * z.2 + b * z.1 ≤
            a * c_p p + b * criticalEnergy p := by
          have h1 := mul_le_mul_of_nonneg_left hdf ha
          have h2 := mul_le_mul_of_nonneg_left hflat hb
          simpa [upperBoundaryF, hflat] using add_le_add h1 h2
        exact hterms.trans hcritical
      · have hvcrit : criticalEnergy p < z.1 := lt_of_not_ge hflat
        by_cases hvend : z.1 = 1
        · have hvalue : z.2 ≤ 0 := by
            have hupper : upperBoundaryF p 1 = 0 := by
              simp [upperBoundaryF, criticalEnergy_lt_one hp]
            have hzupper := hdf
            rw [hvend, hupper] at hzupper
            exact hzupper
          have h0 : z.2 = 0 := le_antisymm hvalue hd0
          rw [h0, hvend]
          simpa [F] using (F_le_K_p ha hb hp hp2 zero_lt_one)
        · have hvlt : z.1 < 1 := by
            rcases lt_or_eq_of_le hv1 with hlt | heq
            · exact hlt
            · exact False.elim (hvend heq)
          let r := radiusOfEnergy p z.1
          have hrbounds := radiusOfEnergy_curved_bounds hp hvcrit hvlt
          have henergy : rareEnergy p r = z.1 :=
            rareEnergy_radiusOfEnergy hp (lt_trans (by
              have hcpos : 0 < criticalEnergy p := by
                dsimp [criticalEnergy]
                exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
                  (zero_lt_one.trans hp)) _
              exact hcpos) hvcrit)
          have hbias : rareBias p r = upperBoundaryF p z.1 := by
            rw [rareBias_radiusOfEnergy hp (lt_trans (by
              have hcpos : 0 < criticalEnergy p := by
                dsimp [criticalEnergy]
                exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
                  (zero_lt_one.trans hp)) _
              exact hcpos) hvcrit)]
            simp [upperBoundaryF, not_le_of_gt hvcrit]
          have hboundary : a * upperBoundaryF p z.1 + b * z.1 ≤ K_p a b p := by
            have hf := F_le_K_p ha hb hp hp2 (radiusOfEnergy_pos hp
              (lt_trans (by
                have hcpos : 0 < criticalEnergy p := by
                  dsimp [criticalEnergy]
                  exact Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hp)
                    (zero_lt_one.trans hp)) _
                exact hcpos) hvcrit))
            have hcurve := rareCurve_support_eq_F (p := p) (α := a) (β := b)
              (r := r) hrbounds.1.le
            rw [henergy, hbias] at hcurve
            have hcurve' : a * upperBoundaryF p z.1 + b * z.1 =
                F a b p r := by nlinarith [hcurve]
            have hf' : F a b p r ≤ K_p a b p := hf
            exact hcurve'.le.trans hf'
          have hterms : a * z.2 + b * z.1 ≤
              a * upperBoundaryF p z.1 + b * z.1 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hdf ha) le_rfl
          exact hterms.trans hboundary
  exact signed_linear_form_le_formula_of_envelope hp hv0 hd0 hv1 hdc henv
    (α := α) (β := β)

/-- The closed convex hull equals the intersection of the support half-spaces
given by the four-branch signed support formula. -/
theorem closedConvexHull_articleAttainablePairs_eq_signedSupportRegion
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    closedConvexHull ℝ (articleAttainablePairs.{u, v} H p τ) =
      signedSupportRegion p := by
  let A := articleAttainablePairs.{u, v} H p τ
  let C := closedConvexHull ℝ A
  apply Set.Subset.antisymm
  · intro z hz α β
    have hA : A ⊆ {x : ℝ × ℝ | α * x.2 + β * x.1 ≤ signedSupportFormula α β p} := by
      intro x hx
      have hLUB := articleSignedValues_isLUB
        (H := H) hp hp2 hτ (α := α) (β := β)
      exact hLUB.1 ⟨x, hx, rfl⟩
    have hclosed : IsClosed
        {x : ℝ × ℝ | α * x.2 + β * x.1 ≤ signedSupportFormula α β p} := by
      exact isClosed_Iic.preimage (biasEnergyFunctional α β).continuous
    have hconv : Convex ℝ
        {x : ℝ × ℝ | α * x.2 + β * x.1 ≤ signedSupportFormula α β p} := by
      have hf : IsLinearMap ℝ (fun x : ℝ × ℝ => α * x.2 + β * x.1) := by
        constructor
        · intro x y
          simp only [Prod.fst_add, Prod.snd_add]
          ring
        · intro c x
          change α * (c * x.2) + β * (c * x.1) = c * (α * x.2 + β * x.1)
          ring
      exact convex_halfSpace_le hf _
    have hz' := closedConvexHull_min hA hconv hclosed hz
    exact hz'
  · intro z hz
    by_contra hnot
    obtain ⟨f, c, hfC, hcz⟩ :=
      geometric_hahn_banach_closed_point
        (convex_closedConvexHull (𝕜 := ℝ) (s := A))
        isClosed_closedConvexHull hnot
    let α := f (0, 1)
    let β := f (1, 0)
    have hsupport : signedSupportFormula α β p ≤ c := by
      have hLUB := articleSignedValues_isLUB
        (H := H) hp hp2 hτ (α := α) (β := β)
      apply hLUB.2
      intro s hs
      rcases hs with ⟨x, hx, rfl⟩
      have hxC : x ∈ closedConvexHull ℝ A :=
        subset_closedConvexHull hx
      have hfx : f x < c := hfC x hxC
      have hcoords := continuousLinearMap_prod_apply f x
      rw [hcoords] at hfx
      dsimp [α, β]
      nlinarith [hfx]
    have hz' := hz α β
    have hcoords := continuousLinearMap_prod_apply f z
    dsimp [α, β] at hsupport hz'
    have hval : f z ≤ signedSupportFormula α β p := by
      rw [hcoords]
      nlinarith [hz']
    linarith

/-- The explicit piecewise region is exactly the intersection of the article's
signed-support half-spaces. -/
theorem closedHullRegion_eq_signedSupportRegion {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) :
    closedHullRegion p = signedSupportRegion p := by
  apply Set.Subset.antisymm
  · exact closedHullRegion_subset_signedSupportRegion hp hp2
  · exact signedSupportRegion_subset_closedHullRegion hp hp2

/-- Explicit closed convex hull formula, with the article's exact attainable
set of arbitrary Hilbert-valued laws. -/
theorem closedConvexHull_articleAttainablePairs_eq_closedHullRegion
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    closedConvexHull ℝ (articleAttainablePairs.{u, v} H p τ) =
      closedHullRegion p := by
  rw [closedConvexHull_articleAttainablePairs_eq_signedSupportRegion hp hp2 hτ,
    ← closedHullRegion_eq_signedSupportRegion hp hp2]

import SharpRadialClipping.Scalar

/-!
# Maximizers on the rare-shock arc

The support-function description of SharpRadialClipping uses the compact radius interval
`[1, p / (p - 1)]`.  This module proves that every nonzero nonnegative
support direction has a maximizing radius in that interval.
-/

noncomputable section

/-- Every nonzero nonnegative direction has a scalar maximizer on the
rare-shock arc. -/
theorem exists_maximizer_in_rare_arc
    {α β p : ℝ} (_hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (_hnonzero : 0 < α ∨ 0 < β) :
    ∃ r : ℝ,
      1 ≤ r ∧ r ≤ p / (p - 1) ∧
        F α β p r = K_p α β p := by
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have harc : 1 ≤ p / (p - 1) := by
    apply (le_div_iff₀ hpm).2
    linarith
  by_cases hreg : α ≤ p * β
  · refine ⟨1, le_rfl, harc, ?_⟩
    simp [F, K_p, hreg]
  · have hreg' : p * β < α := lt_of_not_ge hreg
    have hαpos : 0 < α := by nlinarith
    have hden : 0 < α * (p - 1) := mul_pos hαpos hpm
    have hupper : r_star α β p ≤ p / (p - 1) := by
      rw [r_star]
      apply (div_le_iff₀ hden).2
      have hpmne : p - 1 ≠ 0 := hpm.ne'
      field_simp [hpmne]
      nlinarith
    refine ⟨r_star α β p, (one_lt_r_star hβ hp hreg').le,
      hupper, ?_⟩
    rw [F_at_r_star hβ hp hreg', K_p_eq_criticalValue hβ hp hreg']

/-- At the zero direction every positive radius, hence every point of the
rare-shock arc, is maximizing. -/
theorem every_rare_arc_radius_maximizes_zero
    {p r : ℝ} (_hp : 1 < p) (_hr : 1 ≤ r)
    (_hrmax : r ≤ p / (p - 1)) :
    F 0 0 p r = K_p 0 0 p :=
  every_radius_maximizes_zero_weights

/-- Limiting normalized energy coordinate of the rare-shock curve. -/
def rareEnergy (p r : ℝ) : ℝ := r ^ (-p)

/-- Limiting normalized bias coordinate of the rare-shock curve. -/
def rareBias (p r : ℝ) : ℝ := (r - 1) * r ^ (-p)

/-- Eliminating the radius from the rare-shock parametrization gives the
explicit bias--energy curve from the article. -/
theorem rareBias_eq_energy_rpow_sub_energy
    {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    rareBias p r =
      (rareEnergy p r) ^ ((p - 1) / p) - rareEnergy p r := by
  have hexp : (-p) * ((p - 1) / p) = 1 - p := by
    field_simp [hp.ne']
    ring
  dsimp only [rareBias, rareEnergy]
  rw [← Real.rpow_mul hr.le, hexp]
  calc
    (r - 1) * r ^ (-p)
        = r * r ^ (-p) - r ^ (-p) := by ring
    _ = r ^ (1 - p) - r ^ (-p) := by
      rw [show 1 - p = 1 + (-p) by ring, Real.rpow_add hr,
        Real.rpow_one]

/-- The limiting rare-shock curve in `(Energy, Bias)` coordinates. -/
def rareCurve (p : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ r : ℝ, 1 ≤ r ∧ z = (rareEnergy p r, rareBias p r)}

/-- Evaluation of a nonnegative support direction on the rare-shock curve is
exactly the scalar objective `F`. -/
lemma rareCurve_support_eq_F
    {α β p r : ℝ} (hr : 1 ≤ r) :
    β * rareEnergy p r + α * rareBias p r = F α β p r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [F_outer_formula hr]
  dsimp only [rareEnergy, rareBias]
  rw [Real.rpow_neg hr0.le p]
  simp only [div_eq_mul_inv]
  ring

/-- In every nonzero nonnegative direction, `K_p` is the greatest support
value of the limiting rare-shock curve. -/
theorem rareCurve_support_isGreatest
    {α β p : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hnonzero : 0 < α ∨ 0 < β) :
    IsGreatest
      ((fun z : ℝ × ℝ => β * z.1 + α * z.2) '' rareCurve p)
      (K_p α β p) := by
  obtain ⟨r, hr1, hrupper, hmax⟩ :=
    exists_maximizer_in_rare_arc hα hβ hp hnonzero
  constructor
  · refine ⟨(rareEnergy p r, rareBias p r), ?_, ?_⟩
    · exact ⟨r, hr1, rfl⟩
    · change β * rareEnergy p r + α * rareBias p r = K_p α β p
      rw [rareCurve_support_eq_F hr1, hmax]
  · intro v hv
    rcases hv with ⟨z, hz, rfl⟩
    rcases hz with ⟨r, hr1, rfl⟩
    change β * rareEnergy p r + α * rareBias p r ≤ K_p α β p
    rw [rareCurve_support_eq_F hr1]
    exact F_le_K_p hα hβ hp hp2 (zero_lt_one.trans_le hr1)

/-- Every point of the rare-shock continuation beyond
`p / (p - 1)` is strictly dominated in both nonnegative coordinates by the
endpoint of the exposed arc. -/
theorem rare_continuation_strictly_dominated
    {p r : ℝ} (hp : 1 < p) (hr : p / (p - 1) < r) :
    rareEnergy p r < rareEnergy p (p / (p - 1)) ∧
      rareBias p r < rareBias p (p / (p - 1)) := by
  let R : ℝ := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hRpos : 0 < R := div_pos hp0 hpm1
  have hRone : 1 < R := by
    dsimp only [R]
    apply (lt_div_iff₀ hpm1).2
    linarith
  have henergy :
      rareEnergy p r < rareEnergy p R := by
    dsimp only [rareEnergy]
    exact Real.rpow_lt_rpow_of_neg hRpos hr (neg_neg_of_pos hp0)
  have hrstar : r_star 1 0 p = R := by
    dsimp only [r_star, R]
    field_simp [hpm1.ne']
    ring
  have hbiasF :
      F 1 0 p r < F 1 0 p R := by
    have hstrict :=
      F_outer_lt_second_regime
        (α := 1) (β := 0) (p := p) (r := r)
        (by norm_num) hp (by norm_num) (hRone.trans hr).le
        (by
          rw [hrstar]
          exact ne_of_gt hr)
    rw [← F_at_r_star (α := 1) (β := 0) (p := p)
      (by norm_num) hp (by norm_num), hrstar] at hstrict
    exact hstrict
  have hbias :
      rareBias p r < rareBias p R := by
    rw [F_outer_formula (hRone.trans hr).le,
      F_outer_formula hRone.le] at hbiasF
    dsimp only [rareBias]
    rw [Real.rpow_neg (zero_lt_one.trans (hRone.trans hr)).le p,
      Real.rpow_neg hRpos.le p]
    simpa only [one_mul, zero_add, add_zero, div_eq_mul_inv] using hbiasF
  simpa only [R] using And.intro henergy hbias

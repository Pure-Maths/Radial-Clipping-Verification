import SharpRadialClipping.AllThresholdsHinge
import SharpRadialClipping.AllThresholdsFiniteLaw

/-!
# Ordering the finite radial shells and assembling their spatial law

The finite shell theorem provides a set of distinct positive radii.  The
folding theorem expects a strictly increasing infinite schedule, with the
radius zero inserted at the start and harmless dummy radii after the final
shell.  We construct that schedule here.
-/

open MeasureTheory

noncomputable section
set_option maxHeartbeats 1000000

local instance : MeasurableSpace SharpRadialClippingR3 := borel SharpRadialClippingR3
local instance : BorelSpace SharpRadialClippingR3 := ⟨rfl⟩

/-- The sorted positive radii of `s`, preceded by zero and followed by an
unbounded arithmetic tail. -/
def finiteRadiusSchedule (s : Finset ℝ) : ℕ → ℝ :=
  Nat.rec 0 (fun n prev =>
    if h : n < s.card then (s.orderEmbOfFin rfl ⟨n, h⟩ : ℝ)
    else prev + 1)

theorem finiteRadiusSchedule_zero (s : Finset ℝ) :
    finiteRadiusSchedule s 0 = 0 := rfl

theorem finiteRadiusSchedule_succ (s : Finset ℝ) (n : ℕ) :
    finiteRadiusSchedule s (n + 1) =
      if h : n < s.card then (s.orderEmbOfFin rfl ⟨n, h⟩ : ℝ)
      else finiteRadiusSchedule s n + 1 := rfl

theorem finiteRadiusSchedule_strictMono (s : Finset ℝ)
    (hs : ∀ a ∈ s, 0 < a) : StrictMono (finiteRadiusSchedule s) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < s.card
  · rw [finiteRadiusSchedule_succ, dif_pos hn]
    cases n with
    | zero =>
        rw [finiteRadiusSchedule_zero]
        exact hs _ (s.orderEmbOfFin_mem rfl ⟨0, hn⟩)
    | succ j =>
        have hj : j < s.card := by omega
        rw [finiteRadiusSchedule_succ, dif_pos hj]
        exact (s.orderEmbOfFin rfl).strictMono (by
          show (⟨j, hj⟩ : Fin s.card) < ⟨j + 1, hn⟩
          change j < j + 1
          omega)
  · rw [finiteRadiusSchedule_succ, dif_neg hn]
    linarith

theorem finiteRadiusSchedule_mem (s : Finset ℝ) (i : ℕ)
    (hi : i ∈ Finset.Ioc 0 s.card) : finiteRadiusSchedule s i ∈ s := by
  have hipos : 0 < i := (Finset.mem_Ioc.mp hi).1
  have hibound : i ≤ s.card := (Finset.mem_Ioc.mp hi).2
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hj : j < s.card := by omega
  rw [finiteRadiusSchedule_succ, dif_pos hj]
  exact s.orderEmbOfFin_mem rfl ⟨j, hj⟩

theorem finiteRadiusSchedule_image (s : Finset ℝ) :
    (Finset.Ioc 0 s.card).image (finiteRadiusSchedule s) = s := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact finiteRadiusSchedule_mem s i hi
  · intro ha
    let j : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨a, ha⟩
    have hj : j.val < s.card := j.isLt
    have hi : j.val + 1 ∈ Finset.Ioc 0 s.card := by
      simp only [Finset.mem_Ioc]
      omega
    apply Finset.mem_image.mpr
    refine ⟨j.val + 1, hi, ?_⟩
    rw [finiteRadiusSchedule_succ, dif_pos hj]
    change (s.orderIsoOfFin rfl j : s).val = a
    simp [j]

theorem finiteRadiusSchedule_sum (s : Finset ℝ)
    (hs : ∀ a ∈ s, 0 < a) {E : Type*}
    [AddCommMonoid E] (f : ℝ → E) :
    (∑ i ∈ Finset.Ioc 0 s.card, f (finiteRadiusSchedule s i)) =
      ∑ a ∈ s, f a := by
  conv_rhs => rw [← finiteRadiusSchedule_image s]
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact (finiteRadiusSchedule_strictMono s hs).injective hij

/-- A finite positive-part hinge path indexed by consecutive radii. -/
def finiteShellHingePath {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m : ℕ) (τ : ℝ) : E :=
  ∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 • w i

theorem finiteShellHingePath_adjacent_difference
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m n : ℕ)
    (hr : StrictMono r) (hnm : n ≤ m) :
    finiteShellHingePath r w m (r (n + 1)) -
        finiteShellHingePath r w m (r n) =
      -(r (n + 1) - r n) •
        ∑ i ∈ Finset.Ioc n m, w i := by
  have hleft : r n ≤ r n := le_rfl
  have hright : r n ≤ r (n + 1) := (hr (by omega : n < n + 1)).le
  rw [finiteShellHingePath, finiteShellHingePath,
    sum_hinges_eq_tail_on_knot_interval r w hr n m hnm (r (n + 1))
      hright le_rfl,
    sum_hinges_eq_tail_on_knot_interval r w hr n m hnm (r n)
      hleft hright]
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar : r i - r (n + 1) - (r i - r n) =
      -(r (n + 1) - r n) := by ring
  rw [← sub_smul, hscalar]

theorem finiteShellHingePath_slope_eq_negative_tail
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m n : ℕ)
    (hr : StrictMono r) (hnm : n ≤ m) :
    finitePathSlope r (fun τ => finiteShellHingePath r w m (r τ)) (n + 1) =
      -(∑ i ∈ Finset.Ioc n m, w i) := by
  have hpred : n + 1 - 1 = n := by omega
  have hgap : r (n + 1) - r n ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hr (by omega : n < n + 1)))
  rw [finitePathSlope, hpred,
    finiteShellHingePath_adjacent_difference r w m n hr hnm]
  rw [smul_smul, mul_neg, inv_mul_cancel₀ hgap, neg_one_smul]

/-- The slope jump at knot `i` is exactly that shell's direction-mean
coefficient.  This is the algebra needed to transfer shell mass bounds to
the folded path. -/
theorem finiteShellHingePath_slope_jump_eq_coefficient
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m i : ℕ)
    (hr : StrictMono r) (hi0 : 0 < i) (him : i ≤ m) :
    finitePathSlope r (fun τ => finiteShellHingePath r w m (r τ)) (i + 1) -
        finitePathSlope r (fun τ => finiteShellHingePath r w m (r τ)) i =
      w i := by
  have hpred : i - 1 + 1 = i := by omega
  have hprev : i - 1 ≤ m := by omega
  have htail : (∑ j ∈ Finset.Ioc (i - 1) m, w j) =
      w i + ∑ j ∈ Finset.Ioc i m, w j := by
    have hsplit := Finset.sum_Ioc_consecutive w (by omega : i - 1 ≤ i) him
    have hsingle : Finset.Ioc (i - 1) i = {i} := by
      calc
        Finset.Ioc (i - 1) i = Finset.Ioc (i - 1) ((i - 1) + 1) := by rw [hpred]
        _ = {i - 1 + 1} := Nat.Ioc_succ_singleton (i - 1)
        _ = {i} := by rw [hpred]
    rw [hsingle, Finset.sum_singleton] at hsplit
    exact hsplit.symm
  rw [finiteShellHingePath_slope_eq_negative_tail r w m i hr him]
  conv_lhs => rhs; rw [← hpred]
  rw [finiteShellHingePath_slope_eq_negative_tail r w m (i - 1) hr hprev,
    htail]
  abel

theorem finiteShellHingePath_zero_of_upper
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m : ℕ) (τ : ℝ)
    (hupper : ∀ i ∈ Finset.Ioc 0 m, r i ≤ τ) :
    finiteShellHingePath r w m τ = 0 := by
  unfold finiteShellHingePath
  apply Finset.sum_eq_zero
  intro i hi
  have hmax : max (r i - τ) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr (hupper i hi))
  simp [hmax]

/-- A threshold before the terminal radius belongs to one of the finitely
many consecutive radius intervals. -/
theorem exists_finite_radius_interval
    (r : ℕ → ℝ) (m : ℕ) (τ : ℝ)
    (h0 : r 0 ≤ τ) (hterminal : τ < r m) :
    ∃ k : ℕ, k < m ∧ r k ≤ τ ∧ τ ≤ r (k + 1) := by
  induction m with
  | zero => exact False.elim (not_lt_of_ge h0 hterminal)
  | succ m ih =>
      by_cases hm : τ < r m
      · obtain ⟨k, hkm, hklo, hkhi⟩ := ih hm
        exact ⟨k, by omega, hklo, hkhi⟩
      · exact ⟨m, by omega, le_of_not_gt hm, hterminal.le⟩

theorem finiteRadiusSchedule_orderIso (s : Finset ℝ) (j : Fin s.card) :
    finiteRadiusSchedule s (j.val + 1) =
      ((s.orderIsoOfFin rfl j : s) : ℝ) := by
  rw [finiteRadiusSchedule_succ, dif_pos j.isLt]
  exact (s.coe_orderIsoOfFin_apply rfl j).symm

/-- The unique positive-knot index associated with a shell. -/
def finiteRadiusIndex (s : Finset ℝ) (a : s) : ℕ :=
  ((s.orderIsoOfFin rfl).symm a).val + 1

theorem finiteRadiusSchedule_index (s : Finset ℝ) (a : s) :
    finiteRadiusSchedule s (finiteRadiusIndex s a) = (a : ℝ) := by
  unfold finiteRadiusIndex
  rw [finiteRadiusSchedule_orderIso]
  simp

theorem finiteRadiusIndex_schedule (s : Finset ℝ) (i : ℕ)
    (hi : i ∈ Finset.Ioc 0 s.card) :
    finiteRadiusIndex s ⟨finiteRadiusSchedule s i,
      finiteRadiusSchedule_mem s i hi⟩ = i := by
  have hi0 : 0 < i := (Finset.mem_Ioc.mp hi).1
  have him : i ≤ s.card := (Finset.mem_Ioc.mp hi).2
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hj : j < s.card := by omega
  unfold finiteRadiusIndex
  have hsub :
      (⟨finiteRadiusSchedule s (j + 1),
        finiteRadiusSchedule_mem s (j + 1) hi⟩ : s) =
        s.orderIsoOfFin rfl ⟨j, hj⟩ := by
    apply Subtype.ext
    exact finiteRadiusSchedule_orderIso s ⟨j, hj⟩
  rw [hsub, (s.orderIsoOfFin rfl).symm_apply_apply]

theorem finiteRadiusSchedule_sum_fintype (s : Finset ℝ)
    (hs : ∀ a ∈ s, 0 < a) {E : Type*} [AddCommMonoid E]
    (f : ℝ → E) :
    (∑ i ∈ Finset.Ioc 0 s.card, f (finiteRadiusSchedule s i)) =
      ∑ a : s, f a := by
  rw [finiteRadiusSchedule_sum s hs f]
  exact (Finset.sum_coe_sort s f).symm

/-- The original shell path is affine between consecutive radial knots. -/
theorem finiteShellHingePath_affine_on_interval
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℕ → ℝ) (w : ℕ → E) (m k : ℕ)
    (hr : StrictMono r) (hkm : k ≤ m)
    (τ : ℝ) (hleft : r k ≤ τ) (hright : τ ≤ r (k + 1)) :
    finiteShellHingePath r w m τ =
      finiteShellHingePath r w m (r k) +
        (τ - r k) •
          finitePathSlope r
            (fun n => finiteShellHingePath r w m (r n)) (k + 1) := by
  rw [finiteShellHingePath_slope_eq_negative_tail r w m k hr hkm,
    smul_neg]
  unfold finiteShellHingePath
  rw [sum_hinges_eq_tail_on_knot_interval r w hr k m hkm τ hleft hright,
    sum_hinges_eq_tail_on_knot_interval r w hr k m hkm (r k)
      le_rfl (hr (by omega : k < k + 1)).le,
    Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar : r i - τ = (r i - r k) - (τ - r k) := by ring
  rw [hscalar, sub_smul]
  abel

/-- The finite folding construction converts a finite family of Hilbert
space shell coefficients into three-dimensional coefficients with the same
radial geometry and no larger individual coefficient norms. -/
theorem exists_folded_finite_shell_coefficients
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ℝ) (hs : ∀ a ∈ s, 0 < a)
    (w : ℝ → H) (q : ℝ → ℝ)
    (hw : ∀ a ∈ s, ‖w a‖ ≤ q a) :
    ∃ v : s → SharpRadialClippingR3,
      (∀ a : s, ‖v a‖ ≤ q (a : ℝ)) ∧
      ∀ τ : ℝ, 0 ≤ τ →
        (‖∑ a : s, max ((a : ℝ) - τ) 0 • w (a : ℝ)‖ =
          ‖∑ a : s, max ((a : ℝ) - τ) 0 • v a‖) ∧
        (‖(∑ a : s, (a : ℝ) • w (a : ℝ)) -
            ∑ a : s, max ((a : ℝ) - τ) 0 • w (a : ℝ)‖ =
          ‖(∑ a : s, (a : ℝ) • v a) -
            ∑ a : s, max ((a : ℝ) - τ) 0 • v a‖) := by
  classical
  let r := finiteRadiusSchedule s
  let m := s.card
  let W : ℕ → H := fun i => w (r i)
  let R : ℝ → H := finiteShellHingePath r W m
  have hr0 : r 0 = 0 := finiteRadiusSchedule_zero s
  have hrmono : StrictMono r := finiteRadiusSchedule_strictMono s hs
  have hrstep : ∀ n, r n < r (n + 1) := fun n => hrmono (by omega)
  obtain ⟨Z, hvertex, hedge, hjump, hsegment⟩ :=
    exists_three_space_vertices_at_radii_with_segments R r hr0 hrstep
  have hRm : R (r m) = 0 := by
    exact finiteShellHingePath_zero_of_upper r W m (r m)
      (fun i hi => hrmono.monotone (Finset.mem_Ioc.mp hi).2)
  have hRafter : R (r (m + 1)) = 0 := by
    exact finiteShellHingePath_zero_of_upper r W m (r (m + 1))
      (fun i hi => hrmono.monotone
        ((Finset.mem_Ioc.mp hi).2.trans (Nat.le_succ m)))
  have hZm : Z m = 0 := by
    have h := (hvertex m).1
    rw [hRm] at h
    exact norm_eq_zero.mp (by simpa using h.symm)
  have hZafter : Z (m + 1) = 0 := by
    have h := (hvertex (m + 1)).1
    rw [hRafter] at h
    exact norm_eq_zero.mp (by simpa using h.symm)
  let V : ℕ → SharpRadialClippingR3 := fun i =>
    finitePathSlope r Z (i + 1) - finitePathSlope r Z i
  let vext : ℝ → SharpRadialClippingR3 := fun a =>
    if h : a ∈ s then V (finiteRadiusIndex s ⟨a, h⟩) else 0
  let v : s → SharpRadialClippingR3 := fun a => vext a
  have hveq (i : ℕ) (hi : i ∈ Finset.Ioc 0 m) :
      vext (r i) = V i := by
    have himem : r i ∈ s := finiteRadiusSchedule_mem s i hi
    simp only [vext, dif_pos himem]
    exact congrArg V (finiteRadiusIndex_schedule s i hi)
  have hVbound (i : ℕ) (hi : i ∈ Finset.Ioc 0 m) :
      ‖V i‖ ≤ q (r i) := by
    have hi0 : 0 < i := (Finset.mem_Ioc.mp hi).1
    have him : i ≤ m := (Finset.mem_Ioc.mp hi).2
    let n := i - 1
    have hin : n + 1 = i := by omega
    have hfold := finite_hinge_coefficient_norm_le r
      (fun j => R (r j)) Z n (hjump n)
    rw [hin] at hfold
    have hin2 : n + 2 = i + 1 := by omega
    rw [hin2] at hfold
    have hsource := finiteShellHingePath_slope_jump_eq_coefficient
      r W m i hrmono hi0 him
    have hsource' :
        finitePathSlope r (fun j => R (r j)) (i + 1) -
          finitePathSlope r (fun j => R (r j)) i = w (r i) := hsource
    rw [hsource'] at hfold
    exact hfold.trans (hw (r i) (finiteRadiusSchedule_mem s i hi))
  have hvbound : ∀ a : s, ‖v a‖ ≤ q (a : ℝ) := by
    intro a
    have haidx : finiteRadiusIndex s a ∈ Finset.Ioc 0 m := by
      unfold finiteRadiusIndex
      simp only [Finset.mem_Ioc]
      constructor
      · omega
      · have := ((s.orderIsoOfFin rfl).symm a).isLt
        omega
    have ha := hVbound (finiteRadiusIndex s a) haidx
    have hri := finiteRadiusSchedule_index s a
    have hva : v a = V (finiteRadiusIndex s a) := by
      simp [v, vext, finiteRadiusIndex]
    rw [hva, ← hri]
    exact ha
  have hRsum (τ : ℝ) :
      R τ = ∑ a : s, max ((a : ℝ) - τ) 0 • w (a : ℝ) := by
    exact finiteRadiusSchedule_sum_fintype s hs
      (fun a => max (a - τ) 0 • w a)
  have hZsum (τ : ℝ) :
      ∑ a : s, max ((a : ℝ) - τ) 0 • v a =
        ∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 • V i := by
    calc
      _ = ∑ a : s, max ((a : ℝ) - τ) 0 • vext (a : ℝ) := rfl
      _ = ∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 • vext (r i) :=
        (finiteRadiusSchedule_sum_fintype s hs
          (fun a => max (a - τ) 0 • vext a)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hveq i hi]
  have hRmean :
      (∑ a : s, (a : ℝ) • w (a : ℝ)) = R 0 := by
    rw [hRsum 0]
    apply Finset.sum_congr rfl
    intro a ha
    have hap : 0 ≤ (a : ℝ) := (hs a a.property).le
    simp [max_eq_left hap]
  have hZmean :
      (∑ a : s, (a : ℝ) • v a) = Z 0 := by
    calc
      _ = ∑ a : s, max ((a : ℝ) - 0) 0 • v a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hap : 0 ≤ (a : ℝ) := (hs a a.property).le
        simp [max_eq_left hap]
      _ = ∑ i ∈ Finset.Ioc 0 m, max (r i - 0) 0 • V i := hZsum 0
      _ = ∑ i ∈ Finset.Ioc 0 m, r i • V i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hip : 0 ≤ r i := (hs (r i)
          (finiteRadiusSchedule_mem s i hi)).le
        simp [max_eq_left hip]
      _ = Z 0 := finite_hinge_weighted_sum_eq_initial r Z hr0 hrmono m
        hZm hZafter
  refine ⟨v, hvbound, ?_⟩
  intro τ hτ
  by_cases hsmall : τ < r m
  · obtain ⟨k, hkm, hkleft, hkright⟩ :=
      exists_finite_radius_interval r m τ (by simpa [hr0] using hτ) hsmall
    have hkm' : k ≤ m := Nat.le_of_lt hkm
    have hgeom := finite_hinge_norms_match_on_interval r
      (fun n => R (r n)) Z hrmono k m hkm' τ hkleft hkright
      hRm hRafter hZm hZafter (hsegment k)
    dsimp at hgeom
    have hsourceHinge :
        (∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 •
          (finitePathSlope r (fun n => R (r n)) (i + 1) -
            finitePathSlope r (fun n => R (r n)) i)) = R τ := by
      rw [finite_hinge_reconstruction_for_path r
        (fun n => R (r n)) hrmono k m hkm' τ hkleft hkright
        hRm hRafter]
      exact (finiteShellHingePath_affine_on_interval r W m k
        hrmono hkm' τ hkleft hkright).symm
    have htargetHinge :
        (∑ i ∈ Finset.Ioc 0 m, max (r i - τ) 0 •
          (finitePathSlope r Z (i + 1) - finitePathSlope r Z i)) =
          ∑ a : s, max ((a : ℝ) - τ) 0 • v a := (hZsum τ).symm
    rw [hsourceHinge, htargetHinge] at hgeom
    rw [← hRsum τ, hRmean, hZmean]
    exact ⟨hgeom.1, by simpa only [hr0, norm_sub_rev] using hgeom.2⟩
  · have hlarge : r m ≤ τ := le_of_not_gt hsmall
    have hRzero : R τ = 0 :=
      finiteShellHingePath_zero_of_upper r W m τ
        (fun i hi => (hrmono.monotone (Finset.mem_Ioc.mp hi).2).trans hlarge)
    have hZzero : (∑ a : s, max ((a : ℝ) - τ) 0 • v a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hidx : finiteRadiusIndex s a ≤ m := by
        unfold finiteRadiusIndex
        have := ((s.orderIsoOfFin rfl).symm a).isLt
        omega
      have hale : (a : ℝ) ≤ τ := by
        calc
          (a : ℝ) = r (finiteRadiusIndex s a) :=
            (finiteRadiusSchedule_index s a).symm
          _ ≤ r m := hrmono.monotone hidx
          _ ≤ τ := hlarge
      have hmax : max ((a : ℝ) - τ) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr hale)
      simp [hmax]
    have hanchor : ‖R 0‖ = ‖Z 0‖ := by
      simpa [hr0] using (hvertex 0).1
    rw [← hRsum τ, hRzero, hZzero, hRmean, hZmean]
    constructor
    · simp
    · simpa using hanchor

/-- Every integrable random vector with finitely many possible radii has
a single three-dimensional law preserving its radial distribution and its
clipping bias and centered energy at every positive threshold. -/
theorem exists_spatial_law_of_finite_radius_source
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : Integrable X (μ : Measure Ω))
    (hfinite : (Set.range fun ω : Ω ↦ ‖X ω‖).Finite) :
    ∃ ν : ProbabilityMeasure SharpRadialClippingR3,
      Measure.map (fun z : SharpRadialClippingR3 ↦ ‖z‖) (ν : Measure SharpRadialClippingR3) =
        Measure.map (fun ω ↦ ‖X ω‖) (μ : Measure Ω) ∧
      ∀ τ : ℝ, 0 < τ →
        ‖(∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)) -
          ∫ ω, X ω ∂(μ : Measure Ω)‖ =
          ‖(∫ z, radialClip τ z ∂(ν : Measure SharpRadialClippingR3)) -
            ∫ z, z ∂(ν : Measure SharpRadialClippingR3)‖ ∧
        (∫ ω, ‖radialClip τ (X ω) -
          ∫ ξ, radialClip τ (X ξ) ∂(μ : Measure Ω)‖ ^ 2
            ∂(μ : Measure Ω)) =
          (∫ z, ‖radialClip τ z -
            ∫ y, radialClip τ y ∂(ν : Measure SharpRadialClippingR3)‖ ^ 2
              ∂(ν : Measure SharpRadialClippingR3)) := by
  classical
  obtain ⟨s, h0, hs, hcover⟩ :=
    exists_positive_radius_finset_of_finite_range X hfinite
  let w : ℝ → H := radialShellCoefficient (μ : Measure Ω) X
  let q : ℝ → ℝ := fun a =>
    (μ : Measure Ω).real {ω | ‖X ω‖ = a}
  have hw : ∀ a ∈ s, ‖w a‖ ≤ q a := by
    intro a ha
    exact norm_radialShellCoefficient_le_measureReal μ X hXm a (hs a ha)
  obtain ⟨v, hv, hgeom⟩ :=
    exists_folded_finite_shell_coefficients s hs w q hw
  have hnonneg : ∀ a ∈ insert 0 s, 0 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | has
    · exact le_refl 0
    · exact (hs a has).le
  have hresidual (τ : ℝ) (hτ : 0 < τ) :
      (∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) =
        ∑ a : s, max ((a : ℝ) - τ) 0 • w (a : ℝ) := by
    have hform := finite_radius_residual_path_formula μ X hXm hX
      (insert 0 s) hcover hnonneg τ hτ
    rw [Finset.sum_insert h0] at hform
    have hzero : max ((0 : ℝ) - τ) 0 • w 0 = 0 := by
      simp [w, radialShellCoefficient]
    rw [hzero, zero_add] at hform
    rw [← Finset.sum_coe_sort s
      (fun a => max (a - τ) 0 • w a)] at hform
    exact hform
  have hmean :
      (∫ ω, X ω ∂(μ : Measure Ω)) =
        ∑ a : s, (a : ℝ) • w (a : ℝ) := by
    have hform := finite_radius_mean_formula μ X hXm hX
      (insert 0 s) hcover hnonneg
    rw [Finset.sum_insert h0] at hform
    have hzero : (0 : ℝ) • w 0 = 0 := by simp
    rw [hzero, zero_add] at hform
    rw [← Finset.sum_coe_sort s (fun a => a • w a)] at hform
    exact hform
  have hresidualGeometry (τ : ℝ) (hτ : 0 < τ) :
      ‖∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖∑ a : s, max ((a : ℝ) - τ) 0 • v a‖ := by
    rw [hresidual τ hτ]
    exact (hgeom τ hτ.le).1
  have hclippedGeometry (τ : ℝ) (hτ : 0 < τ) :
      ‖∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)‖ =
        ‖(∑ a : s, (a : ℝ) • v a) -
          ∑ a : s, max ((a : ℝ) - τ) 0 • v a‖ := by
    have hclip : Integrable (fun ω => radialClip τ (X ω))
        (μ : Measure Ω) := integrable_radialClip hX.1 hτ
    have hdiff := integral_sub hX hclip
    have hrearrange :
        (∫ ω, radialClip τ (X ω) ∂(μ : Measure Ω)) =
          (∫ ω, X ω ∂(μ : Measure Ω)) -
            (∫ ω, X ω - radialClip τ (X ω) ∂(μ : Measure Ω)) := by
      rw [hdiff]
      abel
    rw [hrearrange, hmean, hresidual τ hτ]
    exact (hgeom τ hτ.le).2
  obtain ⟨ν, hradial, htrajectory⟩ :=
    exists_spatial_law_of_finite_shell_geometry μ X hXm hX
      s h0 hs hcover v
      (fun a => by simpa only [q] using hv a)
      hresidualGeometry hclippedGeometry
  exact ⟨ν, hradial.symm, htrajectory⟩

end

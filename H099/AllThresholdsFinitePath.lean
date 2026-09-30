import H099.AllThresholdsLongitudinal

/-!
# A simultaneous three-dimensional finite-path placement

The local folding lemma is iterated while never moving a previously placed
vertex.  The source vertices may be supplied as an infinite sequence; every
finite prefix then gives the finite polygonal construction used in the
all-thresholds theorem.
-/

noncomputable section
set_option maxHeartbeats 1000000

private abbrev PathR3 := EuclideanSpace ℝ (Fin 3)

/-- Three consecutive placed vertices together with their anchor and
adjacent-jump invariants. -/
private structure FinitePathState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℕ → H) (anchor : PathR3) (s t : ℕ → ℝ) (n : ℕ) where
  old : PathR3
  mid : PathR3
  cur : PathR3
  old_norm : ‖R n‖ = ‖old‖
  mid_norm : ‖R (n + 1)‖ = ‖mid‖
  cur_norm : ‖R (n + 2)‖ = ‖cur‖
  old_anchor : ‖R n - R 0‖ = ‖old - anchor‖
  mid_anchor : ‖R (n + 1) - R 0‖ = ‖mid - anchor‖
  cur_anchor : ‖R (n + 2) - R 0‖ = ‖cur - anchor‖
  old_mid : ‖R n - R (n + 1)‖ = ‖old - mid‖
  mid_cur : ‖R (n + 1) - R (n + 2)‖ = ‖mid - cur‖
  jump : ‖s n • (mid - old) - t n • (cur - mid)‖ ≤
    ‖s n • (R (n + 1) - R n) - t n • (R (n + 2) - R (n + 1))‖

/-- Advance a placed triple by one vertex using the full one-step
geometric folding theorem. -/
private noncomputable def finitePathState_advance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℕ → H) (anchor : PathR3) (s t : ℕ → ℝ)
    (hanchor : ‖R 0‖ = ‖anchor‖)
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, 0 < t n)
    (n : ℕ) (st : FinitePathState R anchor s t n) :
    FinitePathState R anchor s t (n + 1) := by
  classical
  have hanchorCur : ‖R 0 - R (n + 2)‖ = ‖anchor - st.cur‖ := by
    simpa [norm_sub_rev] using st.cur_anchor
  have hprevCur : ‖R (n + 1) - R (n + 2)‖ = ‖st.mid - st.cur‖ := st.mid_cur
  let hnext :=
    exists_next_vertex_three_space_with_no_larger_jump
      (R 0) (R (n + 2)) (R (n + 1)) (R (n + 3))
      anchor st.cur st.mid hanchor st.cur_norm hanchorCur
      st.mid_norm st.mid_anchor hprevCur (hs (n + 1)) (ht (n + 1))
  let next' := Classical.choose hnext
  have hnext0 := (Classical.choose_spec hnext).1
  have hnextA := (Classical.choose_spec hnext).2.1
  have hnextCur := (Classical.choose_spec hnext).2.2.1
  have hnextJump := (Classical.choose_spec hnext).2.2.2
  refine {
    old := st.mid
    mid := st.cur
    cur := next'
    old_norm := ?_
    mid_norm := ?_
    cur_norm := ?_
    old_anchor := ?_
    mid_anchor := ?_
    cur_anchor := ?_
    old_mid := ?_
    mid_cur := ?_
    jump := ?_
  }
  · simpa [Nat.add_assoc] using st.mid_norm
  · simpa [Nat.add_assoc] using st.cur_norm
  · simpa [Nat.add_assoc] using hnext0
  · simpa [Nat.add_assoc] using st.mid_anchor
  · simpa [Nat.add_assoc] using st.cur_anchor
  · simpa [Nat.add_assoc] using hnextA
  · simpa [Nat.add_assoc] using st.mid_cur
  · have hdist : ‖R (n + 2) - R (n + 3)‖ = ‖st.cur - next'‖ := by
      calc
        ‖R (n + 2) - R (n + 3)‖ = ‖R (n + 3) - R (n + 2)‖ := norm_sub_rev _ _
        _ = ‖next' - st.cur‖ := hnextCur
        _ = ‖st.cur - next'‖ := norm_sub_rev _ _
    simpa only [Nat.add_assoc] using hdist
  · simpa [Nat.add_assoc] using hnextJump

/-- Initialize the first three placed vertices from a congruent triangle
and one application of the folding theorem. -/
private noncomputable def finitePathState_initial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℕ → H) (s t : ℕ → ℝ)
    (hs : 0 ≤ s 0) (ht : 0 < t 0)
    (anchor first : PathR3)
    (hanchor : ‖R 0‖ = ‖anchor‖)
    (hfirst : ‖R 1‖ = ‖first‖)
    (hfirstAnchor : ‖R 0 - R 1‖ = ‖anchor - first‖) :
    FinitePathState R anchor s t 0 := by
  classical
  have hcurAnchor : ‖R 0 - R 1‖ = ‖anchor - first‖ := hfirstAnchor
  have hprevA : ‖R 0 - R 0‖ = ‖anchor - anchor‖ := by simp
  let hnext := exists_next_vertex_three_space_with_no_larger_jump
    (R 0) (R 1) (R 0) (R 2) anchor first anchor
    hanchor hfirst hcurAnchor hanchor hprevA hfirstAnchor hs ht
  let next' := Classical.choose hnext
  have hnext0 := (Classical.choose_spec hnext).1
  have hnextA := (Classical.choose_spec hnext).2.1
  have hnextCur := (Classical.choose_spec hnext).2.2.1
  have hnextJump := (Classical.choose_spec hnext).2.2.2
  refine {
    old := anchor
    mid := first
    cur := next'
    old_norm := ?_
    mid_norm := ?_
    cur_norm := ?_
    old_anchor := ?_
    mid_anchor := ?_
    cur_anchor := ?_
    old_mid := ?_
    mid_cur := ?_
    jump := ?_
  }
  · simpa using hanchor
  · simpa using hfirst
  · simpa using hnext0
  · simp
  · simpa only [norm_sub_rev] using hfirstAnchor
  · simpa using hnextA
  · simpa using hfirstAnchor
  · have hdist : ‖R 1 - R 2‖ = ‖first - next'‖ := by
      calc
        ‖R 1 - R 2‖ = ‖R 2 - R 1‖ := norm_sub_rev _ _
        _ = ‖next' - first‖ := hnextCur
        _ = ‖first - next'‖ := norm_sub_rev _ _
    simpa using hdist
  · simpa using hnextJump

/-- Every path of source vertices admits a simultaneous placement in the
same Euclidean three-space.  All vertex radii, anchor distances, edge
lengths, and weighted adjacent-slope jump bounds hold at once.  Restricting
the result to any finite initial segment gives the finite-polygonal
construction in the article. -/
theorem exists_three_space_path_with_folded_jumps
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℕ → H) (s t : ℕ → ℝ)
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, 0 < t n) :
    ∃ Z : ℕ → PathR3,
      (∀ n, ‖R n‖ = ‖Z n‖ ∧ ‖R n - R 0‖ = ‖Z n - Z 0‖) ∧
      (∀ n, ‖R n - R (n + 1)‖ = ‖Z n - Z (n + 1)‖) ∧
      (∀ n, ‖s n • (Z (n + 1) - Z n) -
          t n • (Z (n + 2) - Z (n + 1))‖ ≤
        ‖s n • (R (n + 1) - R n) -
          t n • (R (n + 2) - R (n + 1))‖) := by
  classical
  obtain ⟨anchor, first, hanchor, hfirst, hfirstAnchor⟩ :=
    exists_three_space_triangle (R 0) (R 1)
  have hanchor' : ‖R 0‖ = ‖anchor‖ := hanchor.symm
  have hfirst' : ‖R 1‖ = ‖first‖ := hfirst.symm
  have hfirstAnchor' : ‖R 0 - R 1‖ = ‖anchor - first‖ := hfirstAnchor.symm
  let states : (n : ℕ) → FinitePathState R anchor s t n :=
    Nat.rec (finitePathState_initial R s t (hs 0) (ht 0)
      anchor first hanchor' hfirst' hfirstAnchor')
      (fun n st => finitePathState_advance R anchor s t hanchor' hs ht n st)
  let Z : ℕ → PathR3 := fun n => (states n).old
  have hZ0 : Z 0 = anchor := by
    simp [Z, states, finitePathState_initial]
  have hZsucc (n : ℕ) : Z (n + 1) = (states n).mid := by
    rfl
  have hZsucc2 (n : ℕ) : Z (n + 2) = (states n).cur := by
    calc
      Z (n + 2) = (states (n + 1)).mid := by simpa [Nat.add_assoc] using hZsucc (n + 1)
      _ = (states n).cur := by rfl
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro n
    constructor
    · exact (states n).old_norm
    · rw [hZ0]
      exact (states n).old_anchor
  · intro n
    rw [hZsucc]
    exact (states n).old_mid
  · intro n
    rw [hZsucc, hZsucc2]
    exact (states n).jump

/-- The same path theorem in the radius notation of the article.  At the
interior radius `r (n+1)`, the two weights are the reciprocal lengths of
the adjacent radius intervals. -/
theorem exists_three_space_vertices_at_radii
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℝ → H) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ n, r n < r (n + 1)) :
    ∃ Z : ℕ → PathR3,
      (∀ n, ‖R (r n)‖ = ‖Z n‖ ∧
        ‖R (r n) - R 0‖ = ‖Z n - Z 0‖) ∧
      (∀ n, ‖R (r n) - R (r (n + 1))‖ = ‖Z n - Z (n + 1)‖) ∧
      (∀ n,
        ‖(r (n + 1) - r n)⁻¹ • (Z (n + 1) - Z n) -
          (r (n + 2) - r (n + 1))⁻¹ • (Z (n + 2) - Z (n + 1))‖ ≤
        ‖(r (n + 1) - r n)⁻¹ • (R (r (n + 1)) - R (r n)) -
          (r (n + 2) - r (n + 1))⁻¹ •
            (R (r (n + 2)) - R (r (n + 1)))‖) := by
  let s : ℕ → ℝ := fun n => (r (n + 1) - r n)⁻¹
  let t : ℕ → ℝ := fun n => (r (n + 2) - r (n + 1))⁻¹
  have hs : ∀ n, 0 ≤ s n := by
    intro n
    exact (inv_pos.mpr (sub_pos.mpr (hr n))).le
  have ht : ∀ n, 0 < t n := by
    intro n
    exact inv_pos.mpr (sub_pos.mpr (by simpa [Nat.add_assoc] using hr (n + 1)))
  obtain ⟨Z, hvertex, hedge, hjump⟩ :=
    exists_three_space_path_with_folded_jumps
      (fun n => R (r n)) s t hs ht
  refine ⟨Z, ?_, hedge, ?_⟩
  · intro n
    obtain ⟨h0, hanchor⟩ := hvertex n
    exact ⟨h0, by simpa [hr0] using hanchor⟩
  · exact hjump

/-- The vertex placement automatically preserves both required distances
at every point of every linear segment, not only at the vertices. -/
theorem exists_three_space_vertices_at_radii_with_segments
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ℝ → H) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ n, r n < r (n + 1)) :
    ∃ Z : ℕ → PathR3,
      (∀ n, ‖R (r n)‖ = ‖Z n‖ ∧
        ‖R (r n) - R 0‖ = ‖Z n - Z 0‖) ∧
      (∀ n, ‖R (r n) - R (r (n + 1))‖ = ‖Z n - Z (n + 1)‖) ∧
      (∀ n,
        ‖(r (n + 1) - r n)⁻¹ • (Z (n + 1) - Z n) -
          (r (n + 2) - r (n + 1))⁻¹ • (Z (n + 2) - Z (n + 1))‖ ≤
        ‖(r (n + 1) - r n)⁻¹ • (R (r (n + 1)) - R (r n)) -
          (r (n + 2) - r (n + 1))⁻¹ •
            (R (r (n + 2)) - R (r (n + 1)))‖) ∧
      (∀ n (θ : ℝ),
        ‖(1 - θ) • R (r n) + θ • R (r (n + 1))‖ =
          ‖(1 - θ) • Z n + θ • Z (n + 1)‖ ∧
        ‖(1 - θ) • R (r n) + θ • R (r (n + 1)) - R 0‖ =
          ‖(1 - θ) • Z n + θ • Z (n + 1) - Z 0‖) := by
  obtain ⟨Z, hvertex, hedge, hjump⟩ :=
    exists_three_space_vertices_at_radii R r hr0 hr
  refine ⟨Z, hvertex, hedge, hjump, ?_⟩
  intro n θ
  have hA := (hvertex n).1
  have hB := (hvertex (n + 1)).1
  have hAC := (hvertex n).2
  have hBC := (hvertex (n + 1)).2
  have hAB : ‖R (r (n + 1)) - R (r n)‖ =
      ‖Z (n + 1) - Z n‖ := by
    simpa only [norm_sub_rev] using hedge n
  constructor
  · simpa using norm_affineCombination_sub_eq_of_three_distances
      (R (r n)) (R (r (n + 1))) (0 : H)
      (Z n) (Z (n + 1)) (0 : PathR3) θ
      (by simpa using hA) (by simpa using hB) hAB
  · exact norm_affineCombination_sub_eq_of_three_distances
      (R (r n)) (R (r (n + 1))) (R 0)
      (Z n) (Z (n + 1)) (Z 0) θ hAC hBC hAB

import SharpRadialClipping.AllThresholdsGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal folding of a residual-path vertex

These lemmas construct the transverse part of the next vertex in a fixed
orthogonal subspace.  They are the analytic folding step used in the rank-one
and rank-two anchor configurations of the all-thresholds construction.
-/

noncomputable section

/-- Every line or plane in Euclidean three-space has a nonzero normal
direction, which supplies the transverse component used in folding. -/
theorem orthogonal_complement_nontrivial_of_finrank_le_two
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hK : Module.finrank ℝ K ≤ 2) : Nontrivial Kᗮ := by
  have hsum := K.finrank_add_finrank_orthogonal
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp
  rw [hdim] at hsum
  apply (Module.finrank_pos_iff (R := ℝ) (M := Kᗮ)).mp
  omega

/-- If the incoming transverse component lies in a nonzero subspace, choose
the outgoing transverse component in that same subspace, with a prescribed
length, so that the two are aligned. -/
theorem exists_aligned_in_submodule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Submodule ℝ E) [Nontrivial N] (u : E) (hu : u ∈ N)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : E, v ∈ N ∧ ‖v‖ = r ∧ ‖u - v‖ = |‖u‖ - r| := by
  let uN : N := ⟨u, hu⟩
  obtain ⟨vN, hvN, hdistN⟩ :=
    exists_aligned_vector_of_norm uN hr
  refine ⟨vN, vN.property, ?_, ?_⟩
  · simpa using hvN
  · simpa [uN] using hdistN

/-- Folding construction with an explicitly identified longitudinal part.
The new transverse vector is chosen inside `N`; orthogonality to the fixed
longitudinal target part and the reverse triangle inequality then ensure
that the velocity jump cannot grow. -/
theorem exists_folded_transverse_with_no_larger_jump
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Submodule ℝ E) [Nontrivial N]
    (p u v : H) (p' u' : E)
    (hu' : u' ∈ N)
    (hp' : ∀ w ∈ N, inner ℝ p' w = 0)
    (hp : inner ℝ p (u - v) = 0)
    (hpNorm : ‖p'‖ = ‖p‖)
    (huNorm : ‖u'‖ = ‖u‖) :
    ∃ v' : E, v' ∈ N ∧ ‖v'‖ = ‖v‖ ∧
      ‖p' + (u' - v')‖ ≤ ‖p + (u - v)‖ := by
  obtain ⟨v', hv'N, hv'Norm, hAlign⟩ :=
    exists_aligned_in_submodule N u' hu' (r := ‖v‖) (norm_nonneg v)
  refine ⟨v', hv'N, hv'Norm, ?_⟩
  have hdiff : u' - v' ∈ N := N.sub_mem hu' hv'N
  exact folded_jump_le p u v p' u' v'
    hpNorm huNorm hv'Norm hp (hp' (u' - v') hdiff)
    (by simpa [hv'Norm] using hAlign)

/-- The preceding folding result remains valid if the incoming and outgoing
transverse pieces of the source are separately orthogonal to the longitudinal
part.  This is the form naturally produced by orthogonal projection. -/
theorem exists_folded_transverse_of_component_orthogonality
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Submodule ℝ E) [Nontrivial N]
    (p u v : H) (p' u' : E)
    (hu' : u' ∈ N)
    (hp' : ∀ w ∈ N, inner ℝ p' w = 0)
    (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0)
    (hpNorm : ‖p'‖ = ‖p‖)
    (huNorm : ‖u'‖ = ‖u‖) :
    ∃ v' : E, v' ∈ N ∧ ‖v'‖ = ‖v‖ ∧
      ‖p' + (u' - v')‖ ≤ ‖p + (u - v)‖ := by
  apply exists_folded_transverse_with_no_larger_jump N p u v p' u'
    hu' hp' ?_ hpNorm huNorm
  rw [inner_sub_right, hpu, hpv, sub_self]

/-- Once the longitudinal endpoint has been placed with the correct
distance to an anchor, any transverse vector of the correct length and
orthogonal to both longitudinal anchor differences preserves that distance.
This gives all three anchor distances using the *same* transverse choice. -/
theorem norm_folded_vertex_sub_anchor
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x a v : H) (x' a' v' : E)
    (hlong : ‖x - a‖ = ‖x' - a'‖)
    (htrans : ‖v‖ = ‖v'‖)
    (horth : inner ℝ (x - a) v = 0)
    (horth' : inner ℝ (x' - a') v' = 0) :
    ‖(x + v) - a‖ = ‖(x' + v') - a'‖ := by
  have hsource : (x + v) - a = (x - a) + v := by abel
  have htarget : (x' + v') - a' = (x' - a') + v' := by abel
  rw [hsource, htarget]
  have hsq : ‖(x - a) + v‖ ^ 2 = ‖(x' - a') + v'‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real, hlong, htrans, horth, horth']
  nlinarith [norm_nonneg ((x - a) + v), norm_nonneg ((x' - a') + v')]

/-- A common transverse choice simultaneously preserves distances to all
three anchors and contracts the adjacent velocity jump.  The hypotheses are
the orthogonal-projection data of the source and target configurations. -/
theorem exists_folded_vertex_with_three_anchor_distances
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (N : Submodule ℝ E) [Nontrivial N]
    (a : Fin 3 → H) (a' : Fin 3 → E)
    (x v p u : H) (x' p' u' : E)
    (hlong : ∀ i, ‖x - a i‖ = ‖x' - a' i‖)
    (hsourceOrth : ∀ i, inner ℝ (x - a i) v = 0)
    (htargetOrth : ∀ i (w : E), w ∈ N → inner ℝ (x' - a' i) w = 0)
    (hu' : u' ∈ N)
    (hp' : ∀ w ∈ N, inner ℝ p' w = 0)
    (hp : inner ℝ p (u - v) = 0)
    (hpNorm : ‖p'‖ = ‖p‖)
    (huNorm : ‖u'‖ = ‖u‖) :
    ∃ v' : E, v' ∈ N ∧
      (∀ i, ‖(x + v) - a i‖ = ‖(x' + v') - a' i‖) ∧
      ‖p' + (u' - v')‖ ≤ ‖p + (u - v)‖ := by
  obtain ⟨v', hv'N, hv'Norm, hJump⟩ :=
    exists_folded_transverse_with_no_larger_jump N p u v p' u'
      hu' hp' hp hpNorm huNorm
  refine ⟨v', hv'N, ?_, hJump⟩
  intro i
  exact norm_folded_vertex_sub_anchor (x := x) (a := a i) (v := v)
    (x' := x') (a' := a' i) (v' := v') (hlong i) hv'Norm.symm
    (hsourceOrth i) (htargetOrth i v' hv'N)

/-- For any line or plane of anchors in `ℝ³`, the required normal
direction is automatic.  This is the geometric folding interface: all
three radii are retained and the adjacent velocity jump contracts. -/
theorem exists_folded_vertex_for_rank_le_two_anchor_space
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hK : Module.finrank ℝ K ≤ 2)
    (a : Fin 3 → H) (a' : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (x v p u : H) (x' p' u' : EuclideanSpace ℝ (Fin 3))
    (ha' : ∀ i, a' i ∈ K) (hx' : x' ∈ K) (hp' : p' ∈ K)
    (hu' : u' ∈ Kᗮ)
    (hlong : ∀ i, ‖x - a i‖ = ‖x' - a' i‖)
    (hsourceOrth : ∀ i, inner ℝ (x - a i) v = 0)
    (hp : inner ℝ p (u - v) = 0)
    (hpNorm : ‖p'‖ = ‖p‖)
    (huNorm : ‖u'‖ = ‖u‖) :
    ∃ v' : EuclideanSpace ℝ (Fin 3), v' ∈ Kᗮ ∧
      (∀ i, ‖(x + v) - a i‖ = ‖(x' + v') - a' i‖) ∧
      ‖p' + (u' - v')‖ ≤ ‖p + (u - v)‖ := by
  letI : Nontrivial Kᗮ := orthogonal_complement_nontrivial_of_finrank_le_two K hK
  apply exists_folded_vertex_with_three_anchor_distances Kᗮ a a' x v p u x' p' u'
    hlong hsourceOrth ?_ hu' ?_ hp hpNorm huNorm
  · intro i w hw
    exact Submodule.inner_right_of_mem_orthogonal (K.sub_mem hx' (ha' i)) hw
  · intro w hw
    exact Submodule.inner_right_of_mem_orthogonal hp' hw

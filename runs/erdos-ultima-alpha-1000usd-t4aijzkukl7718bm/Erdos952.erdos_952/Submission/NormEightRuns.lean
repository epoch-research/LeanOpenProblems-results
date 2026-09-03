import Submission.NormEightOnly

/-! The norm-eight lift bounds pure norm-eight runs. Mixed-jump rays are not
excluded by this result. -/
namespace Erdos952Investigation.NormEightRuns
open NormEightOnly
set_option maxHeartbeats 0

/-- A simple segment in the allowed residue graph cannot have 65² edges of
squared norm eight. -/
theorem no_long_allowed_segment (x : ℕ → GaussianInt)
    (hx : Set.InjOn x (Set.Iic 4225))
    (ha : ∀ n ≤ 4225, Allowed (residue (x n).re) (residue (x n).im)) :
    ¬ ∀ n < 4225, (x (n+1)-x n).norm = 8 := by
  intro hs
  have hanc (n : ℕ) (hn : n ≤ 4225) :
      anchor (x n).re (x n).im = anchor (x 0).re (x 0).im := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (anchor_norm_eight (ha n (by omega)) (ha (n+1) hn)
        (hs n (by omega))).trans (ih (by omega))
  let f : Fin 4226 → Fin 65 × Fin 65 :=
    fun i => (residue (x i).re,residue (x i).im)
  have hi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hx (by have := i.isLt; change i.val ≤ 4225; omega)
      (by have := j.isLt; change j.val ≤ 4225; omega)
    apply eq_of_anchor_and_residue _ hij
    exact (hanc i (by have := i.isLt; omega)).trans
      (hanc j (by have := j.isLt; omega)).symm
  have hc := Fintype.card_le_of_injective f hi
  norm_num at hc

/-- Eventually every 4225-jump block contains a jump whose squared norm is not
8. No upper bound on jumps is assumed. -/
theorem non_eight_jumps_have_eventually_bounded_gaps (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∃ K : ℕ, ∀ N ≥ K, ∃ n, N ≤ n ∧ n < N+4225 ∧
      (x (n+1)-x n).norm ≠ 8 := by
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx 169
  refine ⟨K,?_⟩
  intro N hN
  by_contra! hnone
  apply no_long_allowed_segment (fun i => x (N+i))
    (fun _ _ _ _ he => Nat.add_left_cancel (hx he))
    (fun i _ => prime_allowed (hp (N+i)) (hK _ (by omega)))
  intro n hn
  have hh := hnone (N+n) (by omega) (by omega)
  simpa only [Nat.add_assoc] using hh

/-- In a hypothetical bound-nine prime ray, jumps strictly below eight also
have bounded gaps eventually. This is consistent with the separately proved
necessity of norm-eight jumps. -/
theorem smaller_jumps_have_eventually_bounded_gaps (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hs : ∀ n, (x (n+1)-x n).norm < 9) :
    ∃ K : ℕ, ∀ N ≥ K, ∃ n, N ≤ n ∧ n < N+4225 ∧
      (x (n+1)-x n).norm < 8 := by
  obtain ⟨K,hK⟩ := non_eight_jumps_have_eventually_bounded_gaps x hx hp
  refine ⟨K,?_⟩
  intro N hN
  obtain ⟨n,hn,hn',hne⟩ := hK N hN
  exact ⟨n,hn,hn',by have := hs n; omega⟩

#print axioms no_long_allowed_segment
#print axioms non_eight_jumps_have_eventually_bounded_gaps
#print axioms smaller_jumps_have_eventually_bounded_gaps
end Erdos952Investigation.NormEightRuns

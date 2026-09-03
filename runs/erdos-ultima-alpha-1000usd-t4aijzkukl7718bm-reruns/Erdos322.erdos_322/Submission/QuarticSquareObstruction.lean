import Submission.Spec

/-! Unbounded primitive quartic counts can have completely unrepresentable squared targets. -/
namespace Erdos322Research.QuarticSquareObstruction

open Erdos322

private lemma fourth_mod_sixteen (x : ℕ) : x^4%16 ≤ 1 := by
  have h : ∀ r : Fin 16, (r.val^4)%16 ≤ 1 := by decide
  have hh := h ⟨x%16,Nat.mod_lt _ (by decide)⟩
  rw [Nat.pow_mod]
  exact hh

/-- The residue of a sum of four fourth powers modulo sixteen is at most four. -/
theorem representationCount_zero_of_mod_sixteen {n : ℕ} (hn : 4 < n%16) :
    representationCount 4 n=0 := by
  unfold representationCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
  have h0 := fourth_mod_sixteen (a 0 : ℕ)
  have h1 := fourth_mod_sixteen (a 1 : ℕ)
  have h2 := fourth_mod_sixteen (a 2 : ℕ)
  have h3 := fourth_mod_sixteen (a 3 : ℕ)
  have he := congrArg (fun x : ℕ ↦ x%16) ha
  simp only [Fin.sum_univ_four] at he
  omega

/-- Every target in the elementary primitive family has an unrepresentable square. -/
theorem primitive_family_square_unrepresented (m : ℕ) :
    representationCount 4 ((2*7^(4*m)+1)^2)=0 := by
  have h7 : 7^(4*m)%16=1 := by
    rw [pow_mul,Nat.pow_mod]
    norm_num
  have hN : (2*7^(4*m)+1)%16=3 := by
    rw [Nat.add_mod,Nat.mul_mod,h7]
  apply representationCount_zero_of_mod_sixteen
  rw [Nat.pow_mod,hN]
  norm_num

/-- Arbitrarily high primitive multiplicity does not ensure that even the
square of the target has any quartic representation. -/
theorem infinitely_many_large_counts_with_unrepresented_square (M : ℕ) :
    {n : ℕ | M < primitiveRepresentationCount 4 n ∧
      representationCount 4 (n^2)=0}.Infinite := by
  have hi : Function.Injective (fun t : ℕ ↦ 2*7^(4*(M+t))+1) := by
    intro a b he
    dsimp only at he
    have hp : 7^(4*(M+a))=7^(4*(M+b)) := by omega
    have hh := Nat.pow_right_injective (by decide : 2 ≤ 7) hp
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨t,rfl⟩
  dsimp only
  exact ⟨by have := primitive_quartic_count_lower (M+t); omega,
    primitive_family_square_unrepresented (M+t)⟩

/-- There is no multiplicity threshold beyond which squaring the target
universally preserves representability. -/
theorem no_eventual_square_amplification :
    ¬ (∃ M : ℕ, ∀ n : ℕ, M < representationCount 4 n →
      0 < representationCount 4 (n^2)) := by
  rintro ⟨M,hM⟩
  obtain ⟨n,hn,hzero⟩ :=
    (infinitely_many_large_counts_with_unrepresented_square M).nonempty
  have hbig : M < representationCount 4 n :=
    hn.trans_le (primitiveRepresentationCount_le 4 n)
  have hh := hM n hbig
  omega

end Erdos322Research.QuarticSquareObstruction

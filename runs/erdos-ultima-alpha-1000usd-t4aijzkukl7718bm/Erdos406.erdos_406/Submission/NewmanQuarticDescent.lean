import Submission.NewmanQuarticBlocks
import Submission.NewmanJointCandidate

/-! An exact descent and finiteness reduction removing the known quartic.
The remaining set of quartic-free candidates is not proved finite here. -/
namespace Erdos406QuarticDescent
open Polynomial Erdos406QuarticBlocks Erdos406QuarticSquare Erdos406SparseTriple
open Erdos406Cyclotomic Erdos406FactorParity Erdos406ReciprocalFlip
  Erdos406ReciprocalCandidate Erdos406FactorBridge

lemma block_eval_three : block.eval 3 = 256 := by
  rw [block_expanded]
  norm_num

/-- Removing the quartic block gives a smaller, six-spaced candidate, and
that smaller candidate cannot itself have the quartic as a factor. -/
theorem candidate_quartic_descent (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0, 1])
    (hd : qQuartic ∣ digitPoly (Nat.digits 3 (2^k))) :
    ∃ j : ℕ, k = j+8 ∧ Nat.digits 3 (2^j) ⊆ [0, 1] ∧ SixSpaced (2^j) ∧
      ¬ qQuartic ∣ digitPoly (Nat.digits 3 (2^j)) := by
  let P := digitPoly (Nat.digits 3 (2^k))
  have hP : Binary P := binary_digitPoly _ hg
  obtain ⟨S, hS, he⟩ := binary_multiple_classification P hP hd
  obtain ⟨n, hn, hsp⟩ := spaced_eval hS
  have hv : (2^k : ℕ) = 256*n := by
    have hh := congrArg (eval (3 : ℤ)) he
    change (digitPoly (Nat.digits 3 (2^k))).eval 3 = (block*S).eval 3 at hh
    rw [digitPoly_eval_three, eval_mul, block_eval_three, hn] at hh
    exact_mod_cast hh
  have hnD : n ∣ 2^k := by rw [hv]; exact dvd_mul_left n 256
  obtain ⟨j, _, hj⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hnD
  have hk : k = j+8 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2^k = 2^(j+8)
    rw [hv, hj, pow_add]
    norm_num
    ring
  have hgj : Nat.digits 3 (2^j) ⊆ [0, 1] := by
    rw [← hj]
    exact (sixSpaced_implies_triple hsp).1
  have hSe : S = digitPoly (Nat.digits 3 (2^j)) := by
    apply binary_eval_three_injective S _ (spaced_binary hS) (binary_digitPoly _ hgj)
    rw [digitPoly_eval_three, hn, hj]
  refine ⟨j, hk, hgj, by rwa [← hj], ?_⟩
  intro hqd
  have hqS : qQuartic ∣ S := by rwa [hSe]
  obtain ⟨T, hT⟩ := hqS
  have hP0 : P.coeff 0 = 1 := by
    exact (candidate_monic_factor k hg P
      (candidate_digitPoly_isMonicOfDegree k hg).monic (dvd_refl P)).1
  apply qQuartic_sq_not_dvd_newman P hP0 hP
  refine ⟨(X+1)*T, ?_⟩
  rw [he, hT]
  unfold block
  ring

def QuarticFree : Set ℕ := {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] ∧
  ¬ qQuartic ∣ digitPoly (Nat.digits 3 n)}

/-- Every candidate is quartic-free, or is 256 times a quartic-free candidate.
The reverse inclusion is not asserted: multiplying by 256 need not preserve
the digit condition for an arbitrary quartic-free candidate. -/
theorem candidate_subset_quartic_free_union :
    {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]} ⊆
      QuarticFree ∪ (fun n : ℕ => 256*n) '' QuarticFree := by
  rintro n ⟨⟨k, rfl⟩, hg⟩
  by_cases hd : qQuartic ∣ digitPoly (Nat.digits 3 (2^k))
  · obtain ⟨j, hk, hgj, _, hfree⟩ := candidate_quartic_descent k hg hd
    right
    refine ⟨2^j, ⟨⟨j,rfl⟩,hgj,hfree⟩, ?_⟩
    rw [hk, pow_add]
    norm_num
    ring
  · exact Or.inl ⟨⟨k,rfl⟩,hg,hd⟩

/-- Exact finiteness reduction. Its right-hand side is still unproved. -/
theorem finite_iff_quartic_free_finite :
    {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔ QuarticFree.Finite := by
  constructor
  · intro h
    exact h.subset (fun n hn => ⟨hn.1,hn.2.1⟩)
  · intro h
    exact (h.union (h.image (fun n : ℕ => 256*n))).subset candidate_subset_quartic_free_union

/-- Thus an infinite set of candidates would already have infinitely many
quartic-free members. This is a conditional statement, not a disproof. -/
theorem infinite_forces_infinitely_many_quartic_free
    (h : ¬ {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    ¬ QuarticFree.Finite := by
  exact fun hf => h (finite_iff_quartic_free_finite.mpr hf)

#print axioms candidate_quartic_descent
#print axioms finite_iff_quartic_free_finite
end Erdos406QuarticDescent

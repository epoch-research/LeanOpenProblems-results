import Submission.RationalLinearFeasibility

/-! Exact rational fractional partitions and finite uniform multicover
certificates. These are not edge-disjoint partitions of the original graph. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
open RationalLinearFeasibility
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma exists_rational_fractional_partition (G : SimpleGraph V)
    (hG : ∀ x, Even (G.degree x)) :
    ∃ q : CyclePiece G → ℚ, (∀ H, 0 ≤ q H) ∧
      (∀ e ∈ G.edgeSet, (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then q H else 0) = 1) ∧
      (∑ H, q H) ≤ 2 * Fintype.card V := by
  obtain ⟨t,ht,hcost⟩ := exists_fractional_partition_linear G hG
  let A : G.edgeSet → CyclePiece G → ℚ := fun e H => if e.val ∈ H.val.edgeSet then 1 else 0
  have hA : ∀ e : G.edgeSet, (∑ H, (A e H : ℝ) * t H) = (1 : ℚ) := by
    intro e
    simpa only [A,apply_ite,Rat.cast_one,Rat.cast_zero,ite_mul,one_mul,zero_mul]
      using ht.2 e.val e.property
  obtain ⟨q,hq,hcov,hb⟩ := exists_nonnegative_rat_combination A (fun _ => 1)
    (2 * Fintype.card V) t ht.1 hA (by exact_mod_cast hcost)
  refine ⟨q,hq,?_,hb⟩
  intro e he
  simpa only [A,ite_mul,one_mul,zero_mul] using hcov ⟨e,he⟩

/-- A positive integer multicover with average cycle count at most 2*n.
The multiplicity m is not asserted to equal one or to be a power of two. -/
lemma exists_uniform_multicover_linear (G : SimpleGraph V)
    (hG : ∀ x, Even (G.degree x)) :
    ∃ (m : ℕ) (k : CyclePiece G → ℕ), 0 < m ∧
      (∀ e ∈ G.edgeSet, (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0) = m) ∧
      (∑ H, k H) ≤ 2 * m * Fintype.card V := by
  obtain ⟨q,hq,hcov,hb⟩ := exists_rational_fractional_partition G hG
  obtain ⟨m,k,hm,hk⟩ := clear_nonnegative_denominators q hq
  refine ⟨m,k,hm,?_,?_⟩
  · intro e he
    have hh : ((∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0 : ℕ) : ℚ) = m := by
      simp only [Nat.cast_sum,apply_ite,Nat.cast_zero,hk]
      rw [show (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then (m : ℚ) * q H else 0) =
          (m : ℚ) * ∑ H : CyclePiece G, if e ∈ H.val.edgeSet then q H else 0 by
        simp only [Finset.mul_sum,mul_ite,mul_zero]]
      rw [hcov e he,mul_one]
    exact_mod_cast hh
  · have heq : ((∑ H, k H : ℕ) : ℚ) = (m : ℚ) * ∑ H, q H := by
      simp only [Nat.cast_sum,hk,Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left hb (show (0 : ℚ) ≤ m from Nat.cast_nonneg m)
    rw [← heq] at hh
    have hh' : ((∑ H, k H : ℕ) : ℚ) ≤ 2 * m * Fintype.card V := by nlinarith
    exact_mod_cast hh'

end Erdos184.FractionalCycles

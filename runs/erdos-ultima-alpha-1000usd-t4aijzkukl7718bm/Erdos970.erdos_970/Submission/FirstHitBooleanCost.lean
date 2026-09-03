import Submission.FirstHitSigned

/-! Exact Boolean coefficient costs for squared first-hit kernels. The improved
criterion remains conditional; no uniform quadratic bound is asserted. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication in the Boolean polynomial algebra merges terms by union. -/
noncomputable def booleanSquareCoefficient (a : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ Q : Finset ι, ∑ R : Finset ι, if Q ∪ R = T then a Q * a R else 0

noncomputable def booleanSquareCost (a : Finset ι → ℝ) : ℝ :=
  ∑ T : Finset ι, |booleanSquareCoefficient a T|

lemma booleanSquare_expansion (a : Finset ι → ℝ) (ω : ι → Bool) :
    (∑ Q : Finset ι, a Q * hitMonomial Q ω) ^ 2 =
      ∑ T : Finset ι, booleanSquareCoefficient a T * hitMonomial T ω := by
  symm
  simp only [booleanSquareCoefficient, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  calc
    _ = ∑ Q : Finset ι, ∑ R : Finset ι, ∑ T : Finset ι,
        if Q ∪ R = T then (a Q * a R) * hitMonomial T ω else 0 := by
      apply sum_congr rfl
      intro Q hQ
      rw [sum_comm]
    _ = ∑ Q : Finset ι, ∑ R : Finset ι, (a Q * a R) * hitMonomial (Q ∪ R) ω := by
      simp
    _ = _ := by
      rw [pow_two, sum_mul_sum]
      apply sum_congr rfl
      intro Q hQ
      apply sum_congr rfl
      intro R hR
      rw [← hitMonomial_mul]
      ring

lemma booleanSquareCost_le (a : Finset ι → ℝ) :
    booleanSquareCost a ≤ (∑ T : Finset ι, |a T|) ^ 2 := by
  calc
    _ ≤ ∑ T : Finset ι, ∑ Q : Finset ι, ∑ R : Finset ι,
        if Q ∪ R = T then |a Q| * |a R| else 0 := by
      apply sum_le_sum
      intro T hT
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro Q hQ
      apply (abs_sum_le_sum_abs _ _).trans_eq
      apply sum_congr rfl
      intro R hR
      split_ifs <;> simp [abs_mul]
    _ = (∑ T : Finset ι, |a T|) ^ 2 := by
      rw [sum_comm]
      calc
        _ = ∑ Q : Finset ι, ∑ R : Finset ι, ∑ T : Finset ι,
            if Q ∪ R = T then |a Q| * |a R| else 0 := by
          apply sum_congr rfl
          intro Q hQ
          rw [sum_comm]
        _ = _ := by simp [pow_two, sum_mul_sum]

lemma booleanSquare_error (q : ι → ℝ) (a : Finset ι → ℝ)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (U : Finset ι) :
    |(∑ j ∈ range m, hitMonomial U (ω j) * (∑ T : Finset ι, a T * hitMonomial T (ω j)) ^ 2) -
      (m : ℝ) * average q (fun v => hitMonomial U v * (∑ T : Finset ι, a T * hitMonomial T v) ^ 2)| ≤
      booleanSquareCost a := by
  have heq (v : ι → Bool) :
      hitMonomial U v * (∑ T : Finset ι, a T * hitMonomial T v) ^ 2 =
      ∑ T : Finset ι, booleanSquareCoefficient a T * hitMonomial (U ∪ T) v := by
    rw [booleanSquare_expansion, mul_sum]
    apply sum_congr rfl
    intro T hT
    rw [← hitMonomial_mul]
    ring
  simp_rw [heq]
  exact finite_polynomial_interval_error univ (booleanSquareCoefficient a)
    (fun T => U ∪ T) q m ω herr

lemma arbitrary_square_hit_boolean_error (q : ι → ℝ) (c : Finset ι → ℝ)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (U : Finset ι) :
    |(∑ j ∈ range m, hitMonomial U (ω j) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * average q (fun v => hitMonomial U v * linearKernel q c v ^ 2)| ≤
      booleanSquareCost (ordinaryCoefficient q c) := by
  simp_rw [linearKernel_expansion]
  exact booleanSquare_error q (ordinaryCoefficient q c) m ω herr U

section Ordered
variable [LinearOrder ι]

/-- The same first-hit construction, retaining cancellations inside each square. -/
theorem survivor_of_first_hit_boolean_cost (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : ι → Finset ι → ℝ)
    (hsum : ∀ i, (∑ Q : Finset ι, c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (∑ i, ((m : ℝ) * q i * (∑ Q : Finset ι, c i Q ^ 2 * variance q Q) +
        booleanSquareCost (ordinaryCoefficient q (c i)))) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ range m,
      ∑ i, hitMonomial {i} (ω j) * linearKernel q (c i) (ω j) ^ 2 := by
    calc
      _ = ∑ j ∈ range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply first_hit_signed_sum_ge_one q c hsum hprior (ω j)
        intro heq
        obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
        exact hi (congrFun heq i)
  have hbound (i : ι) :
      (∑ j ∈ range m, hitMonomial {i} (ω j) * linearKernel q (c i) (ω j) ^ 2) ≤
        (m : ℝ) * q i * (∑ Q : Finset ι, c i Q ^ 2 * variance q Q) +
          booleanSquareCost (ordinaryCoefficient q (c i)) := by
    have he := arbitrary_square_hit_boolean_error q (c i) m ω herr {i}
    have hnot (Q : Finset ι) (hiQ : i ∈ Q) : c i Q = 0 := by
      by_contra hc
      exact lt_irrefl i (hprior i Q hc i hiQ)
    rw [linearKernel_hit_average_of_not_mem q hq (c i) i hnot] at he
    linarith [(abs_le.mp he).2]
  rw [sum_comm] at hlower
  have hupper := sum_le_sum (s := univ) (fun i _ => hbound i)
  exact hmain.not_ge (hlower.trans hupper)

end Ordered
#print axioms survivor_of_first_hit_boolean_cost
end Erdos970.FiniteSelberg

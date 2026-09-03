import FormalConjecturesUtil
import Submission.Model126
import Submission.ArithmeticCells126
import Submission.ArithmeticValuation126

/-!
# One prime's finite integer opposition family

The level labels contain a valuation tag and a globally oriented unit residue.
At two the first modulus is four.  The construction retains only bichromatic
classes, and `ArithmeticCells126.build` combines all repeated supports.
-/

open scoped BigOperators

namespace E126.ArithmeticPrime126

open ArithmeticValuation126

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximum off-diagonal sum valuation, with maximum of the empty set zero. -/
def maxDepth (a : ι → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ : Finset ι).offDiag.sup (fun ij => (a ij.1 + a ij.2).factorization p)

lemma sumExp_le_maxDepth (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) :
    sumExp p (a i) (a j) ≤ maxDepth a p := by
  by_cases hij : i = j
  · subst j
    rw [same_color_sumExp_zero hp (ha i) (ha i) rfl]
    exact Nat.zero_le _
  · have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag :=
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
    exact (Nat.sub_le _ _).trans (Finset.le_sup (f := fun ij : ι × ι =>
      (a ij.1 + a ij.2).factorization p) hmem)

lemma log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_le)

/-- The explicit prime family. It is defined even without positivity assumptions
on the inputs; those assumptions enter its arithmetic kernel theorem. -/
def family (a : ι → ℕ) (p : ℕ) (hp : p.Prime) : OppositionFamily ι :=
  ArithmeticCells126.build (maxDepth a p)
    (fun i => Signature126.primeColor p (a i))
    (fun n i => label p n (a i))
    (fun _ _ h _ _ he => label_refines p h he)
    (Real.log (p : ℝ)) (log_prime_nonneg hp)

@[simp] lemma family_sign (a : ι → ℕ) (p : ℕ) (hp : p.Prime) (i : ι) :
    (family a p hp).sign i = Signature126.primeColor p (a i) := rfl

/-- Exact opposite-side kernel, with the adjusted exponent at two. -/
theorem opposition_eq (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) :
    (family a p hp).opposition i j =
      (sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) := by
  classical
  by_cases hc : Signature126.primeColor p (a i) = Signature126.primeColor p (a j)
  · rw [same_color_sumExp_zero hp (ha i) (ha j) hc]
    simp [OppositionFamily.opposition, hc]
  · unfold family
    rw [ArithmeticCells126.opposition_eq_sum _ _ _ _ _ _ i j hc]
    simp_rw [label_eq_opposite hp (ha i) (ha j) hc]
    exact ArithmeticCells126.sum_initial _ _ _ (sumExp_le_maxDepth a ha p hp i j)

/-- Every retained same-side level is accounted for by the adjusted difference
valuation. This upper bound suffices without an explicit common-neighbor maximum. -/
theorem agreement_le (a : ι → ℕ) (p : ℕ) (hp : p.Prime) (i j : ι)
    (hij : a i ≠ a j) :
    (family a p hp).agreement i j ≤
      (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) := by
  classical
  have hw := log_prime_nonneg hp
  by_cases hc : Signature126.primeColor p (a i) = Signature126.primeColor p (a j)
  · calc
      (family a p hp).agreement i j ≤
          ∑ n ∈ Finset.range (maxDepth a p),
            if label p n (a i) = label p n (a j) then Real.log (p : ℝ) else 0 :=
        ArithmeticCells126.agreement_le_sum _ _ _ _ _ _ i j
      _ ≤ ∑ n ∈ Finset.range (maxDepth a p),
          if n < diffExp p (a i) (a j) then Real.log (p : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases he : label p n (a i) = label p n (a j)
        · rw [if_pos he, if_pos (label_eq_same_bound hp hij hc n he)]
        · rw [if_neg he]
          split_ifs
          · exact hw
          · exact le_rfl
      _ ≤ (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) :=
        ArithmeticCells126.sum_initial_le _ _ _ hw
  · have hz : (family a p hp).agreement i j = 0 := by
      simp [OppositionFamily.agreement, hc]
    rw [hz]
    exact mul_nonneg (Nat.cast_nonneg _) hw

/-- After subtracting opposition, the common normalization and the two-adic
baseline cancel. This form is convenient for summing over the prime support. -/
theorem signed_le (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) (hij : a i ≠ a j) :
    (family a p hp).signed i j ≤
      ((diff (a i) (a j)).factorization p : ℝ) * Real.log (p : ℝ) -
      ((a i + a j).factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [OppositionFamily.signed_eq, opposition_eq a ha p hp i j]
  calc
    _ ≤ (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) -
        (sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) :=
      sub_le_sub_right (agreement_le a p hp i j hij) _
    _ = _ := by
      rw [diffExp, sumExp, Nat.cast_sub (base_le_diff hp (ha i) (ha j) hij),
        Nat.cast_sub (base_le_sum hp (ha i) (ha j))]
      ring

end

end E126.ArithmeticPrime126

import FormalConjecturesUtil
import Submission.Model126
import Submission.LogKernel126
import Submission.ArithmeticPrime126

/-!
# The positive-integer arithmetic model for Erdős problem 126

For distinct positive integers indexed by any finite type, and any prime set
containing the support of all off-diagonal sums, this module constructs one
finite laminar opposition family per prime. Its total opposition is exactly
`E126.arithmetic_log_kernel`, including the diagonal, and its total signed
kernel is strictly negative off the diagonal.

The construction uses globally oriented unit residues. Bichromatic cells are
retained and repeated supports have their weights added. At two, the first
modulus is four and all exponents use the adjusted baseline from the outset.
No declaration from `Submission.Spec` is imported.
-/

open scoped BigOperators

namespace E126

namespace ArithmeticModel126

open ArithmeticValuation126

lemma log_eq_sum_factorization (n : ℕ) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  exact Finsupp.sum_of_support_subset _ hS _ (by intros; simp)

/-- A partial prime-factorization sum is bounded by the full logarithm. -/
lemma sum_factorization_le_log (n : ℕ) (S : Finset ℕ) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  calc
    _ ≤ ∑ p ∈ S ∪ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro p hp hnot
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (log_eq_sum_factorization n _ Finset.subset_union_right).symm

lemma two_mem_of_equal_valuations {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hS : (a + b).primeFactors ⊆ S)
    (he : a.factorization 2 = b.factorization 2) : 2 ∈ S := by
  apply hS
  apply Nat.mem_primeFactors.mpr
  have hs : a + b ≠ 0 := by omega
  refine ⟨Nat.prime_two, ?_, hs⟩
  apply (Nat.prime_two.dvd_iff_one_le_factorization hs).mpr
  have h := base_le_sum Nat.prime_two ha hb
  rw [base_of_eq he] at h
  simp only [epsilon, if_true] at h
  omega

/-- The common baseline sums to log-gcd plus the required equality-of-2-valuations term. -/
lemma sum_base_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hS : (a + b).primeFactors ⊆ S) :
    (∑ p ∈ S, (base p a b : ℝ) * Real.log (p : ℝ)) =
      Real.log (Nat.gcd a b : ℝ) +
        if a.factorization 2 = b.factorization 2 then Real.log 2 else 0 := by
  have hgS : (Nat.gcd a b).primeFactors ⊆ S :=
    (Nat.primeFactors_mono
      (Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)) (by omega)).trans hS
  have heach : ∀ p, (base p a b : ℝ) * Real.log (p : ℝ) =
      ((Nat.gcd a b).factorization p : ℝ) * Real.log (p : ℝ) +
        if p = 2 ∧ a.factorization 2 = b.factorization 2 then Real.log (p : ℝ) else 0 := by
    intro p
    rw [base_eq_gcd_add ha hb, Nat.cast_add, add_mul]
    split_ifs <;> simp
  simp_rw [heach, Finset.sum_add_distrib]
  rw [← log_eq_sum_factorization _ S hgS]
  congr 1
  by_cases he : a.factorization 2 = b.factorization 2
  · have htwo := two_mem_of_equal_valuations ha hb S hS he
    simp [he, htwo]
  · simp [he]

/-- Exact logarithmic sum of all adjusted prime exponents. -/
lemma sum_sumExp_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (hS : (a + b).primeFactors ⊆ S) :
    (∑ p ∈ S, (sumExp p a b : ℝ) * Real.log (p : ℝ)) = arithmetic_log_kernel a b := by
  calc
    _ = (∑ p ∈ S, ((a + b).factorization p : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ S, (base p a b : ℝ) * Real.log (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [sumExp, Nat.cast_sub (base_le_sum (hprime p hp) ha hb), sub_mul]
    _ = arithmetic_log_kernel a b := by
      rw [← log_eq_sum_factorization _ S hS, sum_base_log ha hb S hS]
      unfold arithmetic_log_kernel
      ring

end ArithmeticModel126

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite integer model, indexed by the prescribed prime support.
Its definition needs no injectivity or positivity hypotheses. -/
def arithmeticModel (a : ι → ℕ) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    S → OppositionFamily ι :=
  fun p => ArithmeticPrime126.family a p.1 (hprime p.1 p.2)

/-- Full matrix identity, including the diagonal and empty/singleton index types. -/
theorem arithmeticModel_opposition (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) (i j : ι) :
    totalOpposition (arithmeticModel a S hprime) i j = arithmetic_log_kernel (a i) (a j) := by
  classical
  by_cases hij : i = j
  · subst j
    simp [totalOpposition, arithmetic_log_kernel_diag (ha i)]
  · unfold totalOpposition arithmeticModel
    simp_rw [ArithmeticPrime126.opposition_eq a ha]
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun p => (ArithmeticValuation126.sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ))]
    exact ArithmeticModel126.sum_sumExp_log (ha i) (ha j) S hprime (hsupport i j hij)

/-- A stronger quantitative form of off-diagonal negativity. Both the gcd
normalization and the extra baseline at two cancel in the signed difference. -/
theorem arithmeticModel_signed_le (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (i j : ι) (hij : i ≠ j) :
    totalSigned (arithmeticModel a S hprime) i j ≤
      Real.log (ArithmeticValuation126.diff (a i) (a j) : ℝ) -
        Real.log ((a i + a j : ℕ) : ℝ) := by
  classical
  have hab : a i ≠ a j := fun h => hij (hinj h)
  calc
    _ ≤ ∑ p : S,
        (((ArithmeticValuation126.diff (a i) (a j)).factorization p.1 : ℝ) * Real.log (p.1 : ℝ) -
        ((a i + a j).factorization p.1 : ℝ) * Real.log (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact ArithmeticPrime126.signed_le a ha p.1 (hprime p.1 p.2) i j hab
    _ = (∑ p ∈ S,
        ((ArithmeticValuation126.diff (a i) (a j)).factorization p : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ S, ((a i + a j).factorization p : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.sum_sub_distrib]
      congr 1 <;> symm <;> exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    _ ≤ _ := by
      rw [← ArithmeticModel126.log_eq_sum_factorization _ S (hsupport i j hij)]
      exact sub_le_sub_right (ArithmeticModel126.sum_factorization_le_log _ S) _

/-- Strict signed-kernel negativity for distinct positive integer inputs. -/
theorem arithmeticModel_signed_neg (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (i j : ι) (hij : i ≠ j) :
    totalSigned (arithmeticModel a S hprime) i j < 0 := by
  have hab : a i ≠ a j := fun h => hij (hinj h)
  have hlog := Real.log_lt_log
    (Nat.cast_pos.mpr (ArithmeticValuation126.diff_pos hab) :
      (0 : ℝ) < ArithmeticValuation126.diff (a i) (a j))
    (Nat.cast_lt.mpr (ArithmeticValuation126.diff_lt_sum (ha i) (ha j)))
  exact lt_of_le_of_lt (arithmeticModel_signed_le a ha hinj S hprime hsupport i j hij)
    (sub_neg.mpr hlog)

/-- The model inherits the already-proved weak conditional negative definiteness. -/
theorem arithmeticModel_cnd (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    CND (totalOpposition (arithmeticModel a S hprime)) := by
  intro q hq
  unfold quad
  simp_rw [arithmeticModel_opposition a ha S hprime hsupport]
  exact arithmetic_log_kernel_cnd a ha q hq

/-- Main arithmetic interface for the abstract finite laminar-capacity argument. -/
theorem exists_arithmetic_model (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    ∃ W : S → OppositionFamily ι,
      (∀ i j, totalOpposition W i j = arithmetic_log_kernel (a i) (a j)) ∧
      (∀ i j, i ≠ j → totalSigned W i j < 0) := by
  exact ⟨arithmeticModel a S hprime,
    arithmeticModel_opposition a ha S hprime hsupport,
    arithmeticModel_signed_neg a ha hinj S hprime hsupport⟩

end

end E126

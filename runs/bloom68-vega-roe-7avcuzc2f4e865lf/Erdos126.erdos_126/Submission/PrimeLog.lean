import FormalConjecturesUtil

/-!
# Truncated prime-power counts and logarithmic factorization sums

These lemmas are independent of the other submission modules.
-/

namespace Erdos126PrimeLog

open scoped BigOperators

noncomputable section

/-- The number of positive powers of `p` with exponent at most `K` that divide `m`. -/
def countPowers (p K m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, if p ^ (k + 1) ∣ m then (1 : ℝ) else 0

theorem countPowers_nonneg (p K m : ℕ) : 0 ≤ countPowers p K m := by
  unfold countPowers
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> norm_num

/-- Truncating the count of prime powers truncates the factorization exponent. -/
theorem countPowers_eq_min (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    countPowers p K m = ((min K (m.factorization p) : ℕ) : ℝ) := by
  have hfilter : (Finset.range K).filter (fun k => k < m.factorization p) =
      Finset.range (min K (m.factorization p)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  simp only [countPowers, hp.pow_dvd_iff_le_factorization hm, Nat.add_one_le_iff,
    Finset.sum_boole]
  rw [hfilter, Finset.card_range]

theorem countPowers_le_factorization (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    countPowers p K m ≤ (m.factorization p : ℝ) := by
  rw [countPowers_eq_min p K m hp hm]
  exact_mod_cast (min_le_right K (m.factorization p))

theorem countPowers_eq_factorization (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (hK : m.factorization p ≤ K) :
    countPowers p K m = (m.factorization p : ℝ) := by
  rw [countPowers_eq_min p K m hp hm, min_eq_right hK]

/-- A finite set containing all prime factors gives the full logarithmic sum.
No primality assumption on the other elements of `S` is needed. -/
theorem sum_log_factorization_eq (S : Finset ℕ) (m : ℕ)
    (hsupp : m.primeFactors ⊆ S) :
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) = Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) =
        ∑ p ∈ m.primeFactors, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      symm
      apply Finset.sum_subset hsupp
      intro p _ hp
      have hz : m.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
      simp only [hz, Nat.cast_zero, mul_zero]
    _ = Real.log (m : ℝ) := by
      simpa only [Finsupp.sum, Nat.support_factorization, mul_comm] using
        (Real.log_nat_eq_sum_factorization m).symm

/-- Any finite subsum of the logarithmic factorization sum is at most `log m`. -/
theorem sum_log_factorization_le (S : Finset ℕ) (m : ℕ) :
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) ≤ Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) ≤
        ∑ p ∈ S ∪ m.primeFactors, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro p _ _
      exact mul_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
    _ = Real.log (m : ℝ) :=
      sum_log_factorization_eq (S ∪ m.primeFactors) m Finset.subset_union_right

theorem sum_log_count_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (K m : ℕ) (hm : m ≠ 0) :
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) ≤ Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) ≤
        ∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (countPowers_le_factorization p K m (hS p hp) hm) (Real.log_natCast_nonneg p)
    _ ≤ Real.log (m : ℝ) := sum_log_factorization_le S m

theorem sum_log_count_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (K m : ℕ) (hm : m ≠ 0) (hsupp : m.primeFactors ⊆ S)
    (hK : ∀ p ∈ S, m.factorization p ≤ K) :
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) = Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) =
        ∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [countPowers_eq_factorization p K m (hS p hp) hm (hK p hp)]
    _ = Real.log (m : ℝ) := sum_log_factorization_eq S m hsupp

/-- A finite family has a uniform factorization cutoff for its pairwise sums on `S`. -/
theorem exists_factorization_cutoff {V : Type*} [Fintype V] (a : V → ℕ) (S : Finset ℕ) :
    ∃ K : ℕ, ∀ p ∈ S, ∀ i j : V, (a i + a j).factorization p ≤ K := by
  classical
  refine ⟨S.sup (fun p => Finset.univ.sup (fun i : V =>
    Finset.univ.sup (fun j : V => (a i + a j).factorization p))), ?_⟩
  intro p hp i j
  exact Finset.le_sup_of_le hp <|
    Finset.le_sup_of_le (Finset.mem_univ i) <|
      Finset.le_sup (f := fun j : V => (a i + a j).factorization p) (Finset.mem_univ j)

end

end Erdos126PrimeLog

import Submission.OneSidedSieve

/-! Exact floor/ceiling versions of the finite sieve certificate. -/
namespace Erdos970.BlockSieve.SievePolynomial
open Erdos970.BrunCriterion

/-- The integral ceiling quotient; its intended use has positive denominator. -/
def ceilQuotient (m d : ℕ) : ℕ := m / d + if m % d = 0 then 0 else 1

theorem residue_count_bounds (m d r : ℕ) (hd : 0 < d) :
    m / d ≤ ((Finset.range m).filter (fun i => i ≡ r [MOD d])).card ∧
    ((Finset.range m).filter (fun i => i ≡ r [MOD d])).card ≤ ceilQuotient m d := by
  classical
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hd r]
  dsimp only [ceilQuotient]
  by_cases hm : m % d = 0
  · simp [hm]
  · simp only [if_neg hm]
    split_ifs <;> omega

theorem intersection_count_bounds (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    m / (∏ p ∈ Q, p) ≤ ((Finset.range m).filter
      (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card ∧
    ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card ≤
      ceilQuotient m (∏ p ∈ Q, p) := by
  classical
  obtain ⟨b, hb⟩ := intersection_residue Q hQ r
  simp_rw [hb]
  exact residue_count_bounds m _ b (Finset.prod_pos (fun p hp => (hQ p hp).pos))

/-- Each term is rounded in the direction dictated by its coefficient's sign. -/
noncomputable def roundedMain (S : SievePolynomial) (m : ℕ) : ℝ :=
  ∑ a : S.Term, if 0 ≤ S.coefficient a then
    S.coefficient a * (m / (∏ p ∈ S.primes a, p) : ℕ)
  else S.coefficient a * (ceilQuotient m (∏ p ∈ S.primes a, p) : ℕ)

theorem roundedMain_le_interval (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    S.roundedMain m ≤ ∑ i ∈ Finset.range m, S.value r i := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter
    (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) =
      ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  rw [hcount]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨hlo, hhi⟩ := intersection_count_bounds (S.primes a) (hS a) r m
  change m / (∏ p ∈ S.primes a, p) ≤ C a at hlo
  change C a ≤ ceilQuotient m (∏ p ∈ S.primes a, p) at hhi
  by_cases hc : 0 ≤ S.coefficient a
  · rw [if_pos hc]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) hc
  · rw [if_neg hc]
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hhi) (le_of_not_ge hc)

/-- A covered interval cannot have a positive rounded lower main term. -/
theorem roundedMain_nonpos_of_nonpos (S : SievePolynomial)
    (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, S.value r i ≤ 0) : S.roundedMain m ≤ 0 :=
  (roundedMain_le_interval S hS r m).trans
    (Finset.sum_nonpos (fun i hi => hpoint i (Finset.mem_range.mp hi)))

/-- A positive rounded certificate proves existence of a survivor, without asymptotic errors. -/
theorem survivor_of_positive_roundedMain (P : Finset ℕ) (S : SievePolynomial)
    (hP : ∀ p ∈ P, p.Prime) (hS : S.SupportedOn P) (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ i < m, (∃ p ∈ P, i ≡ r p [MOD p]) → S.value r i ≤ 0)
    (hmain : 0 < S.roundedMain m) :
    ∃ i < m, ∀ p ∈ P, ¬i ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  have hSp : ∀ a, ∀ p ∈ S.primes a, p.Prime := fun a p hp => hP p (hS a hp)
  exact hmain.not_ge (roundedMain_nonpos_of_nonpos S hSp r m
    (fun i hi => hpoint i hi (hbad i hi)))

/-- Empty prime products, and every other divisor of the interval length, incur no error. -/
theorem roundedMain_eq_main_of_dvd (S : SievePolynomial) (m : ℕ)
    (hd : ∀ a, (∏ p ∈ S.primes a, p) ∣ m)
    (hp : ∀ a, 0 < ∏ p ∈ S.primes a, p) :
    S.roundedMain m = (m : ℝ) * S.mean := by
  classical
  rw [roundedMain, mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hmod : m % (∏ p ∈ S.primes a, p) = 0 := Nat.mod_eq_zero_of_dvd (hd a)
  have hquot : ((m / (∏ p ∈ S.primes a, p) : ℕ) : ℝ) =
      (m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.cast_div (hd a) (by exact_mod_cast (hp a).ne')]
  simp only [ceilQuotient, hmod, if_true, Nat.add_zero, hquot]
  split_ifs <;> ring

#print axioms survivor_of_positive_roundedMain
#print axioms roundedMain_eq_main_of_dvd
end Erdos970.BlockSieve.SievePolynomial

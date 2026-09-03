import FormalConjecturesUtil

/-! An elementary explicit power bound for the divisor function, followed
by a uniform subpower estimate on polynomially bounded arguments. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma succ_le_two_pow (e : ℕ) : e+1 ≤ 2^e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [pow_succ]
    nlinarith

lemma exponent_power_bound (e k : ℕ) :
    (e+1)^k ≤ (k.factorial*2^k)*2^e := by
  calc
    _ ≤ (e+1).ascFactorial k := Nat.pow_succ_le_ascFactorial _ _
    _ = k.factorial*(e+k).choose k := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ k.factorial*2^(e+k) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

/-- Only primes below 2^k pay a constant in this bound. -/
lemma prime_exponent_power_bound (p e k : ℕ) (hp : p.Prime) :
    (e+1)^k ≤ (if p<2^k then k.factorial*2^k else 1)*p^e := by
  by_cases h : p<2^k
  · rw [if_pos h]
    exact (exponent_power_bound e k).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le e))
  · rw [if_neg h,one_mul]
    calc
      _ ≤ (2^e)^k := Nat.pow_le_pow_left (succ_le_two_pow e) k
      _ = (2^k)^e := pow_right_comm 2 e k
      _ ≤ _ := Nat.pow_le_pow_left (le_of_not_gt h) e

def divisorPowerConstant (k : ℕ) : ℕ := (k.factorial*2^k)^(2^k)

/-- A completely explicit form of the classical divisor subpower bound. -/
theorem divisor_card_power_bound (n k : ℕ) (hn : n ≠ 0) :
    n.divisors.card^k ≤ divisorPowerConstant k*n := by
  let C := k.factorial*2^k
  have hC : 0 < C := by dsimp [C]; positivity
  have hp : (∏ p ∈ n.primeFactors, p^(n.factorization p))=n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_pow_eq_self hn]
  have hc : (n.primeFactors.filter (fun p => p<2^k)).card ≤ 2^k := by
    calc
      _ ≤ (range (2^k)).card := card_le_card (by
        intro p hp
        exact mem_range.mpr (mem_filter.mp hp).2)
      _ = _ := card_range _
  rw [Nat.card_divisors hn, ← prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<2^k then C else 1)*p^(n.factorization p) :=
      prod_le_prod' fun p hp => prime_exponent_power_bound p (n.factorization p) k
        (Nat.prime_of_mem_primeFactors hp)
    _ = C^((n.primeFactors.filter (fun p => p<2^k)).card)*n := by
      rw [prod_mul_distrib,hp,prod_ite]
      simp only [prod_const,one_pow,mul_one]
    _ ≤ C^(2^k)*n := Nat.mul_le_mul_right n (Nat.pow_le_pow_right hC hc)
    _ = _ := rfl

/-- Uniformity includes every argument n<=N^d, not just a fixed sequence of
arguments. The exponent epsilon can be arbitrarily small and positive. -/
theorem divisor_card_uniform_subpower (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N^d →
      (n.divisors.card : ℝ) ≤ (N : ℝ)^ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((d : ℝ)/ε)
  have hk0 : 0 < k := by
    have hd : (0 : ℝ) ≤ (d : ℝ)/ε := by positivity
    have : (0 : ℝ) < k := hd.trans_lt hk
    exact_mod_cast this
  have hgap : 0 < ε*k-d := by
    have h := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(ε*k-d)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop (divisorPowerConstant k : ℝ),
    eventually_ge_atTop (1 : ℕ)] with N hC hN
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simp only [Nat.divisors_zero,card_empty,Nat.cast_zero]
    positivity
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hb : (n.divisors.card : ℝ)^k ≤ (divisorPowerConstant k : ℝ)*n := by
    exact_mod_cast divisor_card_power_bound n k hn0
  have hnn : (n : ℝ) ≤ (N : ℝ)^d := by exact_mod_cast hn
  have he : ((N : ℝ)^ε)^k=(N : ℝ)^(ε*k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  apply le_of_pow_le_pow_left₀ hk0.ne' (Real.rpow_nonneg hNr.le ε)
  rw [he]
  calc
    _ ≤ (divisorPowerConstant k : ℝ)*n := hb
    _ ≤ (N : ℝ)^(ε*k-d)*(N : ℝ)^d :=
      mul_le_mul hC hnn (Nat.cast_nonneg n) (Real.rpow_nonneg hNr.le _)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hNr]
      congr 1
      ring

#print axioms divisor_card_power_bound
#print axioms divisor_card_uniform_subpower
end Erdos371

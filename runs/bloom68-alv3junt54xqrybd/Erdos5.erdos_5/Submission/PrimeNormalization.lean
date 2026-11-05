import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Elementary logarithmic normalization of the nth prime

The prime-counting lower bound below is obtained from central binomial
coefficients. No prime number theorem or prime-gap result is used.
-/

open Filter
open scoped Topology

namespace Erdos5PrimeNormalization

/-- A convenient elementary exponential lower bound for central binomial coefficients. -/
theorem two_pow_le_centralBinom (n : ℕ) : 2 ^ n ≤ Nat.centralBinom n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : 2 * Nat.centralBinom n ≤ Nat.centralBinom (n + 1) := by
      refine Nat.le_of_mul_le_mul_left (c := n + 1) ?_ (by omega)
      rw [Nat.succ_mul_centralBinom_succ]
      nlinarith
    calc
      2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
      _ ≤ 2 * Nat.centralBinom n := Nat.mul_le_mul_left 2 ih
      _ ≤ Nat.centralBinom (n + 1) := hstep

/-- Each prime-power contribution to the central binomial coefficient is at most `2*n`. -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  have hprod :
      (∏ p ∈ Finset.range (2 * n + 1) with Nat.Prime p,
        p ^ (Nat.centralBinom n).factorization p) = Nat.centralBinom n := by
    rw [Finset.prod_filter_of_ne, Nat.prod_pow_factorization_centralBinom]
    intro p _ hp
    contrapose! hp
    simp [Nat.factorization_eq_zero_of_not_prime (Nat.centralBinom n) hp]
  calc
    Nat.centralBinom n =
        ∏ p ∈ Finset.range (2 * n + 1) with Nat.Prime p,
          p ^ (Nat.centralBinom n).factorization p := hprod.symm
    _ ≤ ∏ p ∈ Finset.range (2 * n + 1) with Nat.Prime p, 2 * n := by
      exact Finset.prod_le_prod' fun p _ =>
        Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    _ = (2 * n) ^ Nat.primeCounting (2 * n) := by
      rw [Finset.prod_const, Nat.primeCounting, Nat.primeCounting',
        Nat.count_eq_card_filter_range]

/-- Taking logarithms of the elementary bounds on the central binomial coefficient. -/
theorem mul_log_two_le_primeCounting_mul_log (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 2 ≤
      (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
  have hnat := (two_pow_le_centralBinom n).trans (centralBinom_le_pow_primeCounting n hn)
  have hreal : (2 : ℝ) ^ n ≤ (2 * (n : ℝ)) ^ Nat.primeCounting (2 * n) := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ n) hreal
  simpa only [Real.log_pow] using hlog

/-- An explicit elementary Chebyshev lower bound, valid at every natural `x ≥ 2`. -/
theorem weak_chebyshev_lower (x : ℕ) (hx : 2 ≤ x) :
    (Real.log 2 / 3) * (x : ℝ) ≤
      (Nat.primeCounting x : ℝ) * Real.log (x : ℝ) := by
  have hm : 0 < x / 2 := by omega
  have hm3 : x ≤ 3 * (x / 2) := by omega
  have h2m : 2 * (x / 2) ≤ x := Nat.mul_div_le x 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Real.log 2 / 3) * (x : ℝ) = ((x : ℝ) / 3) * Real.log 2 := by ring
    _ ≤ (x / 2 : ℕ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hlog2.le
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
      exact_mod_cast (by simpa only [Nat.mul_comm] using hm3 : x ≤ (x / 2) * 3)
    _ ≤ (Nat.primeCounting (2 * (x / 2)) : ℝ) * Real.log (2 * (x / 2 : ℕ)) :=
      mul_log_two_le_primeCounting_mul_log (x / 2) hm
    _ ≤ (Nat.primeCounting x : ℝ) * Real.log (x : ℝ) := by
      apply mul_le_mul
      · exact_mod_cast Nat.monotone_primeCounting h2m
      · apply Real.log_le_log
        · positivity
        · exact_mod_cast h2m
      · apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ 2 * (x / 2) by omega)
      · positivity

/-- The customary divided form of the same lower bound. -/
theorem weak_chebyshev_lower_div (x : ℕ) (hx : 2 ≤ x) :
    (Real.log 2 / 3) * (x : ℝ) / Real.log (x : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))).2
  exact weak_chebyshev_lower x hx

/-- The inclusive prime count at the zero-indexed nth prime is `n+1`. -/
@[simp] theorem primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime n

/-- The nth primes tend to infinity. -/
theorem tendsto_nth_prime_atTop :
    Tendsto (Nat.nth Nat.Prime) atTop atTop :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).tendsto_atTop

/-- The same limit after embedding the nth primes into the reals. -/
theorem tendsto_nth_prime_real_atTop :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop

/-- The logarithms of the nth primes also tend to infinity. -/
theorem tendsto_log_nth_prime_atTop :
    Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_nth_prime_real_atTop

/-- The logarithmic consequence of the Chebyshev lower bound at the nth prime. -/
theorem log_nth_prime_le_log_index_add_log_log (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Nat.nth Nat.Prime n : ℝ) ≤
      Real.log (n : ℝ) + Real.log (Real.log (Nat.nth Nat.Prime n : ℝ)) +
        (Real.log 2 - Real.log (Real.log 2 / 3)) := by
  have hc : 0 < Real.log 2 / 3 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hp : 0 < (Nat.nth Nat.Prime n : ℝ) := by
    exact_mod_cast (Nat.prime_nth_prime n).pos
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hlp : 0 < Real.log (Nat.nth Nat.Prime n : ℝ) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime n).one_lt)
  have hcount := weak_chebyshev_lower (Nat.nth Nat.Prime n)
    (Nat.prime_nth_prime n).two_le
  rw [primeCounting_nth_prime] at hcount
  have htwon : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hbound :
      (Real.log 2 / 3) * (Nat.nth Nat.Prime n : ℝ) ≤
        (2 * (n : ℝ)) * Real.log (Nat.nth Nat.Prime n : ℝ) :=
    hcount.trans (mul_le_mul_of_nonneg_right htwon hlp.le)
  have hlogs := Real.log_le_log (mul_pos hc hp) hbound
  rw [Real.log_mul hc.ne' hp.ne',
    Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2) hnpos).ne' hlp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hlogs
  linarith

/-- Elementary logarithmic normalization in reciprocal form. -/
theorem tendsto_log_index_div_log_nth_prime :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hsmall :
      Tendsto (fun n : ℕ =>
        Real.log (Real.log (Nat.nth Nat.Prime n : ℝ)) /
          Real.log (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_nth_prime_atTop
  have hconst :
      Tendsto (fun n : ℕ =>
        (Real.log 2 - Real.log (Real.log 2 / 3)) /
          Real.log (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_log_nth_prime_atTop
  have herr :
      Tendsto (fun n : ℕ =>
        (Real.log (Real.log (Nat.nth Nat.Prime n : ℝ)) +
          (Real.log 2 - Real.log (Real.log 2 / 3))) /
            Real.log (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_div, add_zero] using hsmall.add hconst
  have hlower :
      Tendsto (fun n : ℕ =>
        1 - (Real.log (Real.log (Nat.nth Nat.Prime n : ℝ)) +
          (Real.log 2 - Real.log (Real.log 2 / 3))) /
            Real.log (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hlp : 0 < Real.log (Nat.nth Nat.Prime n : ℝ) :=
      Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime n).one_lt)
    apply (le_div_iff₀ hlp).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hlp.ne']
    linarith [log_nth_prime_le_log_index_add_log_log n hn]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply (div_le_one (Real.log_pos
      (by exact_mod_cast (Nat.prime_nth_prime n).one_lt))).2
    apply Real.log_le_log
    · exact_mod_cast (show 0 < n by omega)
    · exact_mod_cast (show n ≤ Nat.nth Nat.Prime n by
        have := Nat.add_two_le_nth_prime n
        omega)

/-- The requested unconditional normalization of the logarithm of the nth prime. -/
theorem tendsto_log_nth_prime_div_log_index :
    Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  simpa only [inv_div, inv_one] using
    tendsto_log_index_div_log_nth_prime.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

end Erdos5PrimeNormalization

#print axioms Erdos5PrimeNormalization.two_pow_le_centralBinom
#print axioms Erdos5PrimeNormalization.centralBinom_le_pow_primeCounting
#print axioms Erdos5PrimeNormalization.mul_log_two_le_primeCounting_mul_log
#print axioms Erdos5PrimeNormalization.weak_chebyshev_lower
#print axioms Erdos5PrimeNormalization.weak_chebyshev_lower_div
#print axioms Erdos5PrimeNormalization.primeCounting_nth_prime
#print axioms Erdos5PrimeNormalization.tendsto_nth_prime_atTop
#print axioms Erdos5PrimeNormalization.tendsto_nth_prime_real_atTop
#print axioms Erdos5PrimeNormalization.tendsto_log_nth_prime_atTop
#print axioms Erdos5PrimeNormalization.log_nth_prime_le_log_index_add_log_log
#print axioms Erdos5PrimeNormalization.tendsto_log_index_div_log_nth_prime
#print axioms Erdos5PrimeNormalization.tendsto_log_nth_prime_div_log_index

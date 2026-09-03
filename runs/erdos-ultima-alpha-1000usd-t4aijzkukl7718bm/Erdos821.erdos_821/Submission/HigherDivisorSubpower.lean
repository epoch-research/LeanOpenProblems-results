import Submission.ShiftedDivisorLowerTransfer
import Submission.Valuation

/-!
# Subpower bounds for fixed-order divisor weights

These remove the nonprime prime-power error in the finite lower transfer.
The weighted progression discrepancy remains unestimated.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

lemma tau_succ_le_divisors_pow (k n : ℕ) : tau (k+1) n ≤ n.divisors.card^k := by
  induction k generalizing n with
  | zero =>
    simp only [tau, zero_add, pow_one, pow_zero, zeta_apply]
    split_ifs <;> omega
  | succ k ih =>
    rw [tau_succ]
    calc
      _ ≤ ∑ d ∈ n.divisors, n.divisors.card^k := by
        apply Finset.sum_le_sum
        intro d hd
        apply (ih d).trans
        apply Nat.pow_le_pow_left
        exact Finset.card_le_card (Nat.divisors_subset_of_dvd
          (Nat.mem_divisors.mp hd).2 (Nat.mem_divisors.mp hd).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.pow_succ']

lemma eventually_tau_succ_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (tau (k+1) n : ℝ) ≤ (n : ℝ)^ε := by
  let a : ℝ := ε/((k : ℝ)+1)
  have ha : 0 < a := div_pos hε (by positivity)
  have haε : a*(k : ℝ) ≤ ε := by
    have h : a*((k : ℝ)+1) = ε := by dsimp [a]; field_simp
    nlinarith
  filter_upwards [Erdos821.eventually_card_divisors_le_rpow a ha, eventually_ge_atTop 1]
    with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  calc
    _ ≤ (n.divisors.card : ℝ)^k := by exact_mod_cast tau_succ_le_divisors_pow k n
    _ ≤ ((n : ℝ)^a)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hn k
    _ = (n : ℝ)^(a*(k : ℝ)) := by rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR haε

/-- A global version, including n=0, with a constant depending on the fixed
order and positive exponent. -/
theorem tau_succ_le_const_mul_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, (tau (k+1) n : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_tau_succ_le_rpow k ε hε)
  let C : ℝ := 1 + ∑ m ∈ Finset.range N, (tau (k+1) m : ℝ)
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp only [tau_zero_input, Nat.cast_zero, Real.zero_rpow hε.ne', mul_zero, le_refl]
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hsmall : (tau (k+1) n : ℝ) ≤ C := by
      have h := Finset.single_le_sum (fun m (_ : m ∈ Finset.range N) =>
        (Nat.cast_nonneg (α := ℝ) (tau (k+1) m))) (Finset.mem_range.mpr (show n < N by omega))
      dsimp [C]
      linarith
    exact hsmall.trans (le_mul_of_one_le_right (by linarith : 0 ≤ C) (Real.one_le_rpow hn1 hε.le))

/-- Nonprime prime powers contribute only a power-saving error to any fixed
higher divisor moment. -/
theorem nonprimeMangoldtMoment_subpower_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      nonprimeMangoldtMoment (k+1) X ≤ 2*C*(X : ℝ)^(3/4 : ℝ)*Real.log X := by
  obtain ⟨C,hC,ht⟩ := tau_succ_le_const_mul_rpow k (1/4) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hbound (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      (tau (k+1) (n-1) : ℝ) ≤ C*(X : ℝ)^(1/4 : ℝ) := by
    apply (ht (n-1)).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ C)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show n-1 ≤ X by
      have := (Finset.mem_Icc.mp hn).2; omega)) (by norm_num)
  apply (nonprimeMangoldtMoment_le_of_bound (k+1) X hX _ hbound).trans_eq
  rw [Real.sqrt_eq_rpow, (show (3/4 : ℝ) = 1/4+1/2 by norm_num), Real.rpow_add hXR]
  ring

/-- The only unevaluated arithmetic error is now the weighted discrepancy
over all d<=Q. No prime-progression hypothesis is hidden in this result. -/
theorem shiftedPrimeMoment_lower_with_discrepancy (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q X : ℕ, 1 ≤ Q → 1 ≤ X →
      AnalyticSieve.mangoldtSum X * ((Real.log (Q+1 : ℝ))^k/(k.factorial : ℝ)) -
          divisorProgressionError k Q X - 2*C*(X : ℝ)^(3/4 : ℝ)*Real.log X ≤
        Real.log X * shiftedPrimeMoment (k+1) X := by
  obtain ⟨C,hC,hN⟩ := nonprimeMangoldtMoment_subpower_bound k
  refine ⟨C,hC,?_⟩
  intro Q X hQ hX
  have h1 := mangoldtMoment_factorial_lower_with_error k Q X hQ
  have h2 := mangoldtMoment_le_primeMoment_add_nonprime (k+1) X
  have h3 := hN X hX
  linarith

end Erdos821.HigherDivisors

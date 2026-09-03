import Submission.HigherDivisorSubpower

/-!
# A central-binomial lower bound for the Mangoldt sum

Prime-power multiplicities in a binomial coefficient inject into the prime
powers up to its upper argument. This yields the elementary lower constant
log 2, and in particular a dyadic lower bound strictly above X/2.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators

namespace Erdos821.AnalyticSieve

lemma log_choose_le_mangoldt (N K : ℕ) (hN : 0 < N) :
    Real.log ((N.choose K : ℕ) : ℝ) ≤ mangoldtSum N := by
  let C := N.choose K
  let S := C.primeFactors.sigma (fun p => Finset.Icc 1 (C.factorization p))
  let f : (p : ℕ) × ℕ → ℕ := fun z => z.1^z.2
  have hS (z) (hz : z ∈ S) : z.1.Prime ∧ 1 ≤ z.2 ∧ z.2 ≤ C.factorization z.1 := by
    obtain ⟨hp, he⟩ := Finset.mem_sigma.mp hz
    exact ⟨Nat.prime_of_mem_primeFactors hp, (Finset.mem_Icc.mp he).1, (Finset.mem_Icc.mp he).2⟩
  have hinj : Set.InjOn f (S : Set ((p : ℕ) × ℕ)) := by
    intro z hz w hw he
    have h := (hS z hz).1.pow_inj' (hS w hw).1 (by have := (hS z hz).2.1; omega)
      (by have := (hS w hw).2.1; omega) he
    exact Sigma.ext h.1 (heq_of_eq h.2)
  have hsub : S.image f ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    have hz' := hS z hz
    refine Finset.mem_Icc.mpr ⟨Nat.pow_pos hz'.1.pos, ?_⟩
    exact (Nat.pow_le_pow_right hz'.1.pos hz'.2.2).trans (Nat.pow_factorization_choose_le hN)
  have he : Real.log (C : ℝ) = ∑ z ∈ S, vonMangoldt (f z) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    dsimp only [S, f]
    rw [← Finset.sum_sigma' C.primeFactors
      (fun p => Finset.Icc 1 (C.factorization p)) (fun p e => vonMangoldt (p ^ e))]
    apply Finset.sum_congr rfl
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    calc
      _ = ∑ _e ∈ Finset.Icc 1 (C.factorization p), Real.log p := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        rw [vonMangoldt_apply_pow (by have := (Finset.mem_Icc.mp he).1; omega),
          vonMangoldt_apply_prime hpr]
  change Real.log (C : ℝ) ≤ _
  rw [he, ← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnS => vonMangoldt_nonneg)

/-- The elementary log(2) lower constant, with an explicit logarithmic loss. -/
theorem central_binomial_mangoldt_lower (m : ℕ) (hm : 0 < m) :
    (2*(m : ℝ))*Real.log 2 - Real.log ((2*m : ℕ) : ℝ) ≤ mangoldtSum (2*m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hC : (0 : ℝ) < m.centralBinom := by exact_mod_cast Nat.centralBinom_pos m
  have hbin : (4 : ℝ)^m ≤ ((2*m : ℕ) : ℝ)*(m.centralBinom : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom m hm
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 4^m) hbin
  rw [Real.log_mul (by positivity) hC.ne', Real.log_pow] at hl
  have h4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hl
  have hu := log_choose_le_mangoldt (2*m) m (by omega)
  change Real.log (m.centralBinom : ℝ) ≤ _ at hu
  linarith

lemma dyadic_binomial_mangoldt_lower (r : ℕ) (hr : 1 ≤ r) :
    (((2^r : ℕ) : ℝ)-(r : ℝ))*Real.log 2 ≤ mangoldtSum (2^r) := by
  have h := central_binomial_mangoldt_lower (2^(r-1)) (by positivity)
  have he : 2*2^(r-1) = 2^r := by rw [← _root_.pow_succ']; congr 1; omega
  have heR : (2 : ℝ)*((2^(r-1) : ℕ) : ℝ) = ((2^r : ℕ) : ℝ) := by exact_mod_cast he
  rw [he, heR, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  convert h using 1
  push_cast
  ring

/-- The constant 5/8 leaves a margin above the half threshold needed by
the smallest shifted-prime divisor moment. No PNT is used. -/
theorem eventually_dyadic_mangoldt_five_eighths :
    ∀ᶠ r : ℕ in atTop, (5/8 : ℝ)*((2^r : ℕ) : ℝ) ≤ mangoldtSum (2^r) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 16 1, eventually_ge_atTop 1] with r hpoly hr
  simp only [one_mul, pow_one] at hpoly
  have hsmallNat : 16*r ≤ 2^r := by omega
  have hsmall : 16*(r : ℝ) ≤ ((2^r : ℕ) : ℝ) := by
    exact_mod_cast hsmallNat
  have hlog : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiff : 0 ≤ ((2^r : ℕ) : ℝ)-(r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hmul := mul_le_mul_of_nonneg_left hlog hdiff
  have h := dyadic_binomial_mangoldt_lower r hr
  nlinarith only [hsmall, hmul, h]

end Erdos821.AnalyticSieve

import Submission.QuantitativeTwoLinearSieve

/-! A bounded second moment for the slope factor in the finite two-form sieve. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma prime_product_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  have hc : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) :=
    fun p hp q hq hpq => (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  simpa only [id_eq, Nat.modEq_zero_iff_dvd] using modEq_finset_prod_iff S id hc n 0

/-- A nonnegative divisor-product majorant has an elementary mean bound:
the rounding errors can simply be discarded. -/
lemma prime_divisor_product_mean_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    (∑ n ∈ range N, ∏ p ∈ S, (1 + if p ∣ n+1 then C/p else 0)) ≤
      N * ∏ p ∈ S, (1 + C/(p : ℝ)^2) := by
  classical
  simp_rw [prod_one_add, prod_ite_zero]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro T hT
  have hTS := mem_powerset.mp hT
  have hdiv (n : ℕ) : (∀ p ∈ T, p ∣ n+1) ↔ (∏ p ∈ T, p) ∣ n+1 :=
    (prime_product_dvd_iff T (fun p hp => hS p (hTS hp)) (n+1)).symm
  simp_rw [hdiv]
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.card_multiples, mul_comm]
  calc
    _ ≤ (∏ p ∈ T, C/(p : ℝ)) * ((N : ℝ)/(∏ p ∈ T, p)) :=
      mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := N) (n := ∏ p ∈ T, p))
        (prod_nonneg fun _ _ => div_nonneg hC (by positivity))
    _ = _ := by
      push_cast
      calc
        _ = (N : ℝ) * ((∏ p ∈ T, C/(p : ℝ)) / ∏ p ∈ T, (p : ℝ)) := by ring
        _ = (N : ℝ) * (∏ p ∈ T, (C/(p : ℝ))/(p : ℝ)) := by rw [← prod_div_distrib]
        _ = _ := by
          congr 1
          apply prod_congr rfl
          intro p hp
          ring

lemma exp_four_div_prime_le (p : ℕ) (hp : p.Prime) :
    Real.exp (4/(p : ℝ)) ≤ 1+16/p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : (0 : ℝ) ≤ 2/p := by positivity
  have hx1 : (2 : ℝ)/p ≤ 1 := (div_le_one hp0).mpr hp2
  have h := Real.abs_exp_sub_one_le (show |(2 : ℝ)/p| ≤ 1 by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at h
  have he : Real.exp (2/(p : ℝ)) ≤ 1+4/p := by
    have h' := (le_abs_self (Real.exp (2/(p : ℝ))-1)).trans h
    have he : (4 : ℝ)/p = 2*(2/p) := by ring
    rw [he]
    linarith
  calc
    _ = (Real.exp (2/(p : ℝ)))^2 := by rw [sq, ← Real.exp_add]; congr 1; ring
    _ ≤ (1+4/(p : ℝ))^2 := pow_le_pow_left₀ (Real.exp_nonneg _) he 2
    _ ≤ _ := by
      field_simp
      nlinarith

lemma slopeSieveFactor_sq_le_product (n : ℕ) :
    (slopeSieveFactor n)^2 ≤ ∏ p ∈ n.primeFactors, (1+16/(p : ℝ)) := by
  have he : (slopeSieveFactor n)^2 = ∏ p ∈ n.primeFactors, Real.exp (4/(p : ℝ)) := by
    rw [slopeSieveFactor, sq, ← Real.exp_add, ← Real.exp_sum]
    congr 1
    unfold slopePrimeMass
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [he]
  exact prod_le_prod (fun _ _ => Real.exp_nonneg _)
    (fun p hp => exp_four_div_prime_le p (Nat.prime_of_mem_primeFactors hp))

lemma slope_product_eq_full (N n : ℕ) (hn : n < N) :
    (∏ p ∈ (n+1).primeFactors, (1+16/(p : ℝ))) =
      ∏ p ∈ (N+1).primesBelow, (1 + if p ∣ n+1 then (16 : ℝ)/p else 0) := by
  have hsub : (n+1).primeFactors ⊆ (N+1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by have := Nat.le_of_dvd (by omega : 0 < n+1) hpn; omega, hpp⟩
  calc
    _ = ∏ p ∈ (n+1).primeFactors, (1 + if p ∣ n+1 then (16 : ℝ)/p else 0) := by
      apply prod_congr rfl
      intro p hp
      rw [if_pos (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by
      apply prod_subset hsub
      intro p hp hpn
      have hnot : ¬p ∣ n+1 := fun h => hpn (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primesBelow.mp hp).2, h, by omega⟩)
      simp [hnot]

lemma sum_prime_reciprocal_sq_le_one (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, (1 : ℝ)/(p : ℝ)^2) ≤ 1 := by
  have hsub : (N+1).primesBelow ⊆ Ioc 1 (N+1) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Ioc.mpr ⟨hpp.one_lt, hpN.le⟩
  calc
    _ ≤ ∑ p ∈ Ioc 1 (N+1), (1 : ℝ)/(p : ℝ)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ p ∈ Ioc 1 (N+1), ((p : ℝ)^2)⁻¹ := by simp only [one_div]
    _ ≤ (1 : ℝ)⁻¹ - (N+1 : ℝ)⁻¹ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : 1 ≠ 0) (by omega : 1 ≤ N+1))
    _ ≤ 1 := by
      rw [inv_one]
      exact sub_le_self _ (by positivity)

/-- The singular slope factor has a bounded second moment. This allows it
to be averaged rather than estimated by its worst-case value. -/
theorem slopeSieveFactor_second_moment (N : ℕ) :
    (∑ n ∈ range N, (slopeSieveFactor (n+1))^2) ≤ N * Real.exp 16 := by
  calc
    _ ≤ ∑ n ∈ range N, ∏ p ∈ (N+1).primesBelow,
        (1 + if p ∣ n+1 then (16 : ℝ)/p else 0) := by
      apply sum_le_sum
      intro n hn
      rw [← slope_product_eq_full N n (mem_range.mp hn)]
      exact slopeSieveFactor_sq_le_product (n+1)
    _ ≤ N * ∏ p ∈ (N+1).primesBelow, (1+16/(p : ℝ)^2) :=
      prime_divisor_product_mean_le _ (fun p hp => (Nat.mem_primesBelow.mp hp).2) 16 (by norm_num) N
    _ ≤ N * Real.exp (∑ p ∈ (N+1).primesBelow, (16 : ℝ)/(p : ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.exp_sum]
      exact prod_le_prod (fun _ _ => by positivity) (fun p _ => by
        simpa only [add_comm] using Real.add_one_le_exp ((16 : ℝ)/p^2))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := sum_prime_reciprocal_sq_le_one N
      have he : (∑ p ∈ (N+1).primesBelow, (16 : ℝ)/(p : ℝ)^2) =
          16 * (∑ p ∈ (N+1).primesBelow, (1 : ℝ)/(p : ℝ)^2) := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      rw [he]
      linarith

#print axioms slopeSieveFactor_second_moment
end FiniteSieve
end Erdos371

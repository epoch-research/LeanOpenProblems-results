import Submission.ExactLargeDivisorFirstMoment
import Submission.PrimeSmoothDivisorEstimate

/-! Complementary-divisor switching with the ACTUAL signed coefficients.
No bound on the switched prime-input Möbius correlations is assumed. -/
namespace Erdos972SignedComplementaryDivisors

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972SmoothDivisorTail Erdos972PrimeSmoothDivisorEstimate

set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma block_divisor_sum_eq_cofactor_sum (c : ℕ → ℝ) {D K n : ℕ}
    (hD : 0 < D) (hn : 0 < n) (hnK : n ≤ D*K) :
    (∑ d ∈ (Ioc D (2*D)).filter (fun d => d ∣ n), c d) =
      ∑ k ∈ (Ioc 0 K).filter (fun k => k ∣ n ∧ D*k < n ∧ n ≤ 2*D*k), c (n/k) := by
  classical
  apply sum_bij (fun d _ => n/d)
  · intro d hd
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    have hd0 : 0 < d := hD.trans (mem_Ioc.mp hdI).1
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hkK : n/d ≤ K := by
      have hdD := (mem_Ioc.mp hdI).1
      nlinarith
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk0, hkK⟩, Nat.div_dvd_of_dvd hdn, ?_, ?_⟩
    · have hh := Nat.mul_lt_mul_of_pos_right (mem_Ioc.mp hdI).1 hk0
      nlinarith only [hh, hkd]
    · have hh := Nat.mul_le_mul_right (n/d) (mem_Ioc.mp hdI).2
      nlinarith only [hh, hkd]
  · intro d hd e he hde
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    obtain ⟨heI, hen⟩ := mem_filter.mp he
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn)
      (hD.trans (mem_Ioc.mp hdI).1)
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hke : e*(n/d) = n := by rw [hde]; exact Nat.mul_div_cancel' hen
    nlinarith
  · intro k hk
    obtain ⟨hkI, hkn, hklo, hkhi⟩ := mem_filter.mp hk
    have hk0 := (mem_Ioc.mp hkI).1
    have hdk : (n/k)*k = n := Nat.div_mul_cancel hkn
    have hdD : D < n/k := by nlinarith
    have hd2D : n/k ≤ 2*D := by nlinarith
    refine ⟨n/k, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hdD, hd2D⟩,
      Nat.div_dvd_of_dvd hkn⟩, ?_⟩
    exact Nat.div_div_self hkn hn.ne'
  · intro d hd
    rw [Nat.div_div_self (mem_filter.mp hd).2 hn.ne']

/-- The divisor coefficient stays inside the prime-input sum after
switching. It cannot be replaced by a scalar Möbius mean. -/
theorem signed_block_switch (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (c : ℕ → ℝ) {D K : ℕ} (hD : 0 < D)
    (hg : ∀ p ∈ S, 0 < g p ∧ g p ≤ D*K) :
    (∑ d ∈ Ioc D (2*D), c d*row S a g d) =
      ∑ k ∈ Ioc 0 K, ∑ p ∈ S,
        if k ∣ g p ∧ D*k < g p ∧ g p ≤ 2*D*k then a p*c (g p/k) else 0 := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (∑ d ∈ Ioc D (2*D), if d ∣ g p then c d else 0) =
        ∑ k ∈ Ioc 0 K,
          if k ∣ g p ∧ D*k < g p ∧ g p ≤ 2*D*k then c (g p/k) else 0 := by
    rw [← sum_filter, ← sum_filter]
    exact block_divisor_sum_eq_cofactor_sum c hD (hg p hp).1 (hg p hp).2
  calc
    _ = ∑ p ∈ S, a p*(∑ d ∈ Ioc D (2*D), if d ∣ g p then c d else 0) := by
      simp only [row, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro d hd
      by_cases hdn : d ∣ g p <;> simp [hdn, mul_comm]
    _ = ∑ p ∈ S, a p*(∑ k ∈ Ioc 0 K,
        if k ∣ g p ∧ D*k < g p ∧ g p ≤ 2*D*k then c (g p/k) else 0) := by
      exact sum_congr rfl (fun p hp => congrArg (fun x => a p*x) (hpoint p hp))
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro p hp
      split_ifs <;> simp only [mul_zero]

lemma floorMul_div_nat (α : ℝ) (p k : ℕ) :
    floorMul α p/k = floorMul (α/(k : ℝ)) p := by
  unfold floorMul
  rw [← Nat.floor_div_natCast]
  congr 1
  ring

noncomputable def cofactorMoebiusPrimeBlock (t α : ℝ) (D k N : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N,
    if k ∣ floorMul α p ∧ D*k < floorMul α p ∧ floorMul α p ≤ 2*D*k then
      primeWeight p*dampedCoefficient t (floorMul (α/(k : ℝ)) p) else 0

/-- Exact signed middle-block identity, valid for every real damping
parameter. The short variable is k, but the Möbius argument remains a
Beatty output evaluated at a genuinely prime input. -/
theorem prime_damped_block_switch {α : ℝ} (hα : 1 ≤ α) (t : ℝ) {D K N : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) :
    (∑ d ∈ Ioc D (2*D), dampedCoefficient t d*
      row (Ioc 0 N) primeWeight (floorMul α) d) =
      ∑ k ∈ Ioc 0 K, cofactorMoebiusPrimeBlock t α D k N := by
  have hh := signed_block_switch (Ioc 0 N) primeWeight (floorMul α) (dampedCoefficient t) hD
    (fun p hp => ⟨floorMul_pos hα (mem_Ioc.mp hp).1,
      ((floorMul_strictMono hα).monotone (mem_Ioc.mp hp).2).trans hNK⟩)
  simpa only [cofactorMoebiusPrimeBlock, floorMul_div_nat] using hh

#print axioms block_divisor_sum_eq_cofactor_sum
#print axioms signed_block_switch
#print axioms prime_damped_block_switch
end Erdos972SignedComplementaryDivisors

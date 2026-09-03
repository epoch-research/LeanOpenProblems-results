import FormalConjecturesUtil
import Submission.PrimeWindowMass
import Submission.CofactorDensity

/-! One-variable large-prime-factor counts. No independence or symmetry of
neighboring largest prime factors is asserted here. -/

namespace Erdos371LargePrimeFactorCount

open Finset Filter Erdos371PrimeWindowMass
open scoped Topology

abbrev P := Nat.maxPrimeFac

lemma prime_above_sqrt_eq_max {p n Y N : ℕ} (hp : p.Prime) (hYp : Y < p)
    (hn : 0 < n) (hnN : n ≤ N) (hNY : N ≤ Y^2) (hd : p ∣ n) : Nat.maxPrimeFac n=p := by
  have hpP : p ≤ Nat.maxPrimeFac n := Nat.le_maxPrimeFac hn.ne' hp hd
  by_contra h
  have hpq : p < Nat.maxPrimeFac n := by omega
  have hn1 : 1 < n := hp.one_lt.trans_le (Nat.le_of_dvd hn hd)
  have hq := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hc : p.Coprime (Nat.maxPrimeFac n) := (Nat.coprime_primes hp hq).mpr (by omega)
  have hm : p*Nat.maxPrimeFac n ≤ n := Nat.le_of_dvd hn
    (hc.mul_dvd_of_dvd_of_dvd hd Nat.maxPrimeFac_dvd)
  nlinarith

noncomputable def largeCount (Y N : ℕ) : ℕ :=
  ((range N).filter (fun n => Y < Nat.maxPrimeFac (n+1))).card

lemma prime_divisor_indicator {Y N n : ℕ} (hY : 0 < Y) (hNY : N ≤ Y^2)
    (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ window Y N, if p ∣ n then (1:ℕ) else 0) =
      if Y < Nat.maxPrimeFac n then 1 else 0 := by
  classical
  by_cases h : Y < Nat.maxPrimeFac n
  · rw [if_pos h]
    have hn1 : 1 < n := by have := Nat.maxPrimeFac_le (n := n); omega
    have hmem : Nat.maxPrimeFac n ∈ window Y N := mem_window.mpr
      ⟨Nat.prime_maxPrimeFac_of_one_lt n hn1, h, Nat.maxPrimeFac_le.trans hnN⟩
    rw [sum_eq_single (Nat.maxPrimeFac n)]
    · simp [Nat.maxPrimeFac_dvd]
    · intro p hp hne
      have hp' := mem_window.mp hp
      have hnd : ¬p ∣ n := by
        intro hd
        exact hne (prime_above_sqrt_eq_max hp'.1 hp'.2.1 hn hnN hNY hd).symm
      simp [hnd]
    · exact fun hn' => False.elim (hn' hmem)
  · rw [if_neg h]
    apply sum_eq_zero
    intro p hp
    have hp' := mem_window.mp hp
    have hnd : ¬p ∣ n := by
      intro hd
      have hh := Nat.le_maxPrimeFac hn.ne' hp'.1 hd
      omega
    simp [hnd]

/-- Above the square-root threshold, there is at most one relevant prime
factor per integer, so prime-divisor counting is exact. -/
theorem largeCount_eq_sum {Y N : ℕ} (hY : 0 < Y) (hNY : N ≤ Y^2) :
    largeCount Y N = ∑ p ∈ window Y N, N/p := by
  classical
  calc
    _ = ∑ n ∈ range N, if Y < Nat.maxPrimeFac (n+1) then (1:ℕ) else 0 := by
      simp [largeCount]
    _ = ∑ n ∈ range N, ∑ p ∈ window Y N, if p ∣ n+1 then (1:ℕ) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact (prime_divisor_indicator hY hNY (by omega)
        (by have := mem_range.mp hn; omega)).symm
    _ = ∑ p ∈ window Y N, ∑ n ∈ range N, if p ∣ n+1 then (1:ℕ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p _
      simp only [sum_boole, Nat.card_multiples, Nat.cast_id]

lemma largeCount_lower {Y N : ℕ} (hY : 0 < Y) (hNY : N ≤ Y^2) :
    (N:ℝ)*reciprocal Y N-(Nat.primeCounting N:ℝ) ≤ largeCount Y N := by
  have hsum : (N:ℝ)*reciprocal Y N ≤
      (∑ p ∈ window Y N, (N/p:ℕ):ℝ) + (window Y N).card := by
    unfold reciprocal
    rw [mul_sum]
    have he : ((window Y N).card:ℝ) = ∑ _p ∈ window Y N, (1:ℝ) := by simp
    rw [he, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hprime := (mem_window.mp hp).1
    have hlt : (N:ℝ) < (p:ℝ)*((N/p:ℕ)+1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hprime.pos
    have hh : (N:ℝ)/(p:ℝ) < (N/p:ℕ)+1 :=
      (div_lt_iff₀ (Nat.cast_pos.mpr hprime.pos)).mpr (by nlinarith [hlt])
    simpa only [mul_one_div] using hh.le
  have hcard : (window Y N).card ≤ Nat.primeCounting N := by
    have hh : window Y N ⊆ (N+1).primesBelow := by
      intro p hp
      obtain ⟨hpp,_,hpN⟩ := mem_window.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩
    simpa only [Nat.primesBelow_card_eq_primeCounting'] using card_le_card hh
  have hc : ((window Y N).card:ℝ) ≤ Nat.primeCounting N := Nat.cast_le.mpr hcard
  rw [largeCount_eq_sum hY hNY]
  push_cast
  linarith

/-- An explicit one-variable lower bound on a power subsequence. -/
theorem fourth_seventh_large_proportion : ∀ᶠ t : ℕ in atTop,
    (201/400:ℝ) ≤ (largeCount (t^4) (t^7):ℝ)/(t^7:ℕ) := by
  have hpow : Tendsto (fun t : ℕ => t^7) atTop atTop :=
    tendsto_pow_atTop (by omega : (7:ℕ)≠0)
  have hπ := Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero.comp hpow
  have hπsmall := hπ.eventually_lt_const (show (0:ℝ)<1/400 by norm_num)
  filter_upwards [eventually_window_gt_half, hπsmall, eventually_gt_atTop 1]
    with t ht hpt ht1
  simp only [Function.comp_def] at hpt
  have ht0 : 0 < t := by omega
  have hY : 0 < t^4 := pow_pos ht0 _
  have hNY : t^7 ≤ (t^4)^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right ht0 (by omega)
  have hN : (0:ℝ) < (t^7:ℕ) := Nat.cast_pos.mpr (pow_pos ht0 _)
  have hh := div_le_div_of_nonneg_right (largeCount_lower hY hNY) hN.le
  rw [sub_div, mul_div_cancel_left₀ _ hN.ne'] at hh
  linarith

end Erdos371LargePrimeFactorCount

#print axioms Erdos371LargePrimeFactorCount.largeCount_eq_sum
#print axioms Erdos371LargePrimeFactorCount.fourth_seventh_large_proportion

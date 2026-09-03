import Submission.DivisorRankin

/-!
# Higher-divisor-weighted rough shifted primes

A weighted cofactor cover and its sieve upper bound. No lower bound for
higher divisor moments on shifted primes is assumed or obtained.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

open AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def roughPrimeMoment (k X Y : ℕ) : ℝ :=
  ∑ p ∈ roughProgressionPrimes 1 Y X, (tau k (p-1) : ℝ)

/-- Removing one large prime factor loses at most the divisor order. The
removed prime need not be coprime to its cofactor. -/
theorem roughPrimeMoment_le_cofactor_sum (k X K Y : ℕ) (hX : X ≤ K*Y) :
    roughPrimeMoment (k+1) X Y ≤ (k+1 : ℝ) *
      ∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ) * primePairCofactorCount X a := by
  let P : ℕ → Finset ℕ := fun a =>
    (Finset.range (X/a+1)).filter (fun q => q.Prime ∧ (a*q+1).Prime)
  let F := (Finset.Icc 1 K).sigma P
  let v : (a : ℕ) × ℕ → ℕ := fun z => z.1*z.2+1
  have hcover : roughProgressionPrimes 1 Y X ⊆ F.image v := by
    intro p hp
    obtain ⟨hpX, _, hpns⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpX
    have hpred : 0 < p-1 := Nat.sub_pos_of_lt hprime.one_lt
    have hnot : ¬∀ q, q.Prime → q ∣ p-1 → q < Y :=
      fun h => hpns (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hnot
    obtain ⟨q, hq, hqdiv, hYq⟩ := hnot
    let a := (p-1)/q
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hpred hqdiv) hq.pos
    have he : a*q = p-1 := Nat.div_mul_cancel hqdiv
    have hY : 0 < Y := by
      by_contra h
      have hY0 : Y = 0 := by omega
      rw [hY0, mul_zero] at hX
      omega
    have haK : a ≤ K := by
      apply Nat.le_of_mul_le_mul_right (c := Y) _ hY
      calc
        a*Y ≤ a*q := Nat.mul_le_mul_left a hYq
        _ ≤ X := by omega
        _ ≤ K*Y := hX
    have hqX : q < X/a+1 := by
      have hqa : q*a ≤ X := by rw [mul_comm, he]; omega
      have hh := (Nat.le_div_iff_mul_le ha).mpr hqa
      omega
    apply Finset.mem_image.mpr
    refine ⟨⟨a,q⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨ha,haK⟩, ?_⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hqX, hq, ?_⟩
      change (a*q+1).Prime
      convert hprime using 1
      omega
    · change a*q+1 = p
      omega
  calc
    _ ≤ ∑ p ∈ F.image v, (tau (k+1) (p-1) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun p _ _ => by positivity)
    _ ≤ ∑ z ∈ F, (tau (k+1) (v z-1) : ℝ) :=
      Finset.sum_image_le_of_nonneg (fun p _ => by positivity)
    _ = ∑ a ∈ Finset.Icc 1 K, ∑ q ∈ P a, (tau (k+1) (a*q) : ℝ) := by
      dsimp [F, v]
      exact (Finset.sum_sigma' (Finset.Icc 1 K) P
        (fun a q => (tau (k+1) (a*q) : ℝ))).symm
    _ ≤ ∑ a ∈ Finset.Icc 1 K, ∑ _q ∈ P a, (k+1 : ℝ)*(tau (k+1) a : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro q hq
      have hp := (Finset.mem_filter.mp hq).2.1
      have h := tau_prime_mul_le k q a hp
      rw [mul_comm q a] at h
      exact_mod_cast h
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      change (primePairCofactorCount X a : ℝ) * ((k+1 : ℝ)*(tau (k+1) a : ℝ)) = _
      ring

lemma sum_tau_le_harmonic (k K : ℕ) :
    (∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ)) ≤
      (K : ℝ)*(harmonic K : ℝ)^k := by
  simp_rw [tau_cast]
  exact sum_zeta_pow_le_harmonic k K

/-- The higher-divisor cofactor weight costs only `eulerCost(k+1)` in the
main term, rather than a constant to the power k. -/
theorem weighted_prime_pair_cofactor_bound (k X K J : ℕ) (hKX : K ≤ X) (hJ : 0 < J) :
    (∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ)*primePairCofactorCount X a) ≤
      (16*(X : ℝ)/((J : ℝ)*Real.log 2)^2) *
        (eulerCost (k+1)*harmonicMoment (k+1) K) +
      ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) * (K : ℝ)*(harmonic K : ℝ)^k := by
  let B := 16*(X : ℝ)/((J : ℝ)*Real.log 2)^2
  let E := (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hb (a : ℕ) (ha : a ∈ Finset.Icc 1 K) :
      (primePairCofactorCount X a : ℝ) ≤
        B*((a : ℝ)/a.totient)^2/(a : ℝ)+E := by
    have ha0 := (Finset.mem_Icc.mp ha).1
    apply (prime_pair_cofactor_bound X a J ha0 ((Finset.mem_Icc.mp ha).2.trans hKX) hJ).trans
    calc
      _ ≤ (4*(X : ℝ)/((J : ℝ)*Real.log 2)^2) *
          ((4*((a : ℝ)/a.totient)^2)/(a : ℝ))+E := by
        gcongr
        exact Sieve.totient_ratio_two_mul_sq_le a ha0
      _ = _ := by dsimp [B,E]; ring
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ)*
        (B*((a : ℝ)/a.totient)^2/(a : ℝ)+E) :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hb a ha) (by positivity))
    _ = B*(∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ)*((a : ℝ)/a.totient)^2/(a : ℝ)) +
        E*(∑ a ∈ Finset.Icc 1 K, (tau (k+1) a : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ B*(eulerCost (k+1)*harmonicMoment (k+1) K)+E*((K : ℝ)*(harmonic K : ℝ)^k) :=
      _root_.add_le_add
        (mul_le_mul_of_nonneg_left (harmonicMoment_totient_ratio_le_cost k K) hB)
        (mul_le_mul_of_nonneg_left (sum_tau_le_harmonic k K) hE)
    _ = _ := by dsimp [B,E]; ring

/-- A complete finite upper bound on the rough part of the shifted-prime
moment. A suitable lower bound on the total moment is still needed. -/
theorem roughPrimeMoment_sieve_bound (k X K Y J : ℕ)
    (hX : X ≤ K*Y) (hKX : K ≤ X) (hJ : 0 < J) :
    roughPrimeMoment (k+1) X Y ≤ (k+1 : ℝ)*
      ((16*(X : ℝ)/((J : ℝ)*Real.log 2)^2)*
          (eulerCost (k+1)*harmonicMoment (k+1) K) +
        ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)*(K : ℝ)*(harmonic K : ℝ)^k) :=
  (roughPrimeMoment_le_cofactor_sum k X K Y hX).trans
    (mul_le_mul_of_nonneg_left (weighted_prime_pair_cofactor_bound k X K J hKX hJ)
      (by positivity))

end Erdos821.HigherDivisors

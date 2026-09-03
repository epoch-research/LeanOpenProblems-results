import Submission.HarmonicDivisorLower

/-!
# A finite lower-moment transfer with the distribution error explicit

The harmonic main term is unconditional. This file does not bound the
higher-divisor-weighted progression error, and therefore does not assert
the sharp shifted-prime moment needed to settle Erdős 821.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

open AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def shiftedMangoldtMoment (k X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, vonMangoldt n * (tau k (n-1) : ℝ)

noncomputable def nonprimeMangoldtMoment (k X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬n.Prime),
    vonMangoldt n * (tau k (n-1) : ℝ)

noncomputable def divisorProgressionError (k Q X : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ) *
    |residueOneMangoldt d X - mangoldtSum X/(d.totient : ℝ)|

lemma divisorProgressionError_nonneg (k Q X : ℕ) : 0 ≤ divisorProgressionError k Q X := by
  apply Finset.sum_nonneg
  intro d hd
  positivity

lemma divisor_progression_sum_le_mangoldtMoment (k Q X : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ)*residueOneMangoldt d X) ≤
      shiftedMangoldtMoment (k+1) X := by
  unfold residueOneMangoldt shiftedMangoldtMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  by_cases hn' : n = 1
  · subst n
    simp only [vonMangoldt_apply_one, ite_self, mul_zero, Finset.sum_const_zero, zero_mul, le_refl]
  have hn0 : n-1 ≠ 0 := by omega
  have hsub : (Finset.Icc 1 Q).filter (fun d => d ∣ n-1) ⊆ (n-1).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hn0⟩
  calc
    _ = vonMangoldt n * ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => d ∣ n-1), (tau k d : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [residue_one_iff_dvd_pred hn1]
      split_ifs <;> ring
    _ ≤ vonMangoldt n * ∑ d ∈ (n-1).divisors, (tau k d : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.cast_nonneg _))
        vonMangoldt_nonneg
    _ = _ := by rw [tau_succ, Nat.cast_sum]

lemma mangoldtMoment_lower_with_error (k Q X : ℕ) :
    mangoldtSum X * harmonicMoment k Q - divisorProgressionError k Q X ≤
      shiftedMangoldtMoment (k+1) X := by
  have hψ : 0 ≤ mangoldtSum X := Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
  have hmain : mangoldtSum X * harmonicMoment k Q ≤
      ∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ) * (mangoldtSum X/(d.totient : ℝ)) := by
    unfold harmonicMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
    have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    calc
      _ = (tau k d : ℝ)*(mangoldtSum X/(d : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hψ hφ hφd) (Nat.cast_nonneg _)
  have he : (∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ) * (mangoldtSum X/(d.totient : ℝ))) -
      (∑ d ∈ Finset.Icc 1 Q, (tau k d : ℝ)*residueOneMangoldt d X) ≤
        divisorProgressionError k Q X := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d hd
    calc
      _ = (tau k d : ℝ)*(mangoldtSum X/(d.totient : ℝ)-residueOneMangoldt d X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [neg_sub] using neg_le_abs (residueOneMangoldt d X - mangoldtSum X/(d.totient : ℝ)))
        (Nat.cast_nonneg _)
  have hs := divisor_progression_sum_le_mangoldtMoment k Q X
  linarith

lemma mangoldtMoment_factorial_lower_with_error (k Q X : ℕ) (hQ : 1 ≤ Q) :
    mangoldtSum X * ((Real.log (Q+1 : ℝ))^k/(k.factorial : ℝ)) - divisorProgressionError k Q X ≤
      shiftedMangoldtMoment (k+1) X := by
  apply le_trans _ (mangoldtMoment_lower_with_error k Q X)
  apply sub_le_sub_right
  exact mul_le_mul_of_nonneg_left (harmonicMoment_factorial_lower k Q hQ)
    (Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg))

lemma mangoldtMoment_le_primeMoment_add_nonprime (k X : ℕ) :
    shiftedMangoldtMoment k X ≤ Real.log X * shiftedPrimeMoment k X + nonprimeMangoldtMoment k X := by
  have hP : (Finset.Icc 1 X).filter Nat.Prime = (X+1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1,hpX⟩,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpX,hp⟩
      exact ⟨⟨hp.pos,by omega⟩,hp⟩
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X) Nat.Prime
    (fun n => vonMangoldt n * (tau k (n-1) : ℝ))
  change _ + nonprimeMangoldtMoment k X = shiftedMangoldtMoment k X at he
  rw [hP] at he
  rw [← he]
  apply _root_.add_le_add ?_ le_rfl
  unfold shiftedPrimeMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpX,hpr⟩ := Nat.mem_primesBelow.mp hp
  rw [vonMangoldt_apply_prime hpr]
  exact mul_le_mul_of_nonneg_right (log_nat_mono (by omega : p ≤ X)) (Nat.cast_nonneg _)

lemma nonprimeMangoldtMoment_le_of_bound (k X : ℕ) (hX : 1 ≤ X) (B : ℝ)
    (hB : ∀ n ∈ Finset.Icc 1 X, (tau k (n-1) : ℝ) ≤ B) :
    nonprimeMangoldtMoment k X ≤ B * (2*Real.sqrt X*Real.log X) := by
  have hB0 : 0 ≤ B := by
    have h := hB 1 (Finset.mem_Icc.mpr ⟨le_rfl,hX⟩)
    simpa only [Nat.sub_self, tau_zero_input, Nat.cast_zero] using h
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬n.Prime), vonMangoldt n * B :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
        (hB n (Finset.mem_filter.mp hn).1) vonMangoldt_nonneg)
    _ = B * ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le X hX) hB0

/-- An explicit lower transfer. Obtaining a suitably small value of the
weighted progression error is an additional arithmetic obligation. -/
theorem shiftedPrimeMoment_factorial_lower_with_error (k Q X : ℕ) (hQ : 1 ≤ Q) (hX : 1 ≤ X)
    (B : ℝ) (hB : ∀ n ∈ Finset.Icc 1 X, (tau (k+1) (n-1) : ℝ) ≤ B) :
    mangoldtSum X * ((Real.log (Q+1 : ℝ))^k/(k.factorial : ℝ)) -
        divisorProgressionError k Q X - B*(2*Real.sqrt X*Real.log X) ≤
      Real.log X * shiftedPrimeMoment (k+1) X := by
  have h1 := mangoldtMoment_factorial_lower_with_error k Q X hQ
  have h2 := mangoldtMoment_le_primeMoment_add_nonprime (k+1) X
  have h3 := nonprimeMangoldtMoment_le_of_bound (k+1) X hX B hB
  linarith

end Erdos821.HigherDivisors

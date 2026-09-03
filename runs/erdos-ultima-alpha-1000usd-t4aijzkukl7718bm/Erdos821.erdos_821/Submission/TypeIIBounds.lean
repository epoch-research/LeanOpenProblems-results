import Submission.MaximalLargeSieve
import Submission.TypeIEstimates
import Submission.DivisorMoments

/-!
# Coefficient-energy bounds for Type II sums

A natural-number formulation of the adaptive bilinear large sieve is
combined with divisor-square and von Mangoldt coefficient bounds.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

/-- The adaptive hyperbolic large sieve with natural input indices. -/
theorem adaptive_hyperbolic_large_sieve_nat
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℕ) (a b : ℕ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, (n : ℝ) ≤ X) (hB : ∀ n ∈ B, (n : ℝ) ≤ Y)
    (N : ℕ) (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N)
    (hAN : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) (hBN : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R q χ then
        (a m * b n) * χ ((m * n : ℕ) : ZMod (q : ℕ)) else 0‖) ≤
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2)) := by
  let e : ℕ ↪ ℤ := ⟨fun n => n, Nat.cast_injective⟩
  have h := adaptive_hyperbolic_large_sieve M Q hQ hM C hC (A.map e) (B.map e)
    (fun z => a z.toNat) (fun z => b z.toNat) X Y hX hY ?_ ?_ N R hR ?_ ?_
  · simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, Int.toNat_natCast,
      ← Nat.cast_mul, Nat.cast_le, Int.cast_natCast] using h
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hz
    simpa only [e, Function.Embedding.coeFn_mk, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      using hA n hn
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hz
    simpa only [e, Function.Embedding.coeFn_mk, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      using hB n hn
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hz
    change 1 ≤ (n : ℤ) ∧ (n : ℤ) ≤ N
    exact_mod_cast hAN n hn
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hz
    change 1 ≤ (n : ℤ) ∧ (n : ℤ) ≤ N
    exact_mod_cast hBN n hn

lemma longPart_vonMangoldt_nonneg (U n : ℕ) : 0 ≤ longPart vonMangoldt U n := by
  rw [longPart_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · rfl

lemma longPart_vonMangoldt_le_log (U n : ℕ) : longPart vonMangoldt U n ≤ Real.log n := by
  rw [longPart_apply]
  split_ifs
  · exact vonMangoldt_le_log
  · exact Real.log_natCast_nonneg n

lemma sum_longPart_vonMangoldt_sq_le (U N : ℕ) :
    (∑ n ∈ Icc 1 N, (longPart vonMangoldt U n) ^ 2) ≤ (N : ℝ) * (Real.log N) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (Real.log N) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have h := (longPart_vonMangoldt_le_log U n).trans (log_nat_mono (mem_Icc.mp hn).2)
      nlinarith [longPart_vonMangoldt_nonneg U n, Real.log_natCast_nonneg N]
    _ = _ := by simp

lemma sum_subset_typeII_energy_le (V X : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 X) :
    (∑ n ∈ A, ‖(vaughanTypeII V n : ℂ)‖ ^ 2) ≤ (X : ℝ) * (1 + Real.log X) ^ 3 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hA (fun n hn hnA => sq_nonneg _)).trans
    (sum_vaughanTypeII_sq_le V X)

lemma sum_subset_vonMangoldt_energy_le (U Y : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 1 Y) :
    (∑ n ∈ B, ‖(longPart vonMangoldt U n : ℂ)‖ ^ 2) ≤ (Y : ℝ) * (Real.log Y) ^ 2 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hB (fun n hn hnB => sq_nonneg _)).trans
    (sum_longPart_vonMangoldt_sq_le U Y)

/-- A Type II block with independently selected character cutoffs and
explicit coefficient-energy bounds. -/
theorem vaughan_typeII_block_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (U V X Y N : ℕ) (A B : Finset ℕ)
    (hA : A ⊆ Icc 1 X) (hB : B ⊆ Icc 1 Y)
    (hAN : ∀ n ∈ A, n ≤ N) (hBN : ∀ n ∈ B, n ≤ N)
    (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖∑ m ∈ A, ∑ n ∈ B, if m * n ≤ R q χ then
        ((vaughanTypeII V m : ℂ) * (longPart vonMangoldt U n : ℂ)) *
          χ ((m * n : ℕ) : ZMod (q : ℕ)) else 0‖) ≤
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
          (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
          ((X : ℝ) * (1 + Real.log X) ^ 3) * ((Y : ℝ) * (Real.log Y) ^ 2)) := by
  have h := adaptive_hyperbolic_large_sieve_nat M Q hQ hM C hC A B
    (fun n => (vaughanTypeII V n : ℂ)) (fun n => (longPart vonMangoldt U n : ℂ)) X Y
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun n hn => by exact_mod_cast (mem_Icc.mp (hA hn)).2)
    (fun n hn => by exact_mod_cast (mem_Icc.mp (hB hn)).2)
    N R hR (fun n hn => ⟨(mem_Icc.mp (hA hn)).1, hAN n hn⟩)
    (fun n hn => ⟨(mem_Icc.mp (hB hn)).1, hBN n hn⟩)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by
    have := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
    positivity)
  apply Real.sqrt_le_sqrt
  have hK : 0 ≤ (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
      (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) := by positivity
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (sum_subset_typeII_energy_le V X A hA) hK)
    (sum_subset_vonMangoldt_energy_le U Y B hB)
    (by positivity) (by have := Real.log_natCast_nonneg X; positivity)

end Erdos821.AnalyticSieve

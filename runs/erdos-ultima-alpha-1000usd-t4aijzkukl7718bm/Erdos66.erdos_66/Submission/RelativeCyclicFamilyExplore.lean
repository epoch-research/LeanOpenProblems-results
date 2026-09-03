import Submission.MixedCyclicThickeningExplore

/-! Finite nested cyclic families with a relative, rather than absolute,
mixed-convolution error. The mean coefficient is fixed before the prime. -/
namespace Erdos66RelativeCyclicFamily
open Erdos66MixedCyclicThickening
open scoped Classical
set_option maxHeartbeats 1000000

lemma relative_error_arithmetic (T i j : ℕ) (hT : 1 ≤ T)
    (hi : T ^ 2 ≤ i) (hj : T ^ 2 ≤ j) (E : ℝ) (hE : 0 ≤ E)
    (hEsq : E ^ 2 ≤ 16 * (i : ℝ) * j * (i + j)) :
    (T : ℝ) ^ 2 * (E + 10 * i + 10 * j + 8) +
      2 * T * (4 * i * j + E + 10 * i + 10 * j + 8) ≤ 112 * T * i * j := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hi' : (T : ℝ) ^ 2 ≤ i := by exact_mod_cast hi
  have hj' : (T : ℝ) ^ 2 ≤ j := by exact_mod_cast hj
  have hTi : (T : ℝ) ≤ i := by nlinarith
  have hTj : (T : ℝ) ≤ j := by nlinarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hscale : ((i : ℝ) + j) * (T : ℝ) ^ 2 ≤ 2 * i * j := by
    have h₁ := mul_le_mul_of_nonneg_left hj' hi0
    have h₂ := mul_le_mul_of_nonneg_left hi' hj0
    nlinarith
  have hsq₁ := mul_le_mul_of_nonneg_right hEsq (sq_nonneg (T : ℝ))
  have hsq₂ := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 16 * (i : ℝ) * j by positivity)
  have hEt : E * T ≤ 6 * (i : ℝ) * j := by
    have hET : 0 ≤ E * T := mul_nonneg hE (Nat.cast_nonneg _)
    have hij : 0 ≤ (i : ℝ) * j := mul_nonneg hi0 hj0
    nlinarith [sq_nonneg (E * T - 6 * (i : ℝ) * j)]
  have hlinear : (T : ℝ) * (E + 10 * i + 10 * j + 8) ≤ 34 * i * j := by
    have h₁ := mul_le_mul_of_nonneg_left hTj hi0
    have h₂ := mul_le_mul_of_nonneg_left hTi hj0
    have h₃ : (T : ℝ) ≤ i * j := by nlinarith
    nlinarith
  have hterm : 0 ≤ E + 10 * (i : ℝ) + 10 * j + 8 := by positivity
  have hsmall : E + 10 * (i : ℝ) + 10 * j + 8 ≤ 34 * i * j := by
    nlinarith [mul_le_mul_of_nonneg_right hT' hterm]
  have h₁ := mul_le_mul_of_nonneg_left hlinear (Nat.cast_nonneg (α := ℝ) T)
  have h₂ := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * (T : ℝ) by positivity)
  have hpos : 0 ≤ (T : ℝ) * i * j := by positivity
  nlinarith

/-- For fixed accuracy and a fixed number of integer levels, the coefficient
beta is chosen before the arbitrarily large modulus. Zero is the empty level. -/
theorem exists_relative_cyclic_family (η : ℝ) (hη : 0 < η) (H : ℕ) :
    ∃ β : ℝ, 0 < β ∧ ∀ N₀ : ℕ, ∃ M : ℕ, N₀ < M ∧ ∃ hM : NeZero M,
      ∃ C : ℕ → Finset (ZMod M), C 0 = ∅ ∧ Monotone C ∧
        ∀ i ≤ H, ∀ j ≤ H, ∀ z : ZMod M,
          |(((C i).filter (fun a ↦ z - a ∈ C j)).card : ℝ) - β * i * j| ≤ η * (β * i * j) := by
  obtain ⟨T, hTbig⟩ := exists_nat_gt (max (1 : ℝ) (28 / η))
  have hT' : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hTbig
  have hT : 1 ≤ T := by exact_mod_cast hT'.le
  have hηT : 28 < η * T := by
    have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt (le_max_right _ _) hTbig)
    linarith
  let D := T ^ 2
  let β : ℝ := 4 * (T : ℝ) ^ 2 * D ^ 2
  have hβ : 0 < β := by dsimp [β, D]; positivity
  refine ⟨β, hβ, fun N₀ ↦ ?_⟩
  letI : NeZero T := ⟨by omega⟩
  obtain ⟨p, hp, hpN, C, hC, E, he⟩ := exists_mixed_flat_cyclic_family (D * H) T (max N₀ 2)
  letI : Fact p.Prime := ⟨hp⟩
  let M := (p * T) ^ 2
  have hpT : p ≤ p * T := by nlinarith
  have hMp : p ≤ M := by dsimp [M]; nlinarith [show 2 ≤ p by omega]
  let C' : ℕ → Finset (ZMod M) := fun i ↦ if i = 0 then ∅ else C (D * i)
  refine ⟨M, by omega, inferInstance, C', by simp [C'], ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · simp [C', hi]
    · have hj : j ≠ 0 := by omega
      simp only [C', if_neg hi, if_neg hj]
      exact hC (Nat.mul_le_mul_left D hij)
  · intro i hiH j hjH z
    by_cases hi : i = 0
    · simp [C', hi]
    by_cases hj : j = 0
    · simp [C', hj]
    have hD : 0 < D := by dsimp [D]; positivity
    have hiD : T ^ 2 ≤ D * i := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D (show 1 ≤ i by omega)
    have hjD : T ^ 2 ≤ D * j := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D (show 1 ≤ j by omega)
    obtain ⟨hE, hEsq, hcount⟩ := he (D * i) (by positivity) (Nat.mul_le_mul_left D hiH)
      (D * j) (by positivity) (Nat.mul_le_mul_left D hjH)
    have hb := relative_error_arithmetic T (D * i) (D * j) hT hiD hjD (E (D * i) (D * j)) hE hEsq
    have hmain : 112 * (T : ℝ) * (D * i) * (D * j) ≤ η * (β * i * j) := by
      have hh := mul_le_mul_of_nonneg_right hηT.le (show 0 ≤ 4 * (T : ℝ) * (D * i) * (D * j) by positivity)
      dsimp [β]
      push_cast at hh ⊢
      nlinarith
    simp only [C', if_neg hi, if_neg hj]
    push_cast at hcount hb
    have hh := (hcount z).trans (hb.trans hmain)
    dsimp [β]
    push_cast at hh ⊢
    convert hh using 2 <;> ring

end Erdos66RelativeCyclicFamily

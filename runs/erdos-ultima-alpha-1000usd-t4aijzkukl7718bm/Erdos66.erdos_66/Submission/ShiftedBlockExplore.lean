import Submission.ShiftedProfileExplore

/-! Shifted taper estimates: a uniform endpoint error for the upper bound,
and a vanishing edge-loss term for the lower bound on late blocks. -/
namespace Erdos66ShiftedBlock
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66ConstantProfile
  Erdos66FiniteTaper Erdos66ShiftedProfile
open scoped Classical

lemma shifted_block_upper (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (hC : Antitone C) (H s q t : ℕ) (ht : t < M)
    (β D : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hcounts : ∀ i ≤ q, ∀ j ≤ q,
      (((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ) ≤
        β * (level H (i + s) : ℝ) * level H (j + s) + D) :
    (sumRep (blockSet M C) (q * M + t) : ℝ) ≤
      β * (H : ℝ) ^ 2 * (1 + b s ^ 2) + (q + 1) * D := by
  let R (i j : ℕ) : ℝ := (((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ)
  have hupp₀ := Finset.sum_le_sum (s := Finset.range q)
    (fun k hk ↦ hcounts k (by have := Finset.mem_range.mp hk; omega)
      (q - k - 1) (by omega))
  have hlevel : (∑ k ∈ Finset.range q,
      (level H (k + s) : ℝ) * level H (q - k - 1 + s)) ≤ (H : ℝ) ^ 2 := by
    by_cases hq : q = 0
    · subst q
      simp
    · have hh := (shifted_level_convolution_bounds H s (q - 1)).2
      rw [show q - 1 + 1 = q by omega] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [show q - k - 1 = q - 1 - k by omega]
  have hupp : (∑ k ∈ Finset.range q, R k (q - k - 1)) ≤ β * (H : ℝ) ^ 2 + q * D := by
    simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hupp₀
    have hh := mul_le_mul_of_nonneg_left hlevel hβ
    dsimp only [R]
    nlinarith
  have hend : R q 0 ≤ β * (H : ℝ) ^ 2 * b s ^ 2 + D := by
    have hh := hcounts q le_rfl 0 (Nat.zero_le q)
    simp only [Nat.zero_add] at hh
    have hb := mul_le_mul_of_nonneg_left (shifted_level_endpoint H s q) hβ
    dsimp only [R]
    nlinarith
  have hfiber := lower_add_upper M (C q) (C 0) t
  have hL : (lower M (C q) (C 0) t : ℝ) ≤ R q 0 := by
    dsimp [R]
    exact_mod_cast (show lower M (C q) (C 0) t ≤
      ((C q).filter (fun a ↦ (t : ZMod M) - a ∈ C 0)).card by omega)
  have hb := (block_brackets M C hC q t ht).2
  have hb' : (sumRep (blockSet M C) (q * M + t) : ℝ) ≤
      (∑ k ∈ Finset.range q, R k (q - k - 1)) + lower M (C q) (C 0) t := by
    dsimp [R]
    exact_mod_cast hb
  nlinarith

lemma shifted_block_lower (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (hC : Antitone C) (H s q t : ℕ) (ht : t < M)
    (β D : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hcounts : ∀ i ≤ q, ∀ j ≤ q,
      |(((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ) -
        β * (level H (i + s) : ℝ) * level H (j + s)| ≤ D) :
    β * (H : ℝ) ^ 2 * (1 - 2 * s * b q - b s ^ 2) -
        2 * β * H * (q + 1) - (q + 2) * D ≤
      (sumRep (blockSet M C) (q * M + t) : ℝ) := by
  let R (i j : ℕ) : ℝ := (((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ)
  have hr (i j : ℕ) (hi : i ≤ q) (hj : j ≤ q) :
      β * (level H (i + s) : ℝ) * level H (j + s) - D ≤ R i j ∧
      R i j ≤ β * (level H (i + s) : ℝ) * level H (j + s) + D := by
    have hh := abs_le.mp (hcounts i hi j hj)
    dsimp [R]
    constructor <;> linarith
  have hlow₀ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k hk ↦ (hr k (q - k) (by have := Finset.mem_range.mp hk; omega) (by omega)).1)
  have hlow : β * ((H : ℝ) ^ 2 * (1 - 2 * s * b q) - 2 * H * (q + 1)) - (q + 1) * D ≤
      ∑ k ∈ Finset.range (q + 1), R k (q - k) := by
    simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hlow₀
    have hh := mul_le_mul_of_nonneg_left (shifted_level_convolution_bounds H s q).1 hβ
    nlinarith
  have hend : R q 0 ≤ β * (H : ℝ) ^ 2 * b s ^ 2 + D := by
    have hh := (hr q 0 le_rfl (Nat.zero_le q)).2
    simp only [Nat.zero_add] at hh
    have hb := mul_le_mul_of_nonneg_left (shifted_level_endpoint H s q) hβ
    nlinarith
  have hfiber := lower_add_upper M (C q) (C 0) t
  have hU : (upper M (C q) (C 0) t : ℝ) ≤ R q 0 := by
    dsimp [R]
    exact_mod_cast (show upper M (C q) (C 0) t ≤
      ((C q).filter (fun a ↦ (t : ZMod M) - a ∈ C 0)).card by omega)
  have hb := (block_brackets M C hC q t ht).1
  have hb' : (∑ k ∈ Finset.range (q + 1), R k (q - k)) ≤
      (sumRep (blockSet M C) (q * M + t) : ℝ) + upper M (C q) (C 0) t := by
    dsimp [R]
    exact_mod_cast hb
  nlinarith

lemma shifted_block_error (M : ℕ) [NeZero M] (C : ℕ → Finset (ZMod M))
    (hC : Antitone C) (H s q t : ℕ) (ht : t < M)
    (β D : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hcounts : ∀ i ≤ q, ∀ j ≤ q,
      |(((C i).filter (fun a ↦ (t : ZMod M) - a ∈ C j)).card : ℝ) -
        β * (level H (i + s) : ℝ) * level H (j + s)| ≤ D) :
    |(sumRep (blockSet M C) (q * M + t) : ℝ) - β * (H : ℝ) ^ 2| ≤
      β * (H : ℝ) ^ 2 * (2 * s * b q + b s ^ 2) +
        2 * β * H * (q + 1) + (q + 2) * D := by
  have hlo := shifted_block_lower M C hC H s q t ht β D hβ hD hcounts
  have hhi := shifted_block_upper M C hC H s q t ht β D hβ hD (fun i hi j hj ↦ by
    have hh := (abs_le.mp (hcounts i hi j hj)).2
    linarith)
  have hnon : 0 ≤ β * (H : ℝ) ^ 2 * (2 * s * b q) + 2 * β * H * (q + 1) + D := by
    have hb := (b_pos q).le
    positivity
  rw [abs_le]
  constructor <;> nlinarith

end Erdos66ShiftedBlock

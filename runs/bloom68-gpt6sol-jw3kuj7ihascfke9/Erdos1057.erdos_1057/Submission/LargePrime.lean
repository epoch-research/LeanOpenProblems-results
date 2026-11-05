import Submission.Korselt

/-!
# A quantitative bound for Carmichael numbers with large prime factors

Korselt's cofactor congruence puts a Carmichael number with prime factor `p` in a
progression `p * (1 + k * (p - 1))`, where `k ≥ 1`. Counting these progressions
and telescoping `1 / (p * (p - 1))` bounds the number with `p ≥ Y` by `2 * X / Y`.
-/

namespace Erdos1057

/-- Carmichael numbers at most `X` having some prime factor at least `Y`. -/
def largePrimeCarmichaels (X Y : ℕ) : Set ℕ :=
  {n | IsCarmichael n ∧ n ≤ X ∧ ∃ p, p.Prime ∧ Y ≤ p ∧ p ∣ n}

private theorem largePrimeCarmichaels_card_le_sum (X Y : ℕ) :
    (largePrimeCarmichaels X Y).ncard ≤
      ∑ p ∈ Finset.Icc Y X, X / (p * (p - 1)) := by
  classical
  let s : Finset ℕ := (Finset.Icc Y X).biUnion fun p =>
    (Finset.Icc 1 (X / (p * (p - 1)))).image (fun k => p * (1 + k * (p - 1)))
  have hcover : largePrimeCarmichaels X Y ⊆ (s : Set ℕ) := by
    intro n hn
    obtain ⟨hnC, hX, p, hp, hYp, hpn⟩ := hn
    obtain ⟨m, rfl⟩ := hpn
    have hpm : p ≤ m := isCarmichael_prime_le_cofactor hnC hp rfl
    have hp2 : 2 ≤ p := hp.two_le
    have hm1 : 1 ≤ m := by omega
    obtain ⟨k, hk⟩ := isCarmichael_cofactor_constraint hnC hp (m := m) rfl
    have hkpos : 1 ≤ k := by
      by_contra h
      have hzero : k = 0 := by omega
      subst k
      simp only [mul_zero] at hk
      omega
    have hm : m = 1 + k * (p - 1) := by
      rw [mul_comm (p - 1) k] at hk
      omega
    have hden : 0 < p * (p - 1) := Nat.mul_pos hp.pos (by omega)
    have hkX : k ≤ X / (p * (p - 1)) := by
      apply (Nat.le_div_iff_mul_le hden).2
      calc
        k * (p * (p - 1)) = p * (k * (p - 1)) := by ac_rfl
        _ ≤ p * m := Nat.mul_le_mul_left p (by omega)
        _ ≤ X := hX
    have hpX : p ≤ X := by
      calc
        p = p * 1 := by simp
        _ ≤ p * m := Nat.mul_le_mul_left p hm1
        _ ≤ X := hX
    change p * m ∈ (Finset.Icc Y X).biUnion fun p =>
      (Finset.Icc 1 (X / (p * (p - 1)))).image (fun k => p * (1 + k * (p - 1)))
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_Icc.mpr ⟨hYp, hpX⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr ⟨hkpos, hkX⟩, ?_⟩
    rw [hm]
  calc
    (largePrimeCarmichaels X Y).ncard ≤ s.card := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
    _ ≤ ∑ p ∈ Finset.Icc Y X,
          ((Finset.Icc 1 (X / (p * (p - 1)))).image
            (fun k => p * (1 + k * (p - 1)))).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Finset.Icc Y X, (Finset.Icc 1 (X / (p * (p - 1)))).card :=
      Finset.sum_le_sum fun p _ => Finset.card_image_le
    _ = ∑ p ∈ Finset.Icc Y X, X / (p * (p - 1)) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [Nat.card_Icc]

private theorem reciprocal_sum_le (X Y : ℕ) (hY : 3 ≤ Y) :
    (∑ p ∈ Finset.Icc Y X, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      (1 : ℝ) / ((Y : ℝ) - 1) := by
  by_cases hYX : Y ≤ X
  · have hsum :
        (∑ p ∈ Finset.Icc Y X,
          ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) =
          1 / ((Y : ℝ) - 1) - 1 / (X : ℝ) := by
      let f : ℕ → ℝ := fun q => 1 / ((q : ℝ) - 1)
      have htel := Finset.sum_Ico_sub f (show Y ≤ X + 1 by omega)
      calc
        _ = ∑ p ∈ Finset.Ico Y (X + 1), -(f (p + 1) - f p) := by
          rw [← Finset.Ico_succ_right_eq_Icc]
          apply Finset.sum_congr rfl
          intro p _
          have hstep : (((p + 1 : ℕ) : ℝ) - 1) = (p : ℝ) := by push_cast; ring
          dsimp [f]
          rw [hstep]
          ring
        _ = -(f (X + 1) - f Y) := by
          rw [Finset.sum_neg_distrib, htel]
        _ = 1 / ((Y : ℝ) - 1) - 1 / (X : ℝ) := by
          have hstep : (((X + 1 : ℕ) : ℝ) - 1) = (X : ℝ) := by push_cast; ring
          dsimp [f]
          rw [hstep]
          ring
    calc
      _ = ∑ p ∈ Finset.Icc Y X,
            ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpY : Y ≤ p := (Finset.mem_Icc.mp hp).1
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
          have hp1 : (p : ℝ) - 1 ≠ 0 := by
            have hpr : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
            linarith
          field_simp
          ring
      _ = 1 / ((Y : ℝ) - 1) - 1 / (X : ℝ) := hsum
      _ ≤ 1 / ((Y : ℝ) - 1) := by
        have : 0 ≤ (1 : ℝ) / (X : ℝ) := by positivity
        linarith
  · have hempty : Finset.Icc Y X = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp only [hempty, Finset.sum_empty]
    have hy : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
    exact le_of_lt (div_pos (by norm_num : (0 : ℝ) < 1) (by linarith))

/-- For `Y ≥ 3`, at most `⌊2 X / Y⌋` Carmichael numbers up to `X` have
some prime divisor at least `Y`. In particular this is an unconditional `O(X/Y)` bound. -/
theorem largePrimeCarmichaels_card_le (X Y : ℕ) (hY : 3 ≤ Y) :
    (largePrimeCarmichaels X Y).ncard ≤ 2 * X / Y := by
  have hYr : (3 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hratio : (1 : ℝ) / ((Y : ℝ) - 1) ≤ 2 / (Y : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < Y - 1)
      (by linarith : (0 : ℝ) < Y)).2
    nlinarith
  have hreal : ((largePrimeCarmichaels X Y).ncard : ℝ) ≤
      ((2 * X : ℕ) : ℝ) / (Y : ℝ) := by
    calc
      ((largePrimeCarmichaels X Y).ncard : ℝ) ≤
          ((∑ p ∈ Finset.Icc Y X, X / (p * (p - 1)) : ℕ) : ℝ) := by
            exact_mod_cast largePrimeCarmichaels_card_le_sum X Y
      _ = ∑ p ∈ Finset.Icc Y X, ((X / (p * (p - 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
      _ ≤ ∑ p ∈ Finset.Icc Y X, (X : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : 1 ≤ p := by have := (Finset.mem_Icc.mp hp).1; omega
        simpa only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one] using
          (Nat.cast_div_le (α := ℝ) (m := X) (n := p * (p - 1)))
      _ = (X : ℝ) * (∑ p ∈ Finset.Icc Y X,
          (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ (X : ℝ) * (1 / ((Y : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (reciprocal_sum_le X Y hY) (Nat.cast_nonneg _)
      _ ≤ (X : ℝ) * (2 / (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
      _ = ((2 * X : ℕ) : ℝ) / (Y : ℝ) := by push_cast; ring
  have hypos : (0 : ℝ) < (Y : ℝ) := by linarith
  have hmul : ((largePrimeCarmichaels X Y).ncard : ℝ) * (Y : ℝ) ≤
      ((2 * X : ℕ) : ℝ) := (le_div_iff₀ hypos).mp hreal
  exact (Nat.le_div_iff_mul_le (by omega : 0 < Y)).mpr (by exact_mod_cast hmul)

end Erdos1057

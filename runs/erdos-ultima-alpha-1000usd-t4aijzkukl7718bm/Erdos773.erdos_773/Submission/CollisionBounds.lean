import FormalConjecturesUtil
import Submission.DivisorBound

/-! Bounds for square-difference representations. -/

namespace Erdos773

open Finset Filter

lemma difference_factor {x y D : ℕ} (hxy : y < x) (he : x ^ 2 = y ^ 2 + D) :
    D = (x - y) * (x + y) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hxy.le
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [he]

def squareDifferenceReps (N D : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 < p.2 ∧ p.2 ^ 2 = p.1 ^ 2 + D)

lemma squareDifferenceReps_card_le (N D : ℕ) (hD : 0 < D) :
    (squareDifferenceReps N D).card ≤ D.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2 + p.1, difference_factor hp.1 hp.2⟩, hD.ne'⟩
  · intro p hp q hq heq
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq⟩ := Finset.mem_filter.mp hq
    have hpF := difference_factor hp.1 hp.2
    have hqF := difference_factor hq.1 hq.2
    dsimp at heq
    rw [← heq] at hqF
    have hsum : p.2 + p.1 = q.2 + q.1 := by
      exact mul_left_cancel₀ (Nat.sub_pos_of_lt hp.1).ne' (hpF.symm.trans hqF)
    apply Prod.ext <;> omega

lemma squareDifferenceReps_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N D : ℕ, 0 < D → D ≤ N ^ 2 →
      ((squareDifferenceReps N D).card : ℝ) ≤ C * (N : ℝ) ^ (2 * δ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_subpower δ hδ
  refine ⟨C, hC, ?_⟩
  intro N D hD hDN
  have hDN' : (D : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hDN
  calc
    ((squareDifferenceReps N D).card : ℝ) ≤ (D.divisors.card : ℝ) := by
      exact_mod_cast squareDifferenceReps_card_le N D hD
    _ ≤ C * (D : ℝ) ^ δ := hbound D
    _ ≤ C * ((N : ℝ) ^ 2) ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg D) hDN' hδ.le) hC.le
    _ = C * (N : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      norm_num

def squareCollisions (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter
    (fun t => t.1.2 < t.1.1 ∧ t.1.1 ^ 2 + t.2.1 ^ 2 = t.1.2 ^ 2 + t.2.2 ^ 2)

lemma square_collision_fiber (N : ℕ) (p : ℕ × ℕ) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter
      (fun q => p.2 < p.1 ∧ p.1 ^ 2 + q.1 ^ 2 = p.2 ^ 2 + q.2 ^ 2)) =
    if p.2 < p.1 then squareDifferenceReps N (p.1 ^ 2 - p.2 ^ 2) else ∅ := by
  by_cases h : p.2 < p.1
  · have hsq : p.2 ^ 2 < p.1 ^ 2 := by nlinarith
    have hsub := Nat.sub_add_cancel hsq.le
    have hequiv (q : ℕ × ℕ) :
        p.1 ^ 2 + q.1 ^ 2 = p.2 ^ 2 + q.2 ^ 2 ↔
          q.1 < q.2 ∧ q.2 ^ 2 = q.1 ^ 2 + (p.1 ^ 2 - p.2 ^ 2) := by
      constructor
      · intro he
        constructor
        · nlinarith
        · omega
      · intro he
        omega
    ext q
    simp [h, squareDifferenceReps, hequiv]
  · simp [h]

lemma squareCollisions_card (N : ℕ) :
    (squareCollisions N).card = ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
      if p.2 < p.1 then (squareDifferenceReps N (p.1 ^ 2 - p.2 ^ 2)).card else 0 := by
  unfold squareCollisions
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.card_filter, square_collision_fiber]
  split <;> simp

lemma squareCollisions_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N : ℕ,
      ((squareCollisions N).card : ℝ) ≤ C * (N : ℝ) ^ (2 + 2 * δ) := by
  obtain ⟨C, hC, hrepr⟩ := squareDifferenceReps_subpower δ hδ
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN, squareCollisions, Real.zero_rpow (by linarith : (2 + 2 * δ) ≠ 0)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [squareCollisions_card, Nat.cast_sum]
  calc
    _ ≤ ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), C * (N : ℝ) ^ (2 * δ) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with h
      · simp only [Finset.mem_product, Finset.mem_Icc] at hp
        have hD : 0 < p.1 ^ 2 - p.2 ^ 2 := Nat.sub_pos_of_lt (by nlinarith)
        have hDN : p.1 ^ 2 - p.2 ^ 2 ≤ N ^ 2 := by
          exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hp.1.2 2)
        exact hrepr N _ hD hDN
      · simp only [Nat.cast_zero]
        positivity
    _ = C * (N : ℝ) ^ (2 + 2 * δ) := by
      simp only [Finset.sum_const, Finset.card_product, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_mul]
      rw [Real.rpow_add hNpos]
      norm_num [Real.rpow_two]
      ring

#print axioms squareCollisions_subpower

end Erdos773

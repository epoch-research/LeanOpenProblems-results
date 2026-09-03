import FormalConjecturesUtil
import Submission.DivisorBound

/-! Counting three-term progressions among the squares by their gaps. -/

namespace Erdos773

open Finset Filter

lemma squareAP_parameters {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) :
    let y := c - b
    let d := 2 * b - (a + c)
    0 < y ∧ 0 < d ∧ a + y + d = b ∧ a + 2 * y + d = c ∧
      2 * y ^ 2 = d * (2 * a + d) := by
  dsimp only
  have hy : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hyb : c - b + b = c := Nat.sub_add_cancel hbc.le
  have hac : a + c < 2 * b := by
    have he' : (a : ℤ) ^ 2 + (c : ℤ) ^ 2 = 2 * (b : ℤ) ^ 2 := by exact_mod_cast he
    have hpos : 0 < ((a : ℤ) - c) ^ 2 := sq_pos_of_ne_zero (by omega)
    by_contra! h
    have h' : 2 * (b : ℤ) ≤ (a : ℤ) + c := by exact_mod_cast h
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 2 * b) h' 2
    nlinarith only [hs, he', hpos]
  have hd : 0 < 2 * b - (a + c) := Nat.sub_pos_of_lt hac
  have hdac := Nat.sub_add_cancel hac.le
  have hb : a + (c - b) + (2 * b - (a + c)) = b := by omega
  have hc : a + 2 * (c - b) + (2 * b - (a + c)) = c := by omega
  refine ⟨hy, hd, hb, hc, ?_⟩
  nth_rw 1 [← hb] at he
  nth_rw 1 [← hc] at he
  nlinarith only [he]

def squareAPs (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ (Icc 1 N)).filter
    (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧ t.1.1 ^ 2 + t.2 ^ 2 = 2 * t.1.2 ^ 2)

lemma squareAPs_card_le (N : ℕ) :
    (squareAPs N).card ≤ ∑ y ∈ Icc 1 N, (2 * y ^ 2).divisors.card := by
  let U : Finset (ℕ × ℕ) := (Icc 1 N).biUnion (fun y => {y} ×ˢ (2 * y ^ 2).divisors)
  have hU : U.card ≤ ∑ y ∈ Icc 1 N, (2 * y ^ 2).divisors.card := by
    exact Finset.card_biUnion_le.trans_eq (by simp)
  apply le_trans _ hU
  apply Finset.card_le_card_of_injOn (fun t : (ℕ × ℕ) × ℕ =>
    (t.2 - t.1.2, 2 * t.1.2 - (t.1.1 + t.2)))
  · intro t ht
    obtain ⟨hmem, hab, hbc, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
    apply Finset.mem_biUnion.mpr
    refine ⟨t.2 - t.1.2, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc] at hmem
      exact Finset.mem_Icc.mpr ⟨hy, (Nat.sub_le _ _).trans hmem.2.2⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_singleton_self _, Nat.mem_divisors.mpr ?_⟩
      exact ⟨⟨2 * t.1.1 + (2 * t.1.2 - (t.1.1 + t.2)), hfac⟩, by positivity⟩
  · intro t ht u hu heq
    obtain ⟨_, hab, hbc, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨_, hab', hbc', he'⟩ := Finset.mem_filter.mp hu
    obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
    obtain ⟨hy', hd', hb', hc', hfac'⟩ := squareAP_parameters hab' hbc' he'
    have hyEq : t.2 - t.1.2 = u.2 - u.1.2 := congrArg Prod.fst heq
    have hdEq : 2 * t.1.2 - (t.1.1 + t.2) = 2 * u.1.2 - (u.1.1 + u.2) := congrArg Prod.snd heq
    rw [← hyEq, ← hdEq] at hfac'
    have haEq : 2 * t.1.1 + (2 * t.1.2 - (t.1.1 + t.2)) =
        2 * u.1.1 + (2 * t.1.2 - (t.1.1 + t.2)) :=
      mul_left_cancel₀ hd.ne' (hfac.symm.trans hfac')
    apply Prod.ext
    · apply Prod.ext <;> omega
    · omega

lemma squareAPs_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N : ℕ,
      ((squareAPs N).card : ℝ) ≤ C * (N : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_subpower δ hδ
  refine ⟨C * 2 ^ δ, by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN, squareAPs, Real.zero_rpow (by linarith : 1 + 2 * δ ≠ 0)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  calc
    ((squareAPs N).card : ℝ) ≤ ∑ y ∈ Icc 1 N, ((2 * y ^ 2).divisors.card : ℝ) := by
      exact_mod_cast squareAPs_card_le N
    _ ≤ ∑ y ∈ Icc 1 N, C * (2 * (N : ℝ) ^ 2) ^ δ := by
      apply Finset.sum_le_sum
      intro y hy
      have hyN : (y : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hy).2
      have hpow : (2 * y ^ 2 : ℕ) ≤ 2 * N ^ 2 := Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left (Finset.mem_Icc.mp hy).2 2)
      apply (hbound (2 * y ^ 2)).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact_mod_cast hpow
    _ = (C * 2 ^ δ) * (N : ℝ) ^ (1 + 2 * δ) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg N), Real.rpow_add hNpos]
      norm_num
      ring

#print axioms squareAPs_subpower

end Erdos773

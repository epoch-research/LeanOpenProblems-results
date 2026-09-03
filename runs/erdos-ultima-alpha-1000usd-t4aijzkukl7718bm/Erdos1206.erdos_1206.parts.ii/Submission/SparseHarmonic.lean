import FormalConjecturesUtil

/-! A reciprocal-summability criterion from a power-saving counting bound. -/

namespace Erdos1206
open scoped Classical

lemma summable_reciprocals_of_pow_prefix_bound {S : Set ℕ} {C : ℕ}
    (hcount : ∀ j : ℕ, (S ∩ Set.Iio (16 ^ j)).ncard ≤ C * 8 ^ j) :
    Summable (fun n : ℕ => if n ∈ S then (1 : ℝ) / n else 0) := by
  classical
  let f : ℕ → ℝ := fun n => if n ∈ S then 1 / n else 0
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hf0 : f 0 = 0 := by simp [f]
  have hblock (j : ℕ) : (∑ n ∈ Finset.Ico (16 ^ j) (16 ^ (j + 1)), f n) ≤
      8 * (C : ℝ) * (1 / 2 : ℝ) ^ j := by
    let F := (Finset.Ico (16 ^ j) (16 ^ (j + 1))).filter (fun n => n ∈ S)
    have hcard : F.card ≤ C * 8 ^ (j + 1) := by
      have hsub : (F : Set ℕ) ⊆ S ∩ Set.Iio (16 ^ (j + 1)) := by
        intro n hn
        change n ∈ (Finset.Ico (16 ^ j) (16 ^ (j + 1))).filter (fun n => n ∈ S) at hn
        have hh := Finset.mem_filter.mp hn
        exact ⟨hh.2, (Finset.mem_Ico.mp hh.1).2⟩
      have hh := Set.ncard_le_ncard hsub
      rw [Set.ncard_coe_finset] at hh
      exact hh.trans (hcount (j + 1))
    have hden : (0 : ℝ) < (16 : ℝ) ^ j := by positivity
    have hsum : (∑ n ∈ Finset.Ico (16 ^ j) (16 ^ (j + 1)), f n) =
        ∑ n ∈ F, (1 : ℝ) / n := by
      simp only [F, Finset.sum_filter, f]
    rw [hsum]
    calc
      _ ≤ ∑ n ∈ F, (1 : ℝ) / (16 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
        exact one_div_le_one_div_of_le hden (by exact_mod_cast hh)
      _ = (F.card : ℝ) * (1 / (16 : ℝ) ^ j) := by simp
      _ ≤ ((C : ℝ) * (8 : ℝ) ^ (j + 1)) * (1 / (16 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 8 * (C : ℝ) * ((8 : ℝ) ^ j / (16 : ℝ) ^ j) := by rw [pow_succ]; ring
      _ = 8 * (C : ℝ) * ((8 : ℝ) / 16) ^ j := by rw [div_pow]
      _ = _ := by norm_num
  have hpartial (j : ℕ) : (∑ n ∈ Finset.range (16 ^ j), f n) ≤
      16 * (C : ℝ) * (1 - (1 / 2 : ℝ) ^ j) := by
    induction j with
    | zero => simp [hf0]
    | succ j ih =>
      have hle : 16 ^ j ≤ 16 ^ (j + 1) := by
        rw [pow_succ]
        omega
      have hs := Finset.sum_range_add_sum_Ico f hle
      have hb := hblock j
      rw [pow_succ (1 / 2 : ℝ)]
      nlinarith
  apply summable_of_sum_range_le hf (c := 16 * (C : ℝ))
  intro N
  have hN : N ≤ 16 ^ N := by
    exact (Nat.lt_pow_self (by decide : 1 < 16)).le
  have hs : (∑ n ∈ Finset.range N, f n) ≤ ∑ n ∈ Finset.range (16 ^ N), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun n _ _ => hf n)
  have hp := hpartial N
  have hz : 0 ≤ 16 * (C : ℝ) * (1 / 2 : ℝ) ^ N := by positivity
  linarith

#print axioms summable_reciprocals_of_pow_prefix_bound

end Erdos1206

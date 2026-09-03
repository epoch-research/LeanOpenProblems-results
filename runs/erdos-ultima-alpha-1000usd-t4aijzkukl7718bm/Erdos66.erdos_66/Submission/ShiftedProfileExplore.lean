import Submission.FiniteTaperExplore

/-! Shifting the binomial taper reduces the endpoint error uniformly, while
its self-convolution still tends to one. -/
namespace Erdos66ShiftedProfile
open Filter AdditiveCombinatorics Erdos66ConstantProfile Erdos66FiniteTaper
open scoped Topology

noncomputable def tailConv (s q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (q + 1), b (k + s) * b (q - k + s)

lemma tailConv_zero (q : ℕ) : tailConv 0 q = 1 := by
  simpa only [tailConv, Nat.add_zero, sumConv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using b_convolution q

lemma tailConv_step (s q : ℕ) :
    tailConv s (q + 2) = tailConv (s + 1) q + 2 * b s * b (q + s + 2) := by
  unfold tailConv
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have he : (∑ k ∈ Finset.range (q + 1), b (k + 1 + s) * b (q + 2 - (k + 1) + s)) =
      ∑ k ∈ Finset.range (q + 1), b (k + (s + 1)) * b (q - k + (s + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkq := Finset.mem_range.mp hk
    rw [show k + 1 + s = k + (s + 1) by omega,
      show q + 2 - (k + 1) + s = q - k + (s + 1) by omega]
  rw [he]
  simp only [Nat.zero_add, Nat.sub_zero, Nat.sub_self]
  rw [show q + 2 + s = q + s + 2 by omega]
  ring

lemma tailConv_upper (s q : ℕ) : tailConv s q ≤ 1 := by
  rw [← tailConv_zero q]
  apply Finset.sum_le_sum
  intro k hk
  simp only [Nat.add_zero]
  exact mul_le_mul (b_antitone (by omega : k ≤ k + s))
    (b_antitone (by omega : q - k ≤ q - k + s)) (b_pos _).le (b_pos _).le

lemma tailConv_lower (s q : ℕ) : 1 - 2 * (s : ℝ) * b q ≤ tailConv s q := by
  induction s generalizing q with
  | zero => simp [tailConv_zero]
  | succ s ih =>
    have hh := ih (q + 2)
    have hs := tailConv_step s q
    have h₁ : 2 * (s : ℝ) * b (q + 2) ≤ 2 * s * b q :=
      mul_le_mul_of_nonneg_left (b_antitone (by omega)) (by positivity)
    have h₂ : b s * b (q + s + 2) ≤ b q := by
      calc
        _ ≤ 1 * b q := mul_le_mul (b_le_one s) (b_antitone (by omega))
          (b_pos _).le (by norm_num)
        _ = _ := one_mul _
    push_cast
    nlinarith

lemma tailConv_tendsto (s : ℕ) : Tendsto (tailConv s) atTop (𝓝 1) := by
  have hh := (b_tendsto_zero.const_mul (2 * (s : ℝ))).const_sub 1
  simp only [mul_zero, sub_zero] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hh tendsto_const_nhds
    (tailConv_lower s) (tailConv_upper s)

lemma shifted_level_convolution_bounds (H s q : ℕ) :
    (H : ℝ) ^ 2 * (1 - 2 * s * b q) - 2 * H * (q + 1) ≤
      (∑ k ∈ Finset.range (q + 1), (level H (k + s) : ℝ) * level H (q - k + s)) ∧
    (∑ k ∈ Finset.range (q + 1), (level H (k + s) : ℝ) * level H (q - k + s)) ≤
      (H : ℝ) ^ 2 := by
  have h₁ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k _ ↦ (level_product_bounds H (k + s) (q - k + s)).1)
  have h₂ := Finset.sum_le_sum (s := Finset.range (q + 1))
    (fun k _ ↦ (level_product_bounds H (k + s) (q - k + s)).2)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h₁ h₂
  have hlo := mul_le_mul_of_nonneg_left (tailConv_lower s q) (sq_nonneg (H : ℝ))
  have hhi := mul_le_mul_of_nonneg_left (tailConv_upper s q) (sq_nonneg (H : ℝ))
  dsimp [tailConv] at hlo hhi
  constructor <;> nlinarith

lemma shifted_level_endpoint (H s q : ℕ) :
    (level H (q + s) : ℝ) * level H s ≤ (H : ℝ) ^ 2 * (b s) ^ 2 := by
  have hh := (level_product_bounds H (q + s) s).2
  have hm : b (q + s) * b s ≤ b s ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right
      (b_antitone (by omega : s ≤ q + s)) (b_pos s).le
  exact hh.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg _))

end Erdos66ShiftedProfile

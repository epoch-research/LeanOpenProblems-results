import Submission.InverseTotientMoments
import Submission.Rankin

/-!
# Endpoint bounds for inverse-totient collision moments

The endpoint bounds here do not assert convergence at any fixed exponent
strictly below one. They are compatible with the full Erdős 821 conjecture.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

open Sieve

lemma sum_reciprocal_totient_le_harmonic (A : ℕ) :
    (∑ m ∈ Icc 1 A, 1 / (Nat.totient m : ℝ)) ≤
      totientRatioAverageConstant * (harmonic A : ℝ) := by
  apply le_trans _ (totient_ratio_harmonic_average A)
  apply sum_le_sum
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have hφ0 : (0 : ℝ) < Nat.totient m := by
    exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hm).1
  have hφm : (Nat.totient m : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hratio : 1 ≤ (m : ℝ) / Nat.totient m := (one_le_div hφ0).mpr hφm
  calc
    1 / (Nat.totient m : ℝ) = ((m : ℝ) / Nat.totient m) / m := by field_simp
    _ ≤ ((m : ℝ) / Nat.totient m) ^ 2 / m :=
      div_le_div_of_nonneg_right (by nlinarith) hm0.le

lemma totient_ge_two_pow_of_input_ge (j m : ℕ) (hj : 3 ≤ j)
    (hm : 2 ^ (4 * j) ≤ m) : 2 ^ j ≤ Nat.totient m := by
  have hp : m ≤ 24 * (Nat.totient m) ^ 2 := by
    simpa using input_pow_le_totient_pow m 1 (by decide)
  by_contra h
  have hφ : Nat.totient m ≤ 2 ^ j := (Nat.lt_of_not_ge h).le
  have h24 : 24 < 2 ^ (2 * j) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 6 ≤ 2 * j by omega)
    norm_num at h ⊢
    omega
  have hpow : (Nat.totient m) ^ 2 ≤ 2 ^ (2 * j) := by
    simpa only [← pow_mul, Nat.mul_comm j 2] using Nat.pow_le_pow_left hφ 2
  have hlt : 24 * 2 ^ (2 * j) < 2 ^ (4 * j) := by
    calc
      _ < 2 ^ (2 * j) * 2 ^ (2 * j) := Nat.mul_lt_mul_of_pos_right h24 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  exact (not_lt_of_ge hm) ((hp.trans (Nat.mul_le_mul_left 24 hpow)).trans_lt hlt)

lemma harmonic_fourfold_block_upper (j : ℕ) (hj : 1 ≤ j) :
    (harmonic (2 ^ (4 * (j + 1))) : ℝ) ≤ 10 * (j : ℝ) := by
  have h := harmonic_le_one_add_log (2 ^ (4 * (j + 1)))
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (α := ℝ) (4 * (j + 1)))
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  push_cast at h hmul
  nlinarith

/-- Grouping a nonnegative series into geometric intervals does not require
monotonicity of its summands. -/
lemma summable_of_summable_geometric_blocks (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (t : ℕ) (ht : 1 ≤ t)
    (H : Summable (fun j : ℕ => ∑ n ∈ Ico (2 ^ (t * j)) (2 ^ (t * (j + 1))), f n)) :
    Summable f := by
  let b : ℕ → ℕ := fun j => 2 ^ (t * j)
  let F : ℕ → ℝ := fun j => ∑ n ∈ Ico (b j) (b (j + 1)), f n
  have hF : ∀ j, 0 ≤ F j := fun j => sum_nonneg (fun n _ => hf n)
  have hmono : ∀ j, b j ≤ b (j + 1) := fun j =>
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left t (Nat.le_succ j))
  have heq : ∀ j, (∑ n ∈ range (b j), f n) =
      (∑ n ∈ range (b 0), f n) + ∑ i ∈ range j, F i := by
    intro j
    induction j with
    | zero => simp only [range_zero, sum_empty, add_zero]
    | succ j ih =>
      rw [← sum_range_add_sum_Ico f (hmono j), ih, sum_range_succ]
      exact add_assoc _ _ _
  apply summable_of_sum_range_le hf
    (c := (∑ n ∈ range (b 0), f n) + ∑' j, F j)
  intro N
  have hNb : N ≤ b N := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
  calc
    (∑ n ∈ range N, f n) ≤ ∑ n ∈ range (b N), f n :=
      sum_le_sum_of_subset_of_nonneg (range_mono hNb) (fun n _ _ => hf n)
    _ = _ := heq N
    _ ≤ _ := _root_.add_le_add le_rfl
      (Summable.sum_le_tsum _ (fun j _ => hF j) H)

lemma eventually_weighted_g_le_div_log_cube (R : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) * (Nat.log 2 n : ℝ) ^ R ≤
        (4 * totientRatioAverageConstant + 4) * n / (Nat.log 2 n : ℝ) ^ 3 := by
  filter_upwards [eventually_g_le_div_log_pow (R + 3) (by omega),
    eventually_ge_atTop 2] with n hn hn2
  have hL1 : 1 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by decide) (by simpa using hn2)
  have hL : (0 : ℝ) < Nat.log 2 n := by exact_mod_cast hL1
  apply (le_div_iff₀ (pow_pos hL 3)).mpr
  have hh := (le_div_iff₀ (pow_pos hL (R + 3))).mp hn
  calc
    (g n : ℝ) * (Nat.log 2 n : ℝ) ^ R * (Nat.log 2 n : ℝ) ^ 3 =
        (g n : ℝ) * (Nat.log 2 n : ℝ) ^ (R + 3) := by rw [pow_add]; ring
    _ ≤ _ := hh

lemma summable_weighted_g_at_totient (R : ℕ) :
    Summable (fun m : ℕ =>
      (g (Nat.totient m) : ℝ) * (Nat.log 2 (Nat.totient m) : ℝ) ^ R /
        (Nat.totient m : ℝ) ^ 2) := by
  let C : ℝ := totientRatioAverageConstant
  let K : ℝ := 4 * C + 4
  let f : ℕ → ℝ := fun m =>
    (g (Nat.totient m) : ℝ) * (Nat.log 2 (Nat.totient m) : ℝ) ^ R /
      (Nat.totient m : ℝ) ^ 2
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hf : ∀ m, 0 ≤ f m := fun m => by dsimp [f]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_weighted_g_le_div_log_cube R)
  apply summable_of_summable_geometric_blocks f hf 4 (by decide)
  have Hseries : Summable (fun j : ℕ => 10 * K * C * ((j : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).mul_left (10 * K * C)
  apply Hseries.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max 3 N)] with j hj
  have hj3 : 3 ≤ j := (le_max_left _ _).trans hj
  have hjN : N ≤ j := (le_max_right _ _).trans hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  let B := Ico (2 ^ (4 * j)) (2 ^ (4 * (j + 1)))
  have hpoint (m : ℕ) (hm : m ∈ B) :
      f m ≤ (K / (j : ℝ) ^ 3) * (1 / (Nat.totient m : ℝ)) := by
    have hφj := totient_ge_two_pow_of_input_ge j m hj3 (mem_Ico.mp hm).1
    have hjφ : j ≤ Nat.totient m := Nat.lt_two_pow_self.le.trans hφj
    have hφN : N ≤ Nat.totient m := hjN.trans hjφ
    have hφR : (0 : ℝ) < Nat.totient m := by
      exact_mod_cast (show 0 < Nat.totient m from (by omega : 0 < j).trans_le hjφ)
    have hjL : (j : ℝ) ≤ Nat.log 2 (Nat.totient m) := by
      exact_mod_cast Nat.le_log_of_pow_le (by decide : 1 < 2) hφj
    have hh := hN (Nat.totient m) hφN
    have hden : K * (Nat.totient m : ℝ) / (Nat.log 2 (Nat.totient m) : ℝ) ^ 3 ≤
        K * (Nat.totient m : ℝ) / (j : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (mul_nonneg hK hφR.le) (pow_pos hjR 3)
        (pow_le_pow_left₀ hjR.le hjL 3)
    change _ ≤ K * (Nat.totient m : ℝ) / (Nat.log 2 (Nat.totient m) : ℝ) ^ 3 at hh
    calc
      f m ≤ (K * (Nat.totient m : ℝ) / (j : ℝ) ^ 3) / (Nat.totient m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (hh.trans hden) (sq_nonneg _)
      _ = _ := by field_simp
  have hB : B ⊆ Icc 1 (2 ^ (4 * (j + 1))) := by
    intro m hm
    have hh := mem_Ico.mp hm
    exact mem_Icc.mpr ⟨(Nat.one_le_pow _ _ (by decide : 0 < 2)).trans hh.1, hh.2.le⟩
  have hrecip : (∑ m ∈ B, 1 / (Nat.totient m : ℝ)) ≤ C * (10 * (j : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 (2 ^ (4 * (j + 1))), 1 / (Nat.totient m : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hB (fun m _ _ => by positivity)
      _ ≤ C * (harmonic (2 ^ (4 * (j + 1))) : ℝ) := sum_reciprocal_totient_le_harmonic _
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_fourfold_block_upper j (by omega)) hC
  rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun m _ => hf m))]
  calc
    (∑ m ∈ B, f m) ≤ ∑ m ∈ B, (K / (j : ℝ) ^ 3) * (1 / (Nat.totient m : ℝ)) :=
      sum_le_sum hpoint
    _ = (K / (j : ℝ) ^ 3) * ∑ m ∈ B, 1 / (Nat.totient m : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ (K / (j : ℝ) ^ 3) * (C * (10 * (j : ℝ))) :=
      mul_le_mul_of_nonneg_left hrecip (div_nonneg hK (pow_nonneg hjR.le 3))
    _ = 10 * K * C * ((j : ℝ) ^ 2)⁻¹ := by field_simp

/-- Every fixed logarithmic weight is allowed at the collision endpoint.
This does not move the power exponent to any value below one. -/
theorem summable_inverse_totient_endpoint_log_moment (R : ℕ) :
    Summable (fun n : ℕ =>
      (g n : ℝ) ^ 2 * (Nat.log 2 n : ℝ) ^ R / (n : ℝ) ^ 2) := by
  have H := (summable_totient_weight_iff
    (fun n => (g n : ℝ) * (Nat.log 2 n : ℝ) ^ R / (n : ℝ) ^ 2)
    (fun n => by positivity)).mp (summable_weighted_g_at_totient R)
  exact H.congr (fun n => by ring)

theorem summable_inverse_totient_second_moment_endpoint :
    Summable (fun n : ℕ => (g n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * (1 : ℝ)))) := by
  apply (summable_inverse_totient_endpoint_log_moment 0).congr
  intro n
  rw [pow_zero, mul_one, mul_one, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [Real.rpow_two, div_eq_mul_inv]

end Erdos821

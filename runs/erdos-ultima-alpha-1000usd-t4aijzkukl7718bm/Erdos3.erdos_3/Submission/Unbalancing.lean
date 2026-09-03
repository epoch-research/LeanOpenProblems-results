import Submission.CorrelationMoments

/-! A finite moment unbalancing lemma. These are auxiliary results only. -/
namespace Erdos3Unbalancing
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

lemma pow_le_choose_mul (r p : ℕ) : r^p ≤ (r*p).choose p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, Nat.mul_succ, Nat.add_choose_eq]
    calc
      r^p*r ≤ (r*p).choose p * r := Nat.mul_le_mul_right _ ih
      _ = (r*p).choose p * r.choose 1 := by simp
      _ ≤ ∑ ij ∈ antidiagonal (p+1), (r*p).choose ij.1 * r.choose ij.2 :=
        single_le_sum (f := fun ij : ℕ × ℕ ↦ (r*p).choose ij.1 * r.choose ij.2) (s := antidiagonal (p+1)) (a := (p,1)) (fun _ _ ↦ Nat.zero_le _)  (by simp)

lemma unbalance {X : Type*} [Fintype X] (g : X → ℝ)
    {p r : ℕ} (hr : 0 < r) {e : ℝ} (he : 0 ≤ e)
    (hp : e^p ≤ 𝔼 x, (g x)^p)
    (hg : ∀ j ≤ r*p, 0 ≤ 𝔼 x, (g x)^j) :
    ((r : ℝ)*e)^p ≤ 𝔼 x, (1+g x)^(r*p) := by
  have hpr : p ≤ r*p := by nlinarith
  have hchoose : (r : ℝ)^p ≤ ((r*p).choose p : ℝ) := by
    exact_mod_cast pow_le_choose_mul r p
  have hexpand : (𝔼 x, (1+g x)^(r*p)) =
      ∑ j ∈ range (r*p+1), (𝔼 x, (g x)^j) * ((r*p).choose j : ℝ) := by
    simp_rw [add_comm (1 : ℝ), add_pow, one_pow, mul_one]
    rw [expect_sum_comm]
    simp_rw [← expect_mul]
  rw [hexpand, mul_pow]
  calc
    (r : ℝ)^p*e^p ≤ ((r*p).choose p : ℝ)*(𝔼 x, (g x)^p) :=
      mul_le_mul hchoose hp (pow_nonneg he _) (Nat.cast_nonneg _)
    _ = (𝔼 x, (g x)^p)*((r*p).choose p : ℝ) := mul_comm _ _
    _ ≤ _ := single_le_sum (fun j hj ↦ mul_nonneg (hg j (by simpa using hj))
      (Nat.cast_nonneg _)) (mem_range.mpr (by omega))

lemma unbalance_half {X : Type*} [Fintype X] (g : X → ℝ) {p : ℕ}
    (hp : (1/2 : ℝ)^p ≤ 𝔼 x, (g x)^p)
    (hg : ∀ j ≤ 8*p, 0 ≤ 𝔼 x, (g x)^j) :
    (9/8 : ℝ)^(8*p) ≤ 𝔼 x, (1+g x)^(8*p) := by
  have h := unbalance g (r := 8) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1/2) hp hg
  norm_num only [Nat.cast_ofNat, show (8 : ℝ)*(1/2) = 4 by norm_num] at h
  calc
    (9/8 : ℝ)^(8*p) = ((9/8 : ℝ)^8)^p := pow_mul _ _ _
    _ ≤ (4 : ℝ)^p := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ ≤ _ := h

open Erdos3CorrelationMoments

/-- A large centered convolution moment forces a large positive autocorrelation moment. -/
theorem corr_moment_of_conv_center {G : Type*} [AddCommGroup G] [Fintype G]
    (g : G → ℝ) (hg : (𝔼 x, g x) = 1) {p : ℕ}
    (hp : (1/2 : ℝ)^p ≤ |𝔼 x, (conv g x - 1)^p|) :
    (9/8 : ℝ)^(8*p) ≤ 𝔼 x, (corr g x)^(8*p) := by
  have hmoment := hp.trans (abs_conv_center_moment_le_corr g hg p)
  have h := unbalance_half (fun x ↦ corr g x-1) hmoment
    (fun j _ ↦ corr_center_moment_nonneg g hg j)
  simpa only [add_sub_cancel] using h

#print axioms pow_le_choose_mul
#print axioms corr_moment_of_conv_center
end Erdos3Unbalancing

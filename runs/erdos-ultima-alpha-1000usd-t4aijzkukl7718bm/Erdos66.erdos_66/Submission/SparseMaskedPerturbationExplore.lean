import Submission.SquareExponentScheduleExplore
import Submission.PowerExceptionsNoLimitExplore

/-! Stability of power-saving exceptional estimates under a signed
sublogarithmic perturbation away from a sparse prescribed set. -/
namespace Erdos66SparseMaskedPerturbation
open Filter Erdos66SquareExponentSchedule Erdos66PowerExceptionalCounting
open scoped Classical Topology
set_option maxHeartbeats 2500000

lemma sparse_dyadic_power_summable (k : ℕ → ℕ) (hm : StrictMono k)
    (hk : ∀ j, (j+1)^2 ≤ k j) (α : ℝ) (hα : α ≤ 1/2) :
    Summable (fun n : ℕ ↦ if n∈Set.range (fun j ↦ 2^(k j)) then
      1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
  have hinj : Function.Injective (fun j ↦ 2^(k j)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ 2)).comp hm.injective
  apply (hinj.summable_iff (fun n hn ↦ by simp only [if_neg hn])).mp
  have hs := Erdos66SparseGrowthCosts.shifted_pseries_summable 2 (by decide)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 3] with j hj
  simp only [Function.comp_def,if_pos (show 2^(k j)∈Set.range (fun j ↦ 2^(k j)) from ⟨j,rfl⟩),
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((2^(k j) : ℕ)+2)^(1-α : ℝ))]
  have hfour : (j+1)^4 ≤ 2^(k j) := by
    calc
      _ ≤ (2^(j+1))^4 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 4
      _ = 2^((j+1)*4) := by rw [pow_mul]
      _ ≤ 2^((j+1)^2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (hk j)
  apply one_div_le_one_div_of_le (by positivity)
  have hp : (1 : ℝ) ≤ (2^(k j) : ℕ)+2 := by have := Nat.cast_nonneg (α := ℝ) (2^(k j)); linarith
  have hh := Real.rpow_le_rpow_of_exponent_le hp (show (1 : ℝ)/2 ≤ 1-α by linarith)
  rw [←Real.sqrt_eq_rpow] at hh
  refine le_trans ?_ hh
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have hf : ((j : ℝ)+1)^4 ≤ (2^(k j) : ℕ) := by exact_mod_cast hfour
  nlinarith

/-- The perturbation may have either sign. No insertion, packet, or
independence assumption is used in this transfer. -/
theorem power_exception_transfer (f g : ℕ → ℝ) (S : Set ℕ) (c : ℝ)
    (hchange : Tendsto (fun n ↦ if n∈S then 0 else g n-f n) atTop (𝓝 0))
    (hS : ∀ α : ℝ, α ≤ 1/2 → Summable (fun n : ℕ ↦ if n∈S then
      1/((n : ℝ)+2)^(1-α : ℝ) else 0))
    (hf : ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε ≤ |f n-c| then 1/((n : ℝ)+2)^(1-α : ℝ) else 0)) :
    ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε ≤ |g n-c| then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
  intro ε hε
  obtain ⟨β,hβ,_,hβsum⟩ := hf (ε/2) (by positivity)
  let α := min β (1/2)
  have hα : 0<α := lt_min hβ (by norm_num)
  have hαhalf : α ≤ 1/2 := min_le_right _ _
  have hsmall : Summable (fun n : ℕ ↦ if ε/2 ≤ |f n-c| then
      1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
    apply hβsum.of_norm_bounded
    intro n
    by_cases hn : ε/2 ≤ |f n-c|
    · simp only [if_pos hn,Real.norm_eq_abs,abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 1/((n : ℝ)+2)^(1-α : ℝ))]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
      exact Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        (by have := min_le_left β (1/2); linarith)
    · simp only [if_neg hn,norm_zero,le_refl]
  refine ⟨α,hα,hαhalf.trans_lt (by norm_num),?_⟩
  apply (hsmall.add (hS α hαhalf)).of_norm_bounded_eventually_nat
  have hnorm := hchange.norm
  simp only [norm_zero] at hnorm
  have hclose := hnorm.eventually_lt_const (show (0 : ℝ)<ε/4 by positivity)
  filter_upwards [hclose] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by split_ifs <;> positivity)]
  by_cases hg : ε ≤ |g n-c|
  · rw [if_pos hg]
    by_cases hns : n∈S
    · rw [if_pos hns]
      have hh : 0 ≤ (if ε/2 ≤ |f n-c| then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
        split_ifs <;> positivity
      linarith
    · have hbad : ε/2 ≤ |f n-c| := by
        rw [if_neg hns,Real.norm_eq_abs] at hn
        have ht := abs_sub_le (g n) (f n) c
        linarith
      simp only [if_pos hbad,if_neg hns,add_zero,le_refl]
  · rw [if_neg hg]
    positivity

end Erdos66SparseMaskedPerturbation

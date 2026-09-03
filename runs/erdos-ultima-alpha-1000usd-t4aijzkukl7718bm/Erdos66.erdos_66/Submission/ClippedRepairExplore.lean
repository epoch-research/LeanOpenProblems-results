import Submission.GlobalRepairExplore

/-! Clipping one repaired count to the desired logarithmic profile, without
overshooting an already larger count. -/
namespace Erdos66ClippedRepair
open Filter AdditiveCombinatorics Erdos66GlobalRepair
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def logScale (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)

lemma logScale_pos (n : ℕ) : 0 < logScale n := by
  apply Real.log_pos
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

lemma logScale_atTop : Tendsto logScale atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact tendsto_atTop_mono (fun n ↦ by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    (tendsto_natCast_atTop_atTop (R := ℝ))

lemma logScale_le_double {n : ℕ} (hn : 2 ≤ n) : logScale n ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have harg : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hh := Real.log_le_log (show (0 : ℝ) < n + 2 by positivity) harg
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

noncomputable def correction (r t : ℝ) : ℕ := ⌊max 0 ((t - r) / 2)⌋₊

lemma correction_bounds (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (correction r t : ℝ) ≤ t / 2 ∧
      t - 2 < r + 2 * correction r t ∧
      r + 2 * correction r t ≤ max r t := by
  by_cases htr : t ≤ r
  · have hzero : correction r t = 0 := by
      dsimp [correction]
      rw [max_eq_left (by linarith), Nat.floor_zero]
    rw [hzero, Nat.cast_zero, mul_zero, add_zero, max_eq_left htr]
    constructor
    · positivity
    · constructor <;> linarith
  · have hrt : r ≤ t := by linarith
    have hd : 0 ≤ (t - r) / 2 := by linarith
    have hfloor := Nat.floor_le hd
    have hlt := Nat.lt_floor_add_one ((t - r) / 2)
    dsimp [correction]
    rw [max_eq_right hd, max_eq_right hrt]
    constructor
    · linarith
    · constructor <;> linarith

/-- All sufficiently large one-target repairs can be clipped just below the
requested profile. This estimate is compatible with monotone iteration. -/
theorem eventually_clipped_repair (c ε K C : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Set ℕ,
      (∀ z : ℕ, (sumRep A z : ℝ) ≤ K + C * logScale z) →
      ∃ F : Finset ℕ,
        (∀ a ∈ F, n ≤ 4 * a ∧ a ≤ n) ∧
        c * logScale n - 2 < (sumRep (A ∪ (F : Set ℕ)) n : ℝ) ∧
        (sumRep (A ∪ (F : Set ℕ)) n : ℝ) ≤ max (sumRep A n : ℝ) (c * logScale n) ∧
        ∀ z : ℕ, z ≠ n →
          (sumRep (A ∪ (F : Set ℕ)) z : ℝ) - sumRep A z ≤ ε * logScale z := by
  filter_upwards [eventually_global_repair c ε K C hc.le hε hK hC,
    eventually_ge_atTop 2] with n hn hn2
  intro A hA
  let m := correction (sumRep A n : ℝ) (c * logScale n)
  have hb := correction_bounds (sumRep A n : ℝ) (c * logScale n)
    (Nat.cast_nonneg _) (mul_nonneg hc.le (logScale_pos n).le)
  have hm : (m : ℝ) ≤ c * Real.log n := by
    have hh := mul_le_mul_of_nonneg_left (logScale_le_double hn2) hc.le
    dsimp [m]
    linarith [hb.1]
  obtain ⟨F, hcard, hdis, hsupport, heq, hother⟩ := hn A hA m hm
  refine ⟨F, hsupport, ?_, ?_, fun z hz ↦ (hother z hz).2⟩
  · rw [heq]
    push_cast
    exact hb.2.1
  · rw [heq]
    push_cast
    exact hb.2.2

end Erdos66ClippedRepair

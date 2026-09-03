import Submission.ExponentialProfileParametersExplore

/-! Elementary logarithmic geometry for power-length finite annuli. -/
namespace Erdos66PowerAnnulusGeometry
open scoped Classical
set_option maxHeartbeats 800000

lemma geometry (M q₀ L : ℕ) (a : ℝ) (hM : 2 ≤ M) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hstart : (q₀ : ℝ) + 3 ≤ Real.exp (a * Real.log M / 4))
    (hend : Real.exp (a * Real.log M / 2) ≤ (L : ℝ))
    (n : ℕ) (hn : M * (q₀ + 3) ≤ n)
    (hnpow : (n : ℝ) ≤ (M * (q₀ + 3) : ℕ) ^ (1 + a / 8 : ℝ)) :
    n ≤ M * L ∧ Real.log M ≤ Real.log n ∧
      Real.log n ≤ (1 + a / 2) * Real.log M := by
  let N := M * (q₀ + 3)
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hMN : M ≤ N := by dsimp [N]; nlinarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnM : M ≤ n := hMN.trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs := Real.log_le_log (show 0 < (q₀ : ℝ) + 3 by positivity) hstart
  rw [Real.log_exp] at hs
  have hlogN : Real.log N ≤ (1 + a / 4) * Real.log M := by
    dsimp [N]
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Real.log_mul hMpos.ne' (by positivity)]
    linarith
  have hlogn : Real.log n ≤ (1 + a / 2) * Real.log M := by
    have hh := Real.log_le_log hnpos hnpow
    rw [Real.log_rpow hNpos] at hh
    have hbound := mul_le_mul_of_nonneg_left hlogN (show 0 ≤ 1 + a / 8 by positivity)
    have hsq : a ^ 2 ≤ a := by nlinarith
    have hsq' := mul_le_mul_of_nonneg_right hsq hlogM.le
    nlinarith
  have hnl : n ≤ M * L := by
    have hh := Real.exp_le_exp.mpr hlogn
    have he : Real.exp ((1 + a / 2) * Real.log M) = (M : ℝ) * Real.exp (a * Real.log M / 2) := by
      rw [show (1 + a / 2) * Real.log M = Real.log M + a * Real.log M / 2 by ring,
        Real.exp_add, Real.exp_log hMpos]
    rw [Real.exp_log hnpos, he] at hh
    have hmul := mul_le_mul_of_nonneg_left hend hMpos.le
    exact_mod_cast hh.trans hmul
  exact ⟨hnl, Real.log_le_log hMpos (by exact_mod_cast hnM), hlogn⟩

end Erdos66PowerAnnulusGeometry

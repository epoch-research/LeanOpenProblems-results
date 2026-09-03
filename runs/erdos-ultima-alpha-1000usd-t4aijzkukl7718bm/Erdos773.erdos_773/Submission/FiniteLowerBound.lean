import FormalConjecturesUtil
import Submission.LowerBound
import Submission.AverageCollisionBound
import Submission.AverageAPBound

/-! An explicit finite lower bound. This does not settle Erdős 773. -/
namespace Erdos773
set_option maxHeartbeats 1000000

lemma square_sidon_finite_log_lower (N : ℕ) (hN : 32 ≤ N) :
    (N : ℝ) / (8 * ((N : ℝ) * (1 + Real.log (4 * N))) ^ (1 / 3 : ℝ)) ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  let L : ℝ := 1 + Real.log (4 * N)
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 4 * N by linarith)
    dsimp [L]
    linarith
  have hLupper : L ≤ 4 * N := by
    have hh := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 * N by positivity)
    dsimp [L]
    linarith
  have hNL : (1 : ℝ) ≤ N * L := by nlinarith
  let R : ℝ := ((N : ℝ) * L) ^ (1 / 3 : ℝ)
  have hR1 : 1 ≤ R := Real.one_le_rpow hNL (by norm_num)
  have hR : 0 < R := by linarith
  have hR3 : R ^ 3 = (N : ℝ) * L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N * L)]
    norm_num
  have hRupper : R ≤ N / 2 := by
    have hc : R ^ 3 ≤ ((N : ℝ) / 2) ^ 3 := by
      rw [hR3]
      have hh := mul_le_mul_of_nonneg_left hLupper hN0.le
      have hhh := mul_le_mul_of_nonneg_right hN32 (sq_nonneg (N:ℝ))
      nlinarith only [hh,hhh]
    exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) hc
  have hAP : ((squareAPs N).card : ℝ) ≤ 8 * R ^ 3 := by
    rw [hR3]
    have hh := AverageAP.squareAPs_log_bound N
    dsimp [L]
    nlinarith only [hh]
  have hE : ((squareCollisions N).card : ℝ) ≤ 8 * N * R ^ 3 := by
    have hh := AverageCollision.squareCollisions_log_bound N
    have hlog : Real.log (2 * N) ≤ Real.log (4 * N) :=
      Real.log_le_log (by positivity) (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hlog (show (0:ℝ) ≤ 8 * N ^ 2 by positivity)
    rw [hR3]
    dsimp [L]
    nlinarith only [hh,hmul]
  let p : ℝ := 1 / (4 * R)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; apply (div_le_one (by positivity)).mpr; linarith
  have hpr : p * R = 1 / 4 := by dsimp [p]; field_simp
  have hpN : 1 / 2 ≤ p * N := by
    have hh := mul_le_mul_of_nonneg_left hRupper hp
    nlinarith only [hh,hpr]
  have h3 : p ^ 3 * (squareAPs N).card ≤ 1 / 8 := by
    calc
      _ ≤ p ^ 3 * (8 * R ^ 3) :=
        mul_le_mul_of_nonneg_left hAP (pow_nonneg hp _)
      _ = 8 * (p * R) ^ 3 := by ring
      _ = _ := by rw [hpr]; norm_num
  have h4 : p ^ 4 * (squareCollisions N).card ≤ p * N / 8 := by
    calc
      _ ≤ p ^ 4 * (8 * N * R ^ 3) :=
        mul_le_mul_of_nonneg_left hE (pow_nonneg hp _)
      _ = 8 * p * N * (p * R) ^ 3 := by ring
      _ = _ := by rw [hpr]; ring
  have hb := square_sidon_alteration N p hp hp1
  have ht : (N : ℝ) / (8 * R) = p * N / 2 := by
    dsimp [p]
    ring
  change (N : ℝ) / (8 * R) ≤ _
  rw [ht]
  nlinarith only [hb,h3,h4,hpN]

#print axioms square_sidon_finite_log_lower
end Erdos773

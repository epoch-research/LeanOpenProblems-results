import FormalConjecturesUtil
import Submission.LowerBound
import Submission.AverageCollisionBound

/-! A quantitative version of the two-thirds lower bound.
This does not prove Erdős 773. -/
namespace Erdos773
open Filter
set_option maxHeartbeats 1000000

lemma square_sidon_log_lower_aux (N : ℕ) (hN : 1 ≤ N) (C : ℝ)
    (hAP : ((squareAPs N).card : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ))
    (hC : C ≤ (N : ℝ) ^ (1 / 6 : ℝ)) :
    (N : ℝ) / (8 * ((N : ℝ) * (1 + Real.log (2 * N))) ^ (1 / 3 : ℝ)) ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  let L : ℝ := 1 + Real.log (2 * N)
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2 * N by linarith)
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
  have hR2 : (N : ℝ) ^ (2 / 3 : ℝ) ≤ R ^ 2 := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N * L)]
    norm_num
    exact Real.rpow_le_rpow hN0.le (by nlinarith) (by norm_num)
  have hCN : C * (N : ℝ) ^ (1 / 2 : ℝ) ≤ R ^ 2 := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ ≤ _ := hR2
  have hAP' : ((squareAPs N).card : ℝ) ≤ (N : ℝ) * R ^ 2 := by
    calc
      _ ≤ C * (N : ℝ) ^ (3 / 2 : ℝ) := hAP
      _ = (N : ℝ) * (C * (N : ℝ) ^ (1 / 2 : ℝ)) := by
        have he : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
        rw [he, Real.rpow_add hN0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCN hN0.le
  have hE : ((squareCollisions N).card : ℝ) ≤ 8 * N * R ^ 3 := by
    rw [hR3]
    have hh := AverageCollision.squareCollisions_log_bound N
    dsimp [L]
    nlinarith only [hh]
  let p : ℝ := 1 / (4 * R)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; apply (div_le_one (by positivity)).mpr; linarith
  have hpr : p * R = 1 / 4 := by dsimp [p]; field_simp
  have h3 : p ^ 3 * (squareAPs N).card ≤ p * N / 16 := by
    calc
      _ ≤ p ^ 3 * ((N : ℝ) * R ^ 2) :=
        mul_le_mul_of_nonneg_left hAP' (pow_nonneg hp _)
      _ = p * N * (p * R) ^ 2 := by ring
      _ = _ := by rw [hpr]; ring
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
  nlinarith [mul_nonneg hp hN0.le]

lemma square_sidon_logarithmic_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (8 * ((N : ℝ) * (1 + Real.log (2 * N))) ^ (1 / 3 : ℝ)) ≤
        (Finset.maxSidonSubsetCard
          ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) := by
  obtain ⟨C, hC0, hAP⟩ := squareAPs_subpower (1 / 4) (by norm_num)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, ht.eventually (eventually_ge_atTop C)] with N hN hC
  apply square_sidon_log_lower_aux N hN C
  · convert hAP N using 1 <;> norm_num
  · exact hC

#print axioms square_sidon_logarithmic_lower
end Erdos773

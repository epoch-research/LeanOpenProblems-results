import Submission.BuchstabArbitraryGrowth
import Submission.PowerExposureBudget

/-! Exposure envelopes from every exponent strictly above two. These bounds
are unconditional, but the limiting quadratic endpoint is not asserted. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000

/-- An integral power envelope with any strict gap above the square absorbs
both the near-quadratic constant and a fixed dilation factor. -/
theorem eventually_near_quadratic_power_envelope (a b : ℕ) (ha : 0 < a)
    (hab : 2*a < b) :
    ∀ᶠ t : ℕ in atTop,
      (jacobsthalFunction (t^a) : ℝ) ≤ (t : ℝ)^b/(2 : ℝ)^b := by
  let ε : ℝ := 1/((a : ℝ)+1)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hε : 0 < ε := by dsimp [ε]; positivity
  have haε : (a : ℝ)*ε < 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have habR : 2*(a : ℝ)+1 ≤ b := by exact_mod_cast hab
  let γ : ℝ := (b : ℝ)-(a : ℝ)*(2+ε)
  have hγ : 0 < γ := by dsimp only [γ]; nlinarith only [haε,habR]
  obtain ⟨C,hC,hbound⟩ := RecursiveSieve.Buchstab.exists_near_quadratic_bound ε hε
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop (C*(2 : ℝ)^b)))
  filter_upwards [hs,eventually_ge_atTop 1] with t ht ht1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hj := hbound (t^a) (Nat.pow_pos (by omega))
  have hp : (((t^a : ℕ) : ℝ))^(2+ε) = (t : ℝ)^((a : ℝ)*(2+ε)) := by
    rw [Nat.cast_pow,← rpow_natCast (t : ℝ) a,← rpow_mul ht0.le]
  rw [hp] at hj
  have hh := mul_le_mul_of_nonneg_right ht
    (rpow_nonneg ht0.le ((a : ℝ)*(2+ε)))
  have he : (t : ℝ)^γ*(t : ℝ)^((a : ℝ)*(2+ε)) = (t : ℝ)^b := by
    rw [← rpow_add ht0,show γ+(a : ℝ)*(2+ε)=(b : ℝ) by dsimp [γ]; ring,rpow_natCast]
  rw [he] at hh
  apply hj.trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^b)).mpr
  nlinarith only [hh]

/-- Generalized exposure budget: the only exponent restriction is 2a<b. -/
theorem eventually_subsquare_exposure_budget (a b : ℕ) (ha : 0 < a)
    (hab : 2*a < b) :
    ∀ᶠ t : ℕ in atTop, ∀ k : ℕ, t^b ≤ 2^b*k →
      IsJacobsthalBound (t^a-1) k := by
  filter_upwards [eventually_near_quadratic_power_envelope a b ha hab] with t ht
  intro k hk
  have hkR : (t : ℝ)^b ≤ (2 : ℝ)^b*k := by exact_mod_cast hk
  have hle : (jacobsthalFunction (t^a) : ℝ) ≤ k := ht.trans
    ((div_le_iff₀ (by positivity : (0 : ℝ) < 2^b)).mpr (by simpa only [mul_comm] using hkR))
  have hb := (jacobsthalFunction_le_iff (t^a) k).mp (by exact_mod_cast hle)
  intro n hn hnk r
  exact hb n hn (hnk.trans (Nat.sub_le _ _)) r

#print axioms eventually_subsquare_exposure_budget
end Erdos970.GapAverages

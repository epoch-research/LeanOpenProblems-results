import Submission.RepairParametersExplore

/-! The added cell-collision cost in a predecessor repair is small at a
linear window scale. This is a one-target parameter estimate. -/
namespace Erdos66PredecessorRepairParameters
open Filter Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 1800000

lemma absorb_cell_cost (D G B : ℝ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (N m H : ℕ) (hm : (m : ℝ) ≤ D*Real.log N) (hH : (H : ℝ) ≤ G*Real.sqrt N) :
    (m : ℝ)^4+4*m^2*H+m*(B*Real.sqrt N*Real.log N) ≤
      m^4+m*((B+4*D*G)*Real.sqrt N*Real.log N) := by
  have hh := mul_le_mul_of_nonneg_left hH (show (0 : ℝ) ≤ 4*(m : ℝ)^2 by positivity)
  have hh' := mul_le_mul_of_nonneg_left hm
    (show (0 : ℝ) ≤ 4*(m : ℝ)*G*Real.sqrt N by positivity)
  nlinarith only [hh, hh']

/-- Square-root cell sizes add only another constant to the coarse
sqrt(N) log(N) selection budget. -/
theorem eventually_predecessor_selection_small (D G B ε : ℝ)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 ≤ B) (hε : 0 < ε) (h : ℕ) :
    let t : ℝ := 32*((h : ℝ)+1)/ε
    0 < t ∧ ∀ᶠ N : ℕ in atTop, ∀ L m H : ℕ,
      (N : ℝ)/24 ≤ L → (m : ℝ) ≤ D*Real.log N → (H : ℝ) ≤ G*Real.sqrt N →
      ((m : ℝ)^4+4*m^2*H+m*(B*Real.sqrt N*Real.log N))/L +
        ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*Real.exp t*(B*Real.sqrt N*Real.log N)/L -
          t*(ε*Real.log N/16)) < 1 := by
  dsimp only
  let t : ℝ := 32*((h : ℝ)+1)/ε
  have hB' : 0 ≤ B+4*D*G := by positivity
  obtain ⟨ht, hparams⟩ := eventually_selection_small D (B+4*D*G) ε hD hB' hε h
  refine ⟨ht, ?_⟩
  filter_upwards [eventually_ge_atTop 2, hparams] with N hN hp
  intro L m H hL hm hH
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hcost := div_le_div_of_nonneg_right (absorb_cell_cost D G B hD hG hB N m H hm hH)
    (Nat.cast_nonneg (α := ℝ) L)
  have hBB : B*Real.sqrt N*Real.log N ≤ (B+4*D*G)*Real.sqrt N*Real.log N := by
    have hh : B ≤ B+4*D*G := by
      have hnon : 0 ≤ 4*D*G := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)) hlog
  have hmean := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBB (show (0 : ℝ) ≤ (m : ℝ)*Real.exp t by positivity))
    (Nat.cast_nonneg (α := ℝ) L)
  have he := Real.exp_le_exp.mpr (sub_le_sub_right hmean (t*(ε*Real.log N/16)))
  have hexp := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ (N : ℝ)^h+1 by positivity)
  have hh := hp L m hL hm
  change _ + ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*Real.exp t*(B*Real.sqrt N*Real.log N)/L -
    t*(ε*Real.log N/16)) < 1
  linarith

end Erdos66PredecessorRepairParameters

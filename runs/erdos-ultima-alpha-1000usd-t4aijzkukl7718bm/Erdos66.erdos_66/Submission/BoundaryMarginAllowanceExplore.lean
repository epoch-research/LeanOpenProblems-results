import Submission.ExactBracketHostClippingExplore

/-! Boundary coefficients can absorb any fixed additive allowance. -/
namespace Erdos66BoundaryMarginAllowance
open Filter AdditiveCombinatorics Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66TripleIntersectionMean Erdos66BoundaryLogarithmicClipping
open scoped Classical Topology
set_option maxHeartbeats 2200000

lemma eventually_boundary_allowance (A : Set ℕ) (NB : ℕ → ℕ)
    (hA : ∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤
      20*Real.log ((n:ℝ)+1)) (c : ℝ) (hc : 0<c) (M : ℕ) :
    ∃ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      2*(boundary B (cutoff j) n).card+M ≤ ⌊c*Real.log (n:ℝ)⌋₊ := by
  let j := ⌈240/c⌉₊
  have hj : 240 ≤ c*((j:ℝ)+1) := by
    have hh : 240/c ≤ (j:ℝ) := Nat.le_ceil _
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh',hc]
  have ht : (0:ℝ) < (j:ℝ)+1 := by positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨j,?_⟩
  filter_upwards [eventually_ge_atTop (NB j),eventually_ge_atTop 1,
    hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (2*(M : ℝ)/c)] with n hN hn hlog1 hlogc
  intro B hBA
  have hmono : ((boundary B (cutoff j) n).card:ℝ) ≤ (boundary A (cutoff j) n).card :=
    by exact_mod_cast Finset.card_le_card (boundary_mono hBA (cutoff j) n)
  have hB0 := (mul_le_mul_of_nonneg_left hmono ht.le).trans (hA j n hN)
  have hB : ((j:ℝ)+1)*((boundary B (cutoff j) n).card:ℝ) ≤ 20*ell n := by
    dsimp only [ell]
    linarith only [hB0]
  have hell := ell_le_three_log hn hlog1
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hscale := mul_le_mul_of_nonneg_right hj hlog0
  have hsmall : 2*((boundary B (cutoff j) n).card:ℝ) ≤ c/2*Real.log (n:ℝ) := by
    apply le_of_mul_le_mul_left (a := (j:ℝ)+1) _ ht
    nlinarith only [hB,hell,hscale]
  have hlarge : 2*(M : ℝ) ≤ c*Real.log (n:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlogc
  apply Nat.le_floor
  push_cast
  nlinarith only [hsmall,hlarge]


end Erdos66BoundaryMarginAllowance

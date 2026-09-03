import Submission.PrefixCopyExplore

/-! A necessary mass restriction between a cutoff N and its square.
It rules out a particular full-lift amplification, not the original conjecture. -/
namespace Erdos66QuadraticPrefixMass
open Erdos66Counting Erdos66TauberianProfile Erdos66Explore
open Filter AdditiveCombinatorics
open scoped Topology
set_option maxHeartbeats 1600000

/-- A hypothetical logarithmic-limit witness cannot amplify the entire old
prefix by a factor N-1 by the squared cutoff. -/
theorem eventual_no_linear_mass_amplification {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N in atTop, count A (N^2)<(N-1)*count A N := by
  have hq : 0<4*c/Real.pi := by have := limit_pos hc ht; positivity
  have hp := witness_counting_square_profile hc ht
  have hNtop : Tendsto (fun N : ℕ ↦ N^2) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ by
      change N ≤ N^2
      have : N = 0 ∨ 1 ≤ N := by omega
      rcases this with rfl | h
      · simp
      · nlinarith) tendsto_id
  have hlo := hp.eventually (lt_mem_nhds (show (4*c/Real.pi)/2<4*c/Real.pi by linarith))
  have hhi := (hp.comp hNtop).eventually (gt_mem_nhds (show 4*c/Real.pi<2*(4*c/Real.pi) by linarith))
  filter_upwards [hlo,hhi,eventually_ge_atTop 16] with N hlow hhigh hN
  have hNR : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hlog2 : Real.log (N^2:ℕ)=2*Real.log (N:ℝ) := by rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hden : 0<(N:ℝ)*Real.log N := mul_pos hn0 hlog
  have hden2 : 0<((N^2:ℕ):ℝ)*Real.log (N^2:ℕ) := by rw [hlog2,Nat.cast_pow]; positivity
  have hl := (lt_div_iff₀ hden).mp hlow
  have hh := (div_lt_iff₀ hden2).mp hhigh
  rw [hlog2,Nat.cast_pow] at hh
  by_contra hbad
  have hbad : (N-1)*count A N ≤ count A (N^2) := le_of_not_gt hbad
  have hi : ((N:ℝ)-1)*(count A N:ℝ) ≤ count A (N^2) := by
    have hi' : ((N-1:ℕ):ℝ)*(count A N:ℝ) ≤ count A (N^2) := by exact_mod_cast hbad
    simpa only [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one] using hi'
  have hnm : 0 ≤ (N:ℝ)-1 := by linarith
  have hs := pow_le_pow_left₀ (show 0 ≤ ((N:ℝ)-1)*(count A N:ℝ) by positivity) hi 2
  have hlow' := mul_lt_mul_of_pos_right hl (sq_pos_of_pos (show 0<(N:ℝ)-1 by linarith))
  let d : ℝ := (4*c/Real.pi)/2*((N:ℝ)*Real.log N)
  have hd : 0<d := by dsimp [d]; positivity
  have hcontra : ((N:ℝ)-1)^2*d<8*(N:ℝ)*d := by
    dsimp [d]
    nlinarith only [hlow',hs,hh]
  have hpoly := (mul_lt_mul_iff_left₀ hd).mp hcontra
  nlinarith

end Erdos66QuadraticPrefixMass

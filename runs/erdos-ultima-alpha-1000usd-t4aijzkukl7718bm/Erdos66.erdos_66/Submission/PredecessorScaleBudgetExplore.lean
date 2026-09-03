import Submission.PredecessorCutoffTransferExplore
import Submission.PredecessorRepairParametersExplore

/-! Uniform large-scale budgets for support-localized predecessor repairs. -/
namespace Erdos66PredecessorScaleBudget
open Filter Erdos66PredecessorCutoffTransfer
open scoped Topology Classical
set_option maxHeartbeats 1800000

noncomputable def gapSize (D : ℝ) (N : ℕ) : ℕ :=
  ⌈12*(D+1)*Real.sqrt (N : ℝ)⌉₊

lemma eventually_gap_bounds (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in atTop, 16 ≤ N ∧ 1 ≤ Real.log (N : ℝ) ∧
      gapSize D N ≤ N ∧
      (gapSize D N : ℝ) ≤ (12*(D+1)+1)*Real.sqrt (N : ℝ) ∧
      2*D*Real.sqrt ((16*N : ℕ)+1 : ℕ) < gapSize D N := by
  let G : ℝ := 12*(D+1)+1
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 16, hlog.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (G^2)] with N hN hl hg
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := Real.sq_sqrt hNp.le
  have hsp := Real.sqrt_pos.mpr hNp
  have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  have hGs : G ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hHlo : 12*(D+1)*Real.sqrt (N : ℝ) ≤ gapSize D N := Nat.le_ceil _
  have hHhi : (gapSize D N : ℝ) < 12*(D+1)*Real.sqrt (N : ℝ)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hH : (gapSize D N : ℝ) ≤ G*Real.sqrt (N : ℝ) := by dsimp [G]; nlinarith
  have hHN : gapSize D N ≤ N := by
    have hle : (gapSize D N : ℝ) ≤ N := by nlinarith
    exact_mod_cast hle
  have hs16 := Real.sq_sqrt (show (0 : ℝ) ≤ ((16*N : ℕ)+1 : ℕ) by positivity)
  have hs16n := Real.sqrt_nonneg (((16*N : ℕ)+1 : ℕ) : ℝ)
  have hs16' : Real.sqrt (((16*N : ℕ)+1 : ℕ) : ℝ) ≤ 5*Real.sqrt (N : ℝ) := by
    push_cast at hs16 hs16n ⊢
    nlinarith
  have hlen : 2*D*Real.sqrt (((16*N : ℕ)+1 : ℕ) : ℝ) < gapSize D N := by
    have hh := mul_le_mul_of_nonneg_left hs16' (show (0 : ℝ) ≤ 2*D by positivity)
    nlinarith
  exact ⟨hN,hl,hHN,hH,hlen⟩

lemma polynomial_cutoff_log (N h : ℕ) (hN : 1 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) :
    Real.log (2*((N^h+1 : ℕ) : ℝ)+2) ≤ ((h : ℝ)+6)*Real.log (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (1 : ℝ) ≤ (N : ℝ)^h := one_le_pow₀ (by exact_mod_cast hN)
  have hb : 2*((N^h+1 : ℕ) : ℝ)+2 ≤ 6*(N : ℝ)^h := by push_cast; linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2*((N^h+1 : ℕ) : ℝ)+2) hb
  rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hNp _)), Real.log_pow] at hh
  have h6 : Real.log (6 : ℝ) ≤ 5 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)]
  nlinarith

lemma degree_budget (N H : ℕ) (G B₀ V : ℝ)
    (hN : 0 ≤ (N : ℝ)) (hG : 0 ≤ G) (hB : 1 ≤ B₀) (hlog : 1 ≤ Real.log (N : ℝ))
    (hH : (H : ℝ) ≤ G*Real.sqrt (N : ℝ))
    (hV : V = B₀*Real.log (N : ℝ)) :
    2*Real.sqrt (2*(N : ℝ)*V)+2*H*V ≤
      ((4+2*G)*B₀)*Real.sqrt (N : ℝ)*Real.log (N : ℝ) := by
  have hV1 : 1 ≤ V := by nlinarith
  have hs : Real.sqrt (2*V) ≤ 2*V := by
    have hh := Real.sq_sqrt (show 0 ≤ 2*V by linarith)
    have hn := Real.sqrt_nonneg (2*V)
    nlinarith
  have he : Real.sqrt (2*(N : ℝ)*V) = Real.sqrt (N : ℝ)*Real.sqrt (2*V) := by
    rw [show 2*(N : ℝ)*V=(N : ℝ)*(2*V) by ring,Real.sqrt_mul hN]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (N : ℝ))
  have hh' := mul_le_mul_of_nonneg_right hH (show 0 ≤ V by linarith)
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

lemma finite_profile_envelope (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (AdditiveCombinatorics.sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (N h : ℕ) (hN : 1 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) :
    ∀ z, (AdditiveCombinatorics.sumRep (Erdos66Counting.cutoff A (N^h+1) : Set ℕ) z : ℝ) ≤
      (K+C*((h : ℝ)+6)+1)*Real.log (N : ℝ) := by
  intro z
  have hh := cutoff_envelope A K C hK hC hA (N^h+1) z
  have ht := mul_le_mul_of_nonneg_left (polynomial_cutoff_log N h hN hl) hC
  have hk := mul_le_mul_of_nonneg_left hl hK
  nlinarith

end Erdos66PredecessorScaleBudget

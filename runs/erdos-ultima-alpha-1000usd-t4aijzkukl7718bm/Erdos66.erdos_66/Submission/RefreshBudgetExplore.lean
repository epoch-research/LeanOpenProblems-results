import Submission.RefreshVarianceExplore

/-! A limitation of the displayed independent-refresh tail criterion.
This is NOT a lower bound on all realizations or all dependent repairs. -/
namespace Erdos66RefreshBudget
open scoped Classical
set_option maxHeartbeats 1200000

/-- On a full dyadic window, this particular summed tail must have exponent
strictly greater than one. It cannot be made small merely by moving the window. -/
lemma dyadic_budget_forces_exponent (N : ℕ) (hN : 0<N) (α : ℝ)
    (hbudget : (∑ n∈Finset.Ico N (2*N), 2*Real.exp (-α*Real.log n/8))<1) : 8<α := by
  by_contra hα
  have hα : α ≤ 8 := le_of_not_gt hα
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hterm (n : ℕ) (hn : n∈Finset.Ico N (2*N)) :
      1/(N:ℝ) ≤ 2*Real.exp (-α*Real.log n/8) := by
    have hn := Finset.mem_Ico.mp hn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
    have he : -Real.log (n:ℝ) ≤ -α*Real.log n/8 := by
      nlinarith only [mul_le_mul_of_nonneg_right hα hl]
    have hh := Real.exp_le_exp.mpr he
    rw [Real.exp_neg,Real.exp_log hn0] at hh
    have hnN : (n:ℝ) ≤ 2*N := by exact_mod_cast hn.2.le
    have hi : 1/(N:ℝ) ≤ 2*(n:ℝ)⁻¹ := by
      rw [←one_div]
      field_simp
      nlinarith only [hnN]
    exact hi.trans (mul_le_mul_of_nonneg_left hh (by norm_num))
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico,show 2*N-N=N by omega] at hs
  have he : (N:ℝ)*(1/(N:ℝ))=1 := by field_simp
  rw [he] at hs
  linarith

/-- To make the certified noise smaller than the contraction gain, the
parameters must obey this tradeoff. This concerns the finite union bound only. -/
lemma refresh_budget_tradeoff (N : ℕ) (hN : 0<N) (ε θ b δ : ℝ)
    (hε : 0<ε) (hθ : 0<θ) (hθ1 : θ ≤ 1) (hb : 0<b)
    (hbudget : (∑ n∈Finset.Ico N (2*N),
      2*Real.exp (-ε^2*(θ*b*Real.log n)/8))<1)
    (hnoise : ε*(θ*b)<θ*(2-θ)*δ) : 2*b<θ*δ^2 := by
  have hbudget' : (∑ n∈Finset.Ico N (2*N),
      2*Real.exp (-(ε^2*θ*b)*Real.log n/8))<1 := by
    convert hbudget using 1
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    congr 1
    ring
  have hα := dyadic_budget_forces_exponent N hN (ε^2*θ*b) hbudget'
  have hnoise' : ε*b<(2-θ)*δ := by nlinarith only [hnoise,hθ]
  have hpos : 0 ≤ ε*b := (mul_pos hε hb).le
  have hs : (ε*b)^2<((2-θ)*δ)^2 := by
    nlinarith only [hnoise',hpos,sq_nonneg (ε*b-(2-θ)*δ)]
  have hs' := mul_lt_mul_of_pos_left hs hθ
  have hα' := mul_lt_mul_of_pos_right hα hb
  have hsq : (2-θ)^2 ≤ 4 := by nlinarith [hθ,hθ1]
  have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hθ.le (sq_nonneg δ))
  nlinarith only [hs',hα',hh]

/-- In particular the above certified repair cannot contract arbitrarily
small errors for a fixed positive variance coefficient b. -/
lemma no_small_error_certified_refresh (N : ℕ) (hN : 0<N) (ε θ b δ : ℝ)
    (hε : 0<ε) (hθ : 0<θ) (hθ1 : θ ≤ 1) (hb : 0<b)
    (hsmall : δ^2 ≤ 2*b)
    (hbudget : (∑ n∈Finset.Ico N (2*N),
      2*Real.exp (-ε^2*(θ*b*Real.log n)/8))<1) :
    ¬ε*(θ*b)<θ*(2-θ)*δ := by
  intro hnoise
  have hh := refresh_budget_tradeoff N hN ε θ b δ hε hθ hθ1 hb hbudget hnoise
  have hmul := mul_le_mul_of_nonneg_right hθ1 (sq_nonneg δ)
  nlinarith

end Erdos66RefreshBudget

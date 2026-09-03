import Submission.LogCellWindowBudgetExplore

/-! One insertion potential permits quadratic-logarithmic total demand. -/
namespace Erdos66QuadraticLogWindowBudget
open Filter Erdos66LogCellWindowBudget Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 3500000

theorem eventually_quadratic_log_window_budget (M B ε : ℝ) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (hε : 0<ε) (h : ℕ) :
    let t : ℝ := 20*((h : ℝ)+1)/ε
    0<t ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ M*(Real.log N)^2 →
      (windowSize N : ℝ)/2+2*(2*B*(Real.log N)^5) ≤ windowSize N ∧
      ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*(Real.exp t*(2*B*(Real.log N)^5+m+1)/((windowSize N : ℝ)/2))-
        t*(ε*Real.log N/10))<1 := by
  dsimp only
  let t : ℝ := 20*((h : ℝ)+1)/ε
  let Q : ℝ := 2*Real.exp t*M*(2*B+M+1)
  have ht : 0<t := by dsimp [t]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨ht,?_⟩
  filter_upwards [hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (8*B),
    hlog.eventually_ge_atTop Q,(polynomial_exp_log_limit h).eventually_lt_const (show (0 : ℝ)<1 by norm_num)]
    with N hl hlarge hQle he
  intro m hm
  let L := Real.log (N : ℝ)
  have hL : 1 ≤ L := hl
  have hLp : 0<L := by linarith
  obtain ⟨hw,hlo,hhi⟩ := windowSize_bounds N hl
  have hwp : (0 : ℝ)<windowSize N := by exact_mod_cast hw
  have hp13 : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
  have hp25 : L^2 ≤ L^5 := pow_le_pow_right₀ hL (show 2 ≤ 5 by norm_num)
  have h5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hbound : 2*B*L^5+(m : ℝ)+1 ≤ (2*B+M+1)*L^5 := by
    have hh := mul_le_mul_of_nonneg_left hp25 hM
    change (m : ℝ) ≤ M*L^2 at hm
    nlinarith
  have hnum : (m : ℝ)*(Real.exp t*(2*B*L^5+m+1)) ≤
      Real.exp t*M*(2*B+M+1)*L^7 := by
    have hh := mul_le_mul hm hbound (by positivity) (by positivity : 0 ≤ M*L^2)
    have hhh := mul_le_mul_of_nonneg_left hh (Real.exp_pos t).le
    nlinarith only [hhh]
  have hmean : (m : ℝ)*(Real.exp t*(2*B*L^5+m+1))/((windowSize N : ℝ)/2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hQle (show 0 ≤ L^7 by positivity)
    have heq : L*L^7=L^8 := by ring
    rw [heq] at hh
    apply (div_le_one (by positivity : (0 : ℝ)<(windowSize N : ℝ)/2)).mpr
    dsimp only [Q] at hh
    change L^8 ≤ (windowSize N : ℝ) at hlo
    nlinarith only [hnum,hh,hlo]
  constructor
  · have hB3 : 8*B ≤ L^3 := hlarge.trans hp13
    have hh := mul_le_mul_of_nonneg_right hB3 (show 0 ≤ L^5 by positivity)
    have heq : L^3*L^5=L^8 := by ring
    rw [heq] at hh
    change L^8 ≤ (windowSize N : ℝ) at hlo
    change _+2*(2*B*L^5) ≤ _
    linarith
  · have htilt : t*(ε*Real.log N/10)=2*((h : ℝ)+1)*Real.log N := by
      dsimp only [t]
      field_simp
      ring
    have he' : Real.exp ((m : ℝ)*(Real.exp t*(2*B*(Real.log N)^5+m+1)/((windowSize N : ℝ)/2))-
        t*(ε*Real.log N/10)) ≤ Real.exp (1-2*((h : ℝ)+1)*Real.log N) := by
      apply Real.exp_le_exp.mpr
      rw [htilt]
      simpa only [mul_div_assoc,L] using sub_le_sub_right hmean (2*((h : ℝ)+1)*Real.log N)
    exact (mul_le_mul_of_nonneg_left he' (by positivity : (0 : ℝ) ≤ (N : ℝ)^h+1)).trans_lt he


end Erdos66QuadraticLogWindowBudget

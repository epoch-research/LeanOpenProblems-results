import Submission.RankCellWindowExplore
import Submission.RepairParametersExplore

/-! Polylogarithmic rank-cell windows: long enough for the insertion potential,
yet carrying less than a quarter unit of harmonic profile mass. -/
namespace Erdos66LogCellWindowBudget
open Filter Erdos66Fractional Erdos66FractionalFourthPower Erdos66RepairParameters
open scoped Topology
set_option maxHeartbeats 3500000

noncomputable def windowSize (N : ℕ) : ℕ := ⌈(Real.log (N : ℝ))^8⌉₊

lemma log_power_sqrt_decay (r : ℕ) :
    Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ))^r/Real.sqrt N) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (r : ℝ) (show (0 : ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_natCast,←Real.sqrt_eq_rpow] using hh

lemma log_power_nat_decay (r : ℕ) :
    Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ))^r/(N : ℝ)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (r : ℝ) (show (0 : ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_natCast,Real.rpow_one] using hh

lemma profile_sqrt_upper (N : ℕ) (hN : 2 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) :
    Real.sqrt (N : ℝ)*profile N ≤ 2*Real.log N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ)<N := by linarith
  have hH := harmonic_le_one_add_log (N+1)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(N : ℝ)+1)
    (show (N : ℝ)+1 ≤ (N : ℝ)^2 by nlinarith)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  push_cast at hH
  have hp := profile_square_bound N
  have hs := Real.sq_sqrt hnp.le
  have he : (Real.sqrt (N : ℝ)*profile N)^2=(N : ℝ)*(profile N)^2 := by rw [mul_pow,hs]
  push_cast at hp
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (profile_nonneg _)) (by positivity : 0 ≤ 2*Real.log N)).mp
  rw [he]
  have hb : (N : ℝ)*(profile N)^2 ≤ 3*Real.log N := by nlinarith [sq_nonneg (profile N)]
  nlinarith only [hb,hl]

lemma windowSize_bounds (N : ℕ) (hl : 1 ≤ Real.log (N : ℝ)) :
    0<windowSize N ∧ (Real.log (N : ℝ))^8 ≤ windowSize N ∧
      (windowSize N : ℝ) ≤ 2*(Real.log (N : ℝ))^8 := by
  have h1 : (1 : ℝ) ≤ (Real.log (N : ℝ))^8 := one_le_pow₀ hl
  have hlo : (Real.log (N : ℝ))^8 ≤ windowSize N := Nat.le_ceil _
  have hhi : (windowSize N : ℝ)<(Real.log (N : ℝ))^8+1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨?_,hlo,by linarith⟩
  have hh : (0 : ℝ)<windowSize N := by linarith
  exact_mod_cast hh

lemma eventually_window_mass : ∀ᶠ N : ℕ in atTop,
    0<windowSize N ∧ windowSize N ≤ N ∧ (windowSize N : ℝ)*profile N ≤ 1/4 := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop 1,
    (log_power_nat_decay 8).eventually_le_const (show (0 : ℝ)<1/2 by norm_num),
    (log_power_sqrt_decay 9).eventually_le_const (show (0 : ℝ)<1/16 by norm_num)] with N hN hl hnat hsqrt
  obtain ⟨hw,hlo,hhi⟩ := windowSize_bounds N hl
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsp := Real.sqrt_pos.mpr hn
  have hWN : windowSize N ≤ N := by
    have hh := (div_le_iff₀ hn).mp hnat
    have he : (windowSize N : ℝ) ≤ N := by linarith
    exact_mod_cast he
  refine ⟨hw,hWN,?_⟩
  have hp : profile N ≤ 2*Real.log N/Real.sqrt N := (le_div_iff₀ hsp).mpr (by
    have hh := profile_sqrt_upper N hN hl
    nlinarith)
  have hh := mul_le_mul hhi hp (profile_nonneg N) (by positivity : 0 ≤ 2*(Real.log (N : ℝ))^8)
  have he : 2*(Real.log (N : ℝ))^8*(2*Real.log N/Real.sqrt N)=
      4*((Real.log (N : ℝ))^9/Real.sqrt N) := by ring
  rw [he] at hh
  linarith

lemma window_degree_bound (N : ℕ) (B : ℝ) (hB : 1 ≤ B) (hl : 1 ≤ Real.log (N : ℝ)) :
    Real.sqrt (2*(windowSize N : ℝ)*(B*Real.log N)) ≤ 2*B*(Real.log N)^5 := by
  have hw := (windowSize_bounds N hl).2.2
  have hn : 0 ≤ B*Real.log N := by positivity
  have hmul := mul_le_mul_of_nonneg_right hw (show 0 ≤ 2*B*Real.log N by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have hpow : (Real.log (N : ℝ))^9 ≤ (Real.log N)^10 := pow_le_pow_right₀ hl (by omega)
  have hBB : B ≤ B^2 := by nlinarith
  have hh := mul_le_mul hBB hpow (by positivity) (sq_nonneg B)
  nlinarith only [hmul,hh]

/-- Fixed tilts and polynomially many tests are feasible for O(log N)
replacements in windows of width ceil(log(N)^8). -/
theorem eventually_singleton_window_budget (M B ε : ℝ) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (hε : 0<ε) (h : ℕ) :
    let t : ℝ := 20*((h : ℝ)+1)/ε
    0<t ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ M*Real.log N →
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
  have hp15 : L ≤ L^5 := by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 5 by norm_num)
  have hp12 : L ≤ L^2 := by nlinarith
  have h5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hbound : 2*B*L^5+(m : ℝ)+1 ≤ (2*B+M+1)*L^5 := by
    have hh := mul_le_mul_of_nonneg_left hp15 hM
    change (m : ℝ) ≤ M*L at hm
    nlinarith
  have hnum : (m : ℝ)*(Real.exp t*(2*B*L^5+m+1)) ≤
      Real.exp t*M*(2*B+M+1)*L^6 := by
    have hh := mul_le_mul hm hbound (by positivity) (by positivity : 0 ≤ M*L)
    have hhh := mul_le_mul_of_nonneg_left hh (Real.exp_pos t).le
    nlinarith only [hhh]
  have hmean : (m : ℝ)*(Real.exp t*(2*B*L^5+m+1))/((windowSize N : ℝ)/2) ≤ 1 := by
    have hQ2 : Q ≤ L^2 := hQle.trans hp12
    have hh := mul_le_mul_of_nonneg_right hQ2 (show 0 ≤ L^6 by positivity)
    have heq : L^2*L^6=L^8 := by ring
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

end Erdos66LogCellWindowBudget

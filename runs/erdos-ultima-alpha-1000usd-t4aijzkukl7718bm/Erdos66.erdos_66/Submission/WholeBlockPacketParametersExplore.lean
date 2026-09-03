import Submission.UniformWidthPacketsExplore
import Submission.TripleDeletionParametersExplore

/-! Polynomially many repair packets fit into a common exponential choice
width. The mixed-count threshold is the absolute constant 14. -/
namespace Erdos66WholeBlockPacketParameters
open Filter Erdos66TripleDeletionParameters
open scoped Topology
set_option maxHeartbeats 2200000

noncomputable def hitBudget (m K : ℝ) : ℝ :=
  K*(2*Real.sqrt (2*(shift m : ℝ)*(2*m^3)))/(shift m : ℝ)

lemma shift_positive (m : ℝ) : 0<shift m := Nat.ceil_pos.mpr (Real.exp_pos _)

lemma shift_upper (m : ℝ) (hm : 0 ≤ m) : (shift m : ℝ) ≤ 2*Real.exp (4*m) := by
  have hh := Nat.ceil_lt_add_one (Real.exp_pos (4*m)).le
  have he := Real.one_le_exp (show 0 ≤ 4*m by positivity)
  dsimp [shift]
  linarith

lemma choice_root_bound (m : ℝ) (hm : 1 ≤ m) :
    Real.sqrt (2*(shift m : ℝ)*(2*m^3)) ≤ 4*m^2*Real.exp (2*m) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  have h34 : m^3 ≤ m^4 := pow_le_pow_right₀ hm (by norm_num)
  have hh := mul_le_mul_of_nonneg_right (shift_upper m (by linarith)) (show 0 ≤ 4*m^3 by positivity)
  have hh' := mul_le_mul_of_nonneg_right h34 (show 0 ≤ 8*Real.exp (4*m) by positivity)
  have he : Real.exp (2*m)^2=Real.exp (4*m) := by
    rw [←Real.exp_nat_mul]; congr 1; norm_num; ring
  rw [mul_pow,mul_pow,he]
  nlinarith

lemma hitBudget_bound (m C K : ℝ) (hm : 1 ≤ m) (hK0 : 0 ≤ K) (hK : K ≤ C*m^5) :
    hitBudget m K ≤ 8*C*m^7*Real.exp (-2*m) := by
  have hW : (0 : ℝ)<shift m := by exact_mod_cast shift_positive m
  have hWlower : Real.exp (4*m) ≤ (shift m : ℝ) := Nat.le_ceil _
  have hnum : K*(2*Real.sqrt (2*(shift m : ℝ)*(2*m^3))) ≤ 8*K*m^2*Real.exp (2*m) := by
    have hh := mul_le_mul_of_nonneg_left (choice_root_bound m hm) (show 0 ≤ 2*K by positivity)
    nlinarith only [hh]
  have hfirst : hitBudget m K ≤ 8*K*m^2*Real.exp (-2*m) := by
    apply (div_le_iff₀ hW).mpr
    have hh := mul_le_mul_of_nonneg_left hWlower (show 0 ≤ 8*K*m^2*Real.exp (-2*m) by positivity)
    have he : (8*K*m^2*Real.exp (-2*m))*Real.exp (4*m)=8*K*m^2*Real.exp (2*m) := by
      rw [mul_assoc,←Real.exp_add]; congr 2; ring
    rw [he] at hh
    exact hnum.trans hh
  have hsecond := mul_le_mul_of_nonneg_right hK (show 0 ≤ 8*m^2*Real.exp (-2*m) by positivity)
  apply hfirst.trans
  nlinarith only [hsecond]

lemma collisionBudget_bound (m C K : ℝ) (hm : 1 ≤ m) (hC : 1 ≤ C)
    (hK0 : 0 ≤ K) (hK : K ≤ C*m^5) :
    ((2*K)^2+(2*K)^4)/(shift m : ℝ) ≤ 32*C^4*m^20*Real.exp (-4*m) := by
  have hm5 : 1 ≤ m^5 := one_le_pow₀ hm
  have hbase : 1 ≤ 2*C*m^5 := by nlinarith
  have htwo : (2*K)^2 ≤ (2*C*m^5)^2 := by gcongr 1 <;> nlinarith
  have hfour : (2*K)^4 ≤ (2*C*m^5)^4 := by gcongr 1 <;> nlinarith
  have h24 : (2*C*m^5)^2 ≤ (2*C*m^5)^4 := pow_le_pow_right₀ hbase (by norm_num)
  have hnum : (2*K)^2+(2*K)^4 ≤ 32*C^4*m^20 := by
    calc
      _ ≤ 2*(2*C*m^5)^4 := by linarith
      _ = _ := by ring
  have hW : (0 : ℝ)<shift m := by exact_mod_cast shift_positive m
  calc
    _ ≤ (32*C^4*m^20)/(shift m : ℝ) := div_le_div_of_nonneg_right hnum hW.le
    _ ≤ (32*C^4*m^20)/Real.exp (4*m) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) (Nat.le_ceil _)
    _ = _ := by rw [div_eq_mul_inv,←Real.exp_neg]; congr 2; ring

lemma tilted_hitBudget_bound (m C K : ℝ) (hm : 1 ≤ m) (hK0 : 0 ≤ K) (hK : K ≤ C*m^5) :
    Real.exp m*hitBudget m K ≤ 8*C*m^7*Real.exp (-m) := by
  have hh := mul_le_mul_of_nonneg_left (hitBudget_bound m C K hm hK0 hK) (Real.exp_pos m).le
  apply hh.trans_eq
  rw [mul_comm (Real.exp m),mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma poly_exp_decay (n : ℕ) (b : ℝ) (hb : 0<b) :
    Tendsto (fun m : ℝ ↦ m^n*Real.exp (-b*m)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb

/-- Uniform in both the packet count K and the number M of target tests. -/
theorem eventually_packet_budget (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ m : ℝ in atTop, ∀ K M : ℝ, 0 ≤ K → K ≤ C*m^5 → 0 ≤ M → M ≤ 3*Real.exp (12*m) →
      ((2*K)^2+(2*K)^4)/(shift m : ℝ)+hitBudget m K+
        M*Real.exp (Real.exp m*hitBudget m K-m*14) < 1 := by
  have hd1 : Tendsto (fun m : ℝ ↦ 32*C^4*m^20*Real.exp (-4*m)) atTop (𝓝 0) := by
    convert (poly_exp_decay 20 4 (by norm_num)).const_mul (32*C^4) using 1 <;> simp [mul_assoc]
  have hd2 : Tendsto (fun m : ℝ ↦ 8*C*m^7*Real.exp (-2*m)) atTop (𝓝 0) := by
    convert (poly_exp_decay 7 2 (by norm_num)).const_mul (8*C) using 1 <;> simp [mul_assoc]
  have ht : Tendsto (fun m : ℝ ↦ 8*C*m^7*Real.exp (-m)) atTop (𝓝 0) := by
    convert (poly_exp_decay 7 1 (by norm_num)).const_mul (8*C) using 1 <;> simp [mul_assoc]
  have hd3 : Tendsto (fun m : ℝ ↦ 3*Real.exp (1-2*m)) atTop (𝓝 0) := by
    have hh := (poly_exp_decay 0 2 (by norm_num)).const_mul (3*Real.exp 1)
    convert hh using 1
    · ext m
      simp only [pow_zero,one_mul]
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    · simp
  have hd : Tendsto (fun m : ℝ ↦ 32*C^4*m^20*Real.exp (-4*m)+
      8*C*m^7*Real.exp (-2*m)+3*Real.exp (1-2*m)) atTop (𝓝 0) := by
    convert (hd1.add hd2).add hd3 using 1 <;> norm_num
  filter_upwards [eventually_ge_atTop (1 : ℝ),ht.eventually_le_const (by norm_num : (0 : ℝ)<1),
    hd.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with m hm ht hd
  intro K M hK0 hK hM0 hM
  have hb := collisionBudget_bound m C K hm hC hK0 hK
  have hh := hitBudget_bound m C K hm hK0 hK
  have htilt : Real.exp m*hitBudget m K ≤ 1 := (tilted_hitBudget_bound m C K hm hK0 hK).trans ht
  have hterm : M*Real.exp (Real.exp m*hitBudget m K-m*14) ≤ 3*Real.exp (1-2*m) := by
    have he := mul_le_mul hM (Real.exp_le_exp.mpr (sub_le_sub_right htilt (m*14)))
      (Real.exp_pos _).le (by positivity)
    apply he.trans_eq
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  linarith

/-- Every target in the interval to be repaired admits the common width s
inside its middle-third choices. No extra large-center assumption is needed. -/
lemma start_width (m ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1) :
    12*shift m+48 ≤ start m ε := by
  have hs : 1 ≤ shift m := shift_positive m
  have he : 0<ε^2 := sq_pos_of_pos hε
  have hceil := (div_le_iff₀ he).mp (Nat.le_ceil (64*(shift m : ℝ)^2/ε^2))
  have he1 : ε^2 ≤ 1 := by nlinarith
  have hq0 : (0 : ℝ) ≤ start m ε := Nat.cast_nonneg _
  have hq : 64*(shift m : ℝ)^2 ≤ (start m ε : ℝ) := by
    change 64*(shift m : ℝ)^2 ≤ (start m ε : ℝ)*ε^2 at hceil
    nlinarith [mul_le_mul_of_nonneg_left he1 hq0]
  have hs' : (1 : ℝ) ≤ shift m := by exact_mod_cast hs
  have hh : 12*(shift m : ℝ)+48 ≤ (start m ε : ℝ) := by nlinarith
  exact_mod_cast hh

end Erdos66WholeBlockPacketParameters

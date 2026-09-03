import Submission.GreedyBatchScaleTails
import Submission.GreedyBatchCertificate

/-! All fourteen local scalar errors at shrinking-batch scales. The coarse
cap inequalities are explicit and do not assume an asymptotic trajectory. -/
namespace Erdos773.GreedyBatchScaledErrors
open GreedyBatchCertificate GreedyBatchScalarTails GreedyBatchScaleTails
open IndexedBernoulliMoments
set_option maxHeartbeats 3500000
noncomputable section

structure Conditions (c : Caps) (m : ℕ) (p d : ℝ) : Prop where
  large : 100≤ m
  p_nonneg : 0≤p
  p_le_one : p≤1
  common_pos : 0<c.C
  dp_pos : 0<c.D2*c.P
  pair : c.P≤ m
  degree2 : m^52≤c.D2
  degree3 : m^52≤c.D3
  old2 : m^30*c.C≤c.D2
  old3 : m^30*(c.D2*c.P)≤c.D3
  old4 : m^30*(c.D2*c.P)≤c.D4
  oldShared : m^30*(c.D2*c.P)≤c.B
  graph_load : (c.D2:ℝ)*p≤4/(m:ℝ)^2
  promotion31 : 2*c.D3*p≤10*c.D2/(m:ℝ)^2
  promotion41 : 3*c.D4*p≤10*c.D3/(m:ℝ)^2
  promotion42 : 3*c.D4*p^2≤10*c.D2/(m:ℝ)^2
  shared34 : (c.D3:ℝ)*c.P*p≤(m:ℝ)*d/4
  shared44 : 3*(c.D4:ℝ)*c.P*p^2≤(m:ℝ)*d/4
  shared_overlap : (m:ℝ)^46≤(m:ℝ)*d/4
  common : ∀ r∈Finset.Icc 1 4,
    (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r:ℝ)*p^r≤(m:ℝ)^52/4

def margins (c : Caps) (m : ℕ) (p d : ℝ) : Margins where
  old j := 100*c.degree j/(m:ℝ)^4
  promotion31 := 2*c.D3*p+c.D2/(m:ℝ)^4
  promotion41 := 3*c.D4*p+c.D3/(m:ℝ)^4
  promotion42 := 3*c.D4*p^2+c.D2/(m:ℝ)^4
  sharedOld := 100*c.B/(m:ℝ)^4
  shared34 := (m:ℝ)*d
  shared44 := (m:ℝ)*d
  common _ := (m:ℝ)^52

lemma exp_le_failure (m : ℕ) : Real.exp (-(m:ℝ)^7)≤failure m := by
  have hh := (Real.exp_pos (-(m:ℝ)^7)).le
  dsimp [GreedyBatchScaleTails.failure]
  linarith only [hh]

lemma pair_caps (m P : ℕ) (hm : 1≤ m) (hP : P≤ m) :
    8*P≤8*m^2 ∧ 2*P^2≤8*m^2 ∧ 4*P^2≤8*m^2 := by
  have hm2 : m≤ m^2 := by nlinarith only [hm]
  have hp2 := Nat.pow_le_pow_left hP 2
  omega

lemma near_promotion (m r k Dr P S : ℕ) (p : ℝ)
    (hm : 100≤ m) (hk : k≤4) (hP : P≤ m) (hS : m^52≤S)
    (hp : 0≤p) (hp1 : p≤1)
    (hmean : (Dr*(r-1).choose k:ℕ)*p^k≤10*S/(m:ℝ)^2) :
    promotionError r k Dr P (m^10) p
      ((Dr*(r-1).choose k:ℕ)*p^k+S/(m:ℝ)^4)≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hS0 : (0:ℝ)<S := by
    have hs : (m:ℝ)^52≤S := by exact_mod_cast hS
    exact (pow_pos hm0 52).trans_le hs
  apply scaled_moment m k (Dr*(r-1).choose k) _ p _ hm hk hp hp1 (by positivity)
  · simp [GreedyBatchPromotions.overlapCaps]
  · intro j hj hjk
    rw [GreedyBatchPromotions.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m P (by omega) hP).1
  · exact near_mean_margin m S _ hm (by exact_mod_cast hS) hmean

lemma loose_shared (m r s Dr P : ℕ) (p L : ℝ)
    (hm : 100≤ m) (hrs : (r-3)+(s-3)≤4) (hP : P≤ m) (hp : 0≤p) (hp1 : p≤1)
    (hmean : ((Dr*(r-1).choose 2*P:ℕ):ℝ)*p^((r-3)+(s-3))≤L/4)
    (hE : (m:ℝ)^46≤L/4) :
    sharedError r s Dr P (m^10) p L≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hL : 0<L := by have hh := (pow_pos hm0 46).trans_le hE; linarith only [hh]
  apply scaled_moment m ((r-3)+(s-3)) (Dr*(r-1).choose 2*P) _ p L hm hrs hp hp1 hL
  · simp [GreedyBatchSharedWitnesses.overlapCaps]
  · intro j hj hjk
    rw [GreedyBatchSharedWitnesses.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m P (by omega) hP).2.1
  · exact loose_margin m _ L (by omega) hL.le hmean hE

lemma common_overlap (m : ℕ) (hm : 100≤ m) : (m:ℝ)^46≤(m:ℝ)^52/4 := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤100) hmR 6
  have h6 : (4:ℝ)≤(m:ℝ)^6 := by norm_num at hh; linarith only [hh]
  have hh := mul_le_mul_of_nonneg_right h6 (pow_nonneg hm0 46)
  nlinarith only [hh]

lemma common_moment (c : Caps) (m r : ℕ) (p d : ℝ) (h : Conditions c m p d)
    (hr : r∈Finset.Icc 1 4) :
    commonError c (margins c m p d) p (m^10) r≤Real.exp (-(m:ℝ)^7) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by have := h.large; omega)
  apply scaled_moment m r (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 c.P c.B r)
    _ p ((m:ℝ)^52) h.large (Finset.mem_Icc.mp hr).2 h.p_nonneg h.p_le_one (by positivity)
  · simp [GreedyBatchCommonBudgets.overlapCaps]
  · intro j hj hjr
    rw [GreedyBatchCommonBudgets.overlapCaps,if_neg (by omega : j≠0)]
    exact (pair_caps m c.P (by have := h.large; omega) h.pair).2.2
  · exact loose_margin m _ _ (by have := h.large; omega) (by positivity) (h.common r hr) (common_overlap m h.large)

/-- The six vertex-local scalar errors are uniformly small. -/
theorem vertex_errors (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ∀ i, vertexError c (margins c m p d) p (1/(m:ℝ)^2) (m^10) i≤failure m := by
  intro i
  cases i with
  | old2 =>
    simpa only [vertexError,margins,Caps.degree,if_pos rfl] using
      old_scaled m c.D2 c.D2 c.D2 c.C p h.large h.common_pos h.old2 (by omega) h.p_nonneg h.graph_load
  | old3 =>
    simpa [vertexError,margins,Caps.degree] using
      old_scaled m c.D3 (2*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos h.old3 (by omega) h.p_nonneg h.graph_load
  | old4 =>
    simpa [vertexError,margins,Caps.degree] using
      old_scaled m c.D4 (3*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos h.old4 le_rfl h.p_nonneg h.graph_load
  | promotion31 =>
    have hh := near_promotion m 3 1 c.D3 c.P c.D2 p h.large (by decide) h.pair h.degree2 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion31)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh
  | promotion41 =>
    have hh := near_promotion m 4 1 c.D4 c.P c.D3 p h.large (by decide) h.pair h.degree3 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion41)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh
  | promotion42 =>
    have hh := near_promotion m 4 2 c.D4 c.P c.D2 p h.large (by decide) h.pair h.degree2 h.p_nonneg h.p_le_one
      (by simpa [mul_comm] using h.promotion42)
    apply le_trans ?_ (exp_le_failure m)
    simpa [vertexError,margins,Nat.cast_mul,mul_comm] using hh

/-- The eight ordered-pair scalar errors, including all common layers. -/
theorem pair_errors (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ∀ i, pairError c (margins c m p d) p (1/(m:ℝ)^2) (m^10) i≤failure m := by
  have h34 := loose_shared m 3 4 c.D3 c.P p ((m:ℝ)*d) h.large (by decide) h.pair h.p_nonneg h.p_le_one
    (by simpa using h.shared34) h.shared_overlap
  have h44 := loose_shared m 4 4 c.D4 c.P p ((m:ℝ)*d) h.large (by decide) h.pair h.p_nonneg h.p_le_one
    (by simpa [mul_comm,mul_left_comm,mul_assoc] using h.shared44) h.shared_overlap
  intro i
  cases i with
  | sharedOld =>
    exact old_scaled m c.B (2*c.D2) c.D2 (c.D2*c.P) p h.large h.dp_pos
      h.oldShared (by omega) h.p_nonneg h.graph_load
  | shared34 =>
    exact h34.trans (exp_le_failure m)
  | shared43 =>
    exact h34.trans (exp_le_failure m)
  | shared44 =>
    exact h44.trans (exp_le_failure m)
  | common1 =>
    exact (common_moment c m 1 p d h (by decide)).trans (exp_le_failure m)
  | common2 =>
    exact (common_moment c m 2 p d h (by decide)).trans (exp_le_failure m)
  | common3 =>
    exact (common_moment c m 3 p d h (by decide)).trans (exp_le_failure m)
  | common4 =>
    exact (common_moment c m 4 p d h (by decide)).trans (exp_le_failure m)

/-- Positivity of every chosen threshold follows from the same coarse caps. -/
lemma margins_positive (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    (margins c m p d).Positive := by
  have hm : 0< m := by have := h.large; omega
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have h52 : 0< m^52 := pow_pos hm 52
  have h2 : 0<c.D2 := h52.trans_le h.degree2
  have h3 : 0<c.D3 := h52.trans_le h.degree3
  have hprod : 0< m^30*(c.D2*c.P) := Nat.mul_pos (pow_pos hm 30) h.dp_pos
  have h4 : 0<c.D4 := hprod.trans_le h.old4
  have hB : 0<c.B := hprod.trans_le h.oldShared
  have hdj (j : ℕ) : 0<c.degree j := by dsimp [Caps.degree]; split_ifs <;> assumption
  have hmd : 0<(m:ℝ)*d := by
    have hh := (pow_pos hmR 46).trans_le h.shared_overlap
    linarith only [hh]
  have hp := h.p_nonneg
  constructor
  · intro j
    dsimp [margins]
    have hh := hdj j
    positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · dsimp [margins]; positivity
  · exact hmd
  · exact hmd
  · intro j; exact pow_pos hmR 52

/-- The probability and nonnegative-retention guards are also consequences
of the coarse scale conditions, not additional stochastic assumptions. -/
lemma probability_range (c : Caps) (m : ℕ) (p d : ℝ) (h : Conditions c m p d) :
    ProbabilityRange c p (1/(m:ℝ)^2) := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (8:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have he0 : (0:ℝ)≤1/(m:ℝ)^2 := by positivity
  have he1 : (1:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  refine ⟨h.dp_pos,h.common_pos,h.p_nonneg,h.p_le_one,he0,he1,?_⟩
  have hp := h.p_nonneg
  have hloss : (1-1/(m:ℝ)^2)*p*(2*c.D2-(2+c.C))≤2*c.D2*p := by
    have h1 : p*(2*c.D2-(2+c.C))≤2*c.D2*p := by
      have hh := mul_nonneg hp (show (0:ℝ)≤2+c.C by positivity)
      nlinarith only [hh]
    have h2 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr he1)
    have h3 := mul_le_mul_of_nonneg_right (show (1:ℝ)-1/(m:ℝ)^2≤1 by linarith only [he0])
      (show (0:ℝ)≤2*c.D2*p by positivity)
    nlinarith only [h2,h3]
  have hload : 2*(c.D2:ℝ)*p≤1 := by
    have hh := h.graph_load
    have h8 : (8:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hm2
    ring_nf at hh h8 ⊢
    nlinarith only [hh,h8]
  have hh := sub_nonneg.mpr (hloss.trans hload)
  simpa [retention] using hh

#print axioms near_promotion
#print axioms loose_shared
#print axioms common_moment
#print axioms vertex_errors
#print axioms pair_errors
#print axioms margins_positive
#print axioms probability_range
end
end Erdos773.GreedyBatchScaledErrors

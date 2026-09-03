import Submission.PrimitiveHeightObstruction

/-! Uniform height bookkeeping for repeated primitive-kernel descent. The
logarithmic covolume increases by at most 3H at each step, with H fixed at the
start of the induction. Consequently the interval loss remains polynomial in
the ambient dimension and linear in the initial height. -/
namespace Erdos3LatticeHeightDescent
open Erdos3PrimitiveHeightObstruction Erdos3LatticePrecisionBudget
  Erdos3SharpHigherPhaseWeylInverse
set_option maxHeartbeats 4000000

def baseWeylCost (k D : ℕ) : ℕ := sharpWeylConstant k*(2*D+9)*(4*D+2)
def stepHeight (k D H : ℕ) : ℕ := (2*baseWeylCost k D+6*D+10)*H+(k+1).factorial

lemma six_mul_sq_le_two_pow (H : ℕ) (hH : 16 ≤ H) : 6*H^2 ≤ 2^H := by
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ H hH ih =>
    rw [pow_succ 2 H]
    nlinarith

lemma height_controls (k D H m s V : ℕ)
    (hH : 16 ≤ H) (hD : D ≤ H) (hm : m ≤ D)
    (hT : dualHeight m s ≤ H) (hV : V ≤ (3*(D-m)+1)*H) :
    precisionHeight m s V ≤ (4*D+2)*H ∧
    precisionHeight m s V ≤ 2^H ∧
    weylHeight k m s V ≤ stepHeight k D H ∧
    2*weylHeight k m s V+(k+1).factorial+dualHeight m s+
      2*(m^2+V)+(s+1)+2*H ≤ stepHeight k D H := by
  have hs : s+2*m+2 ≤ H := by unfold dualHeight at hT; omega
  have hV' : V ≤ (3*D+1)*H := hV.trans (Nat.mul_le_mul_right H (by omega))
  have hP : precisionHeight m s V ≤ (4*D+2)*H := by
    have hh := Nat.mul_le_mul hm hs
    unfold precisionHeight basisPrecisionBudget
    nlinarith only [hh,hV',hH]
  have hPdyadic : precisionHeight m s V ≤ 2^H := by
    apply (hP.trans ?_).trans (six_mul_sq_le_two_pow H hH)
    nlinarith only [hD,hH]
  have hU : m^2+V ≤ (3*D+2)*H := by
    have hm2 : m^2 ≤ H := by unfold dualHeight at hT; omega
    nlinarith only [hm2,hV']
  have hs1 : s+1 ≤ H := by omega
  have hW : weylHeight k m s V ≤ baseWeylCost k D*H := by
    unfold weylHeight baseWeylCost
    calc
      _ ≤ sharpWeylConstant k*(2*D+9)*((4*D+2)*H) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hP
      _ = _ := by ring
  have hbudget : 2*weylHeight k m s V+(k+1).factorial+dualHeight m s+
      2*(m^2+V)+(s+1)+2*H ≤ stepHeight k D H := by
    unfold stepHeight
    nlinarith only [hW,hT,hU,hs1]
  exact ⟨hP,hPdyadic,by omega,hbudget⟩

lemma dualHeight_descends (m s : ℕ) : dualHeight m (s+1) ≤ dualHeight (m+1) s := by
  unfold dualHeight
  nlinarith

lemma covolumeHeight_descends (D H m V : ℕ) (hm : m+1 ≤ D)
    (hV : V ≤ (3*(D-(m+1))+1)*H) : V+3*H ≤ (3*(D-m)+1)*H := by
  have hd : D-m = D-(m+1)+1 := by omega
  rw [hd]
  nlinarith only [hV]

lemma dyadic_norm_budget (T P H : ℕ) (hT : T ≤ H) (hP : P ≤ 2^H) :
    (2:ℝ)^T*(P:ℝ)^2 ≤ (2:ℝ)^(3*H) := by
  have hP' : (P:ℝ) ≤ (2:ℝ)^H := by exact_mod_cast hP
  calc
    _ ≤ (2:ℝ)^H*((2:ℝ)^H)^2 := by gcongr <;> norm_num
    _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega

lemma dyadic_stride_budget (q W T U P H s k B : ℕ)
    (hq : q ≤ 2^(W+(k+1).factorial+T+U)*P^2) (hP : P ≤ 2^H)
    (hbudget : 2*W+(k+1).factorial+T+2*U+(s+1)+2*H ≤ B) :
    q*2^(W+(s+1)+U) ≤ 2^B := by
  calc
    _ ≤ (2^(W+(k+1).factorial+T+U)*(2^H)^2)*2^(W+(s+1)+U) :=
      Nat.mul_le_mul_right _ (hq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2)))
    _ = 2^((W+(k+1).factorial+T+U)+H*2+(W+(s+1)+U)) := by
      rw [← pow_mul,← pow_add,← pow_add]
    _ ≤ 2^B := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

lemma dyadic_lift_error_budget (W U s k : ℕ) {a : ℝ} (ha : (1/2:ℝ)^U ≤ a) :
    (2:ℝ)^W ≤ (1/2:ℝ)^(s+1)*a*((2^(W+(s+1)+U):ℕ):ℝ)^(k+1) := by
  have ha0 : 0 ≤ a := (by positivity : (0:ℝ) ≤ (1/2)^U).trans ha
  have hS : (1:ℝ) ≤ (2:ℝ)^(W+(s+1)+U) := one_le_pow₀ (by norm_num)
  have hSpow : (2:ℝ)^(W+(s+1)+U) ≤ ((2:ℝ)^(W+(s+1)+U))^(k+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hS (show 1 ≤ k+1 by omega)
  push_cast
  calc
    _ = (1/2:ℝ)^(s+1)*(1/2:ℝ)^U*(2:ℝ)^(W+(s+1)+U) := by
      simp only [div_pow,one_pow,pow_add,pow_succ]
      field_simp
    _ ≤ (1/2:ℝ)^(s+1)*a*(2:ℝ)^(W+(s+1)+U) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hSpow (mul_nonneg (by positivity) ha0)

#print axioms height_controls
#print axioms dyadic_lift_error_budget
end Erdos3LatticeHeightDescent

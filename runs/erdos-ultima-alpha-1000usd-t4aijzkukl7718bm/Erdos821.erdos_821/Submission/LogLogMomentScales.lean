import Submission.FiniteNearMoment

/-!
# A growing auxiliary parameter with a uniform error budget

The divisor order stays fixed. The parameter A=2^m grows, with base scale
E=2^(2*m+10). All bounds here are finite inequalities or genuine eventual
bounds along this explicit joint choice.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 5000000

def loglogMomentA (m : ℕ) : ℕ := 2^m
def loglogMomentIndex (m : ℕ) : ℕ := 2*m+5
def loglogMomentE (m : ℕ) : ℕ := logMomentScale (loglogMomentIndex m)
def loglogMomentX (w m : ℕ) : ℕ := nearMomentX w (loglogMomentA m) (loglogMomentIndex m)
def loglogBudgetConstant (w : ℕ) : ℕ := 2^24*(w+1)^2

lemma loglogMomentE_eq (m : ℕ) : loglogMomentE m = 2^(2*m+10) := by
  unfold loglogMomentE logMomentScale loglogMomentIndex
  congr 1

lemma loglogMomentA_pos (m : ℕ) : 0 < loglogMomentA m := by unfold loglogMomentA; positivity
lemma loglogMomentE_pos (m : ℕ) : 0 < loglogMomentE m := by rw [loglogMomentE_eq]; positivity

lemma loglog_nearMomentC_bound (w m : ℕ) :
    nearMomentC w (loglogMomentA m) ≤ 2^17*(w+1)*loglogMomentA m := by
  have ha := loglogMomentA_pos m
  unfold nearMomentC
  calc
    _ ≤ 4096*(w+1)*(21*loglogMomentA m) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4096 (Nat.le_succ w)) (by omega)
    _ = (4096*21)*((w+1)*loglogMomentA m) := by ring
    _ ≤ 2^17*((w+1)*loglogMomentA m) := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

lemma loglog_budget_base_bound (w m : ℕ) :
    64*nearMomentC w (loglogMomentA m)+1 ≤ 2^(m+w+25) := by
  let a := loglogMomentA m
  have ha : 1 ≤ a := loglogMomentA_pos m
  have hC := loglog_nearMomentC_bound w m
  have hprod : 1 ≤ (w+1)*a := Nat.mul_pos (by omega) ha
  have hbase : 64*nearMomentC w a+1 ≤ 2^24*(w+1)*a := by
    have h := Nat.mul_le_mul_left 64 hC
    change 64*nearMomentC w a ≤ 64*(2^17*(w+1)*a) at h
    norm_num only at h ⊢
    nlinarith only [h,hprod]
  calc
    _ ≤ 2^24*(w+1)*a := hbase
    _ ≤ 2^24*2^(w+1)*2^m := by
      apply Nat.mul_le_mul_right a
      exact Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    _ = _ := by
      rw [← pow_add,← pow_add]
      congr 1
      omega

lemma loglog_budget_degree_bound (w m : ℕ) :
    w*nearMomentC w (loglogMomentA m)+6*(loglogMomentA m+22) ≤
      (2^18*(w+1)^2)*loglogMomentA m := by
  let a := loglogMomentA m
  have ha : 1 ≤ a := loglogMomentA_pos m
  have hC := loglog_nearMomentC_bound w m
  have h1 : w*nearMomentC w a ≤ 2^17*(w+1)^2*a := by
    calc
      _ ≤ (w+1)*(2^17*(w+1)*a) := Nat.mul_le_mul (Nat.le_succ w) hC
      _ = _ := by ring
  have h2 : 6*(a+22) ≤ 138*a := by omega
  have h3 : a ≤ (w+1)^2*a := Nat.le_mul_of_pos_left _ (by positivity)
  change _ ≤ (2^18*(w+1)^2)*a
  norm_num only at h1 ⊢
  nlinarith only [h1,h2,h3]

lemma loglog_budget_exponent_bound (w m : ℕ) :
    64+6*(m+w+25)+(2*m+11)*((2^18*(w+1)^2)*loglogMomentA m) ≤
      loglogBudgetConstant w*(m+1)*loglogMomentA m := by
  let a := loglogMomentA m
  let V := (w+1)^2
  have ha : 1 ≤ a := loglogMomentA_pos m
  have hsmall : 64+6*(m+w+25) ≤ (2^18*V)*(m+1)*a := by
    calc
      _ ≤ (220+6*w)*(m+1) := by nlinarith [Nat.zero_le (w*m)]
      _ ≤ (1024*V)*(m+1) := by
        apply Nat.mul_le_mul_right
        dsimp [V]
        nlinarith [Nat.zero_le w]
      _ ≤ (2^18*V)*(m+1) := by gcongr; norm_num
      _ ≤ _ := Nat.le_mul_of_pos_right _ ha
  have hlarge : (2*m+11)*((2^18*V)*a) ≤ 11*(2^18*V)*(m+1)*a := by
    have h := Nat.mul_le_mul_right ((2^18*V)*a) (show 2*m+11 ≤ 11*(m+1) by omega)
    nlinarith only [h]
  have heq : loglogBudgetConstant w*(m+1)*a = 2^24*(V*(m+1)*a) := by
    unfold loglogBudgetConstant V
    ring
  change _ ≤ loglogBudgetConstant w*(m+1)*a
  rw [heq]
  change 64+6*(m+w+25)+(2*m+11)*((2^18*V)*a) ≤ 2^24*(V*(m+1)*a)
  norm_num only at hsmall hlarge ⊢
  nlinarith only [hsmall,hlarge,Nat.zero_le (V*(m+1)*a)]

lemma loglog_nearMomentBudget_bound (w m : ℕ) :
    nearMomentBudget w (loglogMomentA m) (loglogMomentIndex m) ≤
      2^(loglogBudgetConstant w*(m+1)*loglogMomentA m) := by
  let a := loglogMomentA m
  let C := nearMomentC w a
  let d := w*C+6*(a+22)
  have hbase := loglog_budget_base_bound w m
  have hdegree := loglog_budget_degree_bound w m
  have hE : loglogMomentE m+1 ≤ 2^(2*m+11) := by
    rw [loglogMomentE_eq,show 2*m+11=(2*m+10)+1 by omega,pow_succ _ (2*m+10)]
    have hp : 1 ≤ 2^(2*m+10) := Nat.one_le_pow _ _ (by decide)
    omega
  have hp : (loglogMomentE m+1)^d ≤ (2^(2*m+11))^((2^18*(w+1)^2)*a) :=
    (Nat.pow_le_pow_left hE d).trans (Nat.pow_le_pow_right (by positivity) hdegree)
  calc
    _ ≤ 2^64*(2^(m+w+25))^6*(2^(2*m+11))^((2^18*(w+1)^2)*a) := by
      unfold nearMomentBudget
      exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hbase 6)) hp
    _ = 2^(64+6*(m+w+25)+(2*m+11)*((2^18*(w+1)^2)*a)) := by
      rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
      apply congrArg (fun e : ℕ => (2 : ℕ)^e)
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (loglog_budget_exponent_bound w m)

lemma loglog_nearMomentR_bound (w m : ℕ) :
    nearMomentR w (loglogMomentA m) (loglogMomentIndex m)+1 ≤
      loglogBudgetConstant w*(m+1)*loglogMomentA m := by
  let a := loglogMomentA m
  have ha : 1 ≤ a := loglogMomentA_pos m
  have hC := loglog_nearMomentC_bound w m
  have h1 : nearMomentR w a (loglogMomentIndex m) ≤
      (10*2^17*(w+1))*(m+1)*a := by
    unfold nearMomentR loglogMomentIndex
    have h := Nat.mul_le_mul hC (show 2*m+5+5 ≤ 10*(m+1) by omega)
    nlinarith only [h]
  have hprod : 1 ≤ (m+1)*a := Nat.mul_pos (by omega) ha
  have hcoef : 10*2^17*(w+1)+1 ≤ loglogBudgetConstant w := by
    unfold loglogBudgetConstant
    norm_num only
    nlinarith [Nat.zero_le w]
  have h2 := Nat.mul_le_mul_right ((m+1)*a) hcoef
  change _ ≤ loglogBudgetConstant w*(m+1)*a
  nlinarith only [h1,hprod,h2]

lemma eventually_loglog_finite_conditions (w : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      nearMomentBudget w (loglogMomentA m) (loglogMomentIndex m) ≤ 2^(loglogMomentE m) ∧
      nearMomentR w (loglogMomentA m) (loglogMomentIndex m)+1 ≤ loglogMomentE m := by
  have hevent := eventually_nat_poly_le_two_pow 1 (loglogBudgetConstant w) 1
  filter_upwards [hevent] with m hm
  have hlin : loglogBudgetConstant w*(m+1) ≤ loglogMomentA m := by
    simpa only [one_mul,pow_one,loglogMomentA] using hm
  have hsmall : loglogBudgetConstant w*(m+1)*loglogMomentA m ≤ loglogMomentE m := by
    calc
      _ ≤ loglogMomentA m*loglogMomentA m := Nat.mul_le_mul_right _ hlin
      _ ≤ loglogMomentE m := by
        rw [loglogMomentA,← pow_add,loglogMomentE_eq]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨(loglog_nearMomentBudget_bound w m).trans (Nat.pow_le_pow_right (by decide) hsmall),
    (loglog_nearMomentR_bound w m).trans hsmall⟩

lemma nearMoment_lower_conductor_of_R_bound (w A m : ℕ)
    (hR : nearMomentR w A m+1 ≤ logMomentScale m) :
    2*w*(A+20) ≤ logMomentScale m := by
  have h : 2*w*(A+20) ≤ nearMomentR w A m := by
    unfold nearMomentR nearMomentC
    calc
      _ ≤ 4096*w*(A+20) := by gcongr; norm_num
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The divisor order w+1 is fixed while the auxiliary parameter grows. -/
theorem eventually_loglog_primeLog_lower (w : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop,
      (loglogMomentX w m : ℝ)*(loglogMomentE m : ℝ)^(w*(loglogMomentA m+8)) ≤
        primeLogDivisorMoment (w+1) (loglogMomentX w m) := by
  filter_upwards [eventually_loglog_finite_conditions w,eventually_ge_atTop 2048]
    with m hm hm2048
  exact nearMoment_primeLog_lower_of_conditions w (loglogMomentA m) (loglogMomentIndex m) hw
    (nearMoment_lower_conductor_of_R_bound _ _ _ hm.2) hm.2
    (by unfold loglogMomentIndex; omega) hm.1

end Erdos821

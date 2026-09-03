import Submission.AffinePotentialCertificates

/-! A concrete weighted automaton with slope4/5. Its arithmetic growth and
good-word bound are verified, but the slope is ABOVE the required threshold.
This is a control of the certificate framework, not a proof of Erdős406. -/

namespace Erdos406WeightedControl
open Erdos406AffinePotential Erdos406GroupedCertificate

noncomputable section

def D : DFA ℕ (Fin 4) where
  start := 0
  step s d := if s.val = 0 then (if d = 0 then 0 else if d = 1 then 1 else 2)
    else if s.val = 1 ∧ d = 2 then 2 else 3
  accept := Set.univ

def w (s : Fin 4) (d : ℕ) : ℝ :=
  (if s.val = 0 then (if d = 0 then 0 else if d = 1 then 5 else 7)
   else if s.val = 1 then (if d = 0 then 3 else if d = 1 then 4 else 5)
   else if s.val = 2 then (if d = 0 then 3 else 4) else 4) / 5

def R (s t : Fin 4) (c : ℕ) : Prop :=
  t.val = if s.val = 0 then c else if s.val = 1 ∧ c = 1 then 2 else 3

def P (s _t : Fin 4) (c : ℕ) : ℝ :=
  (if s.val = 0 then (if c = 0 then 0 else if c = 1 then 5 else if c = 2 then 7 else 8)
   else if s.val = 1 then (if c = 0 then 4 else if c = 3 then 6 else 5)
   else if s.val = 2 then (if c = 0 then 4 else 5) else 5) / 5

set_option maxHeartbeats 2000000 in
def growth : Growth (Fin 4) where
  D := D
  w := w
  R := R
  P := P
  relation_start := by
    intro c hc
    interval_cases c <;>
      norm_num [R,D,evalNat,Nat.digits_of_two_le_of_pos,DFA.eval,DFA.evalFrom]
  relation_step := by
    intro s t c d e cp hc hd he hcp har hr
    have hce : c = (4*d+cp)/3 := by omega
    have hee : e = (4*d+cp)%3 := by omega
    subst c e
    interval_cases d <;> interval_cases cp <;> fin_cases s <;> fin_cases t <;>
      norm_num [R,D] at *
  lower_start := by
    intro c hc
    interval_cases c <;>
      norm_num [P,D,w,evalNat,weightNat,weightFrom,Nat.digits_of_two_le_of_pos,DFA.eval,DFA.evalFrom]
  lower_step := by
    intro s t c d e cp hc hd he hcp har hr
    have hce : c = (4*d+cp)/3 := by omega
    have hee : e = (4*d+cp)%3 := by omega
    subst c e
    interval_cases d <;> interval_cases cp <;> fin_cases s <;> fin_cases t <;>
      norm_num [R,P,D,w] at *
  lower_finish := by
    intro s t hr
    fin_cases s <;> fin_cases t <;> norm_num [R,P] at *

def J (s : Fin 4) : ℝ := if s.val = 1 ∨ s.val = 3 then 1/5 else 0

def goodBound : GoodBound D w where
  c := 4/5
  B := 1/5
  c_nonneg := by norm_num
  G s := s.val ≠ 2
  J := J
  start := by norm_num [D]
  step := by
    intro s d hd hs
    interval_cases d <;> fin_cases s <;> norm_num [D] at *
  weight_step := by
    intro s d hd hs
    interval_cases d <;> fin_cases s <;> norm_num [D,w,J] at *
  bound := by
    intro s hs
    fin_cases s <;> norm_num [D,J] at *

theorem control_grows (n : ℕ) : weightNat D w n + 1 ≤ weightNat D w (4*n+1) :=
  growth.grows n

theorem control_good_bound (n : ℕ) (hn : Good n) :
    weightNat D w n ≤ (4/5 : ℝ) * (Nat.digits 3 n).length + 1/5 :=
  goodBound.good_bound n hn

/-- The missing strict threshold condition is FALSE for this control. -/
theorem control_not_subcritical : ¬ (4/5 : ℝ) * Real.log 4 < Real.log 3 := by
  have hh := Real.log_lt_log (by positivity : (0 : ℝ) < 3^5)
    (by norm_num : (3 : ℝ)^5 < 4^4)
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num at hh
  nlinarith

#print axioms control_grows
#print axioms control_good_bound
#print axioms control_not_subcritical
end
end Erdos406WeightedControl

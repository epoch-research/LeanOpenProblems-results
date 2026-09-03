import Submission.BinaryWeightedCertificates

/-! An exactly checked binary weighted control at rate 5/8. This improves
the previous search control 3/5 but remains BELOW the required rate. It is
not a solution to Erdős 406. -/

namespace Erdos406BinaryWeightedControl
open Erdos406BinaryWeighted Erdos406GroupedCertificate Erdos406AffinePotential

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def D : DFA ℕ (Fin 6) where
  start := 0
  step s d := if s = 0 then (if d = 0 then 0 else 1)
    else if s = 1 then (if d = 0 then 2 else 3)
    else if s = 2 then (if d = 0 then 3 else 4)
    else if s = 4 then (if d = 0 then 3 else 5) else 5
  accept := Set.univ

def W (s : Fin 6) (d : ℕ) : ℤ :=
  if s = 0 then (if d = 0 then 0 else 8)
  else if s = 1 then (if d = 0 then -2 else 0)
  else if s = 2 then (if d = 0 then 4 else 6)
  else if s = 3 then (if d = 0 then 5 else 6)
  else if s = 4 then (if d = 0 then 4 else 5) else 5

def H (s : Fin 6) (c : ℕ) : ℤ :=
  if s = 0 then (if c = 0 then 0 else if c = 1 then 8 else 6)
  else if s = 1 then (if c = 0 then 0 else if c = 1 then 2 else 4)
  else if s = 2 then (if c = 0 then 7 else if c = 1 then 8 else 9)
  else if s = 3 then (if c = 2 then 9 else 8)
  else if s = 4 then (if c = 0 then 7 else 8) else 8

def R (s t : Fin 6) (c : ℕ) : Prop := c < 3 ∧
  if s = 0 then t.val = c
  else if s = 1 then t = (if c = 2 then 4 else 3)
  else if s = 3 ∧ c = 1 then t = 3 ∨ t = 5 else t = 5

instance (s t : Fin 6) (c : ℕ) : Decidable (R s t c) := by unfold R; infer_instance

def w (s : Fin 6) (d : ℕ) : ℝ := (W s d : ℝ) / 8

def P (s _t : Fin 6) (c : ℕ) : ℝ := (H s c : ℝ) / 8

lemma relation_check : ∀ (s t : Fin 6) (c : Fin 3) (d e : Fin 2) (cp : Fin 3),
    3 * d.val + cp.val = 2 * c.val + e.val → R s t c.val →
      R (D.step s d.val) (D.step t e.val) cp.val := by decide +kernel

lemma upper_check : ∀ (s t : Fin 6) (c : Fin 3) (d e : Fin 2) (cp : Fin 3),
    3 * d.val + cp.val = 2 * c.val + e.val → R s t c.val →
      H s c.val + W t e.val - W s d.val ≤ H (D.step s d.val) cp.val := by decide +kernel

lemma finish_check : ∀ (s t : Fin 6) (c : Fin 2), R s t c.val → H s c.val ≤ 8 := by
  decide +kernel

def construction : Construction (Fin 6) where
  D := D
  w := w
  R := R
  P := P
  relation_start := by
    intro c hc
    interval_cases c <;>
      norm_num [R, D, evalNat, Nat.digits_of_two_le_of_pos, DFA.eval, DFA.evalFrom]
  relation_step := by
    intro s t c d e cp hc hd he hcp har hr
    exact relation_check s t ⟨c, hc⟩ ⟨d, hd⟩ ⟨e, he⟩ ⟨cp, hcp⟩ har hr
  upper_start := by
    intro c hc
    interval_cases c <;>
      norm_num [Erdos406BinaryWeighted.weightNat, weightFrom, w, P, W, H, D, evalNat,
        Nat.digits_of_two_le_of_pos, DFA.eval, DFA.evalFrom]
  upper_step := by
    intro s t c d e cp hc hd he hcp har hr
    have hh := upper_check s t ⟨c, hc⟩ ⟨d, hd⟩ ⟨e, he⟩ ⟨cp, hcp⟩ har hr
    have hhR : (H s c : ℝ) + W t e - W s d ≤ H (D.step s d) cp := by exact_mod_cast hh
    change (H s c : ℝ) / 8 + (W t e : ℝ) / 8 - (W s d : ℝ) / 8 ≤
      (H (D.step s d) cp : ℝ) / 8
    linarith
  upper_finish := by
    intro s t c hc hr
    have hh := finish_check s t ⟨c, hc⟩ hr
    have hhR : (H s c : ℝ) ≤ 8 := by exact_mod_cast hh
    change (H s c : ℝ) / 8 ≤ 1
    linarith

def G (s : Fin 6) : Prop := s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 5
instance (s : Fin 6) : Decidable (G s) := by unfold G; infer_instance

def J (s : Fin 6) : ℤ := if s = 2 then -7 else if s = 3 ∨ s = 5 then -8 else 0

lemma power_checks : (∀ s : Fin 6, G s → G (D.step s 0)) ∧
    (∀ s : Fin 6, G s → 5 + J (D.step s 0) - J s ≤ W s 0) ∧
    (∀ s : Fin 6, G s → 0 ≤ 8 + J s) := by decide +kernel

def powerBound : PowerBound D w where
  a := 5 / 8
  B := 0
  G := G
  J s := (J s : ℝ) / 8
  start := by decide +kernel
  step := power_checks.1
  lower_step := by
    intro s hs
    have hh := power_checks.2.1 s hs
    have hhR : (5 : ℝ) + J (D.step s 0) - J s ≤ W s 0 := by exact_mod_cast hh
    change (5 : ℝ) / 8 + (J (D.step s 0) : ℝ) / 8 - (J s : ℝ) / 8 ≤ (W s 0 : ℝ) / 8
    linarith
  lower_end := by
    intro s hs
    have hh := power_checks.2.2 s hs
    have hhR : (0 : ℝ) ≤ 8 + J s := by exact_mod_cast hh
    change -(0 : ℝ) ≤ (W D.start 1 : ℝ) / 8 + (J s : ℝ) / 8 -
      (J (D.step D.start 1) : ℝ) / 8
    rw [show W D.start 1 = 8 from by decide +kernel,
      show J (D.step D.start 1) = 0 from by decide +kernel]
    norm_num
    linarith

theorem control_construction_bound (n d : ℕ) (hd : d < 2) :
    Erdos406BinaryWeighted.weightNat D w (3 * n + d) ≤
      Erdos406BinaryWeighted.weightNat D w n + 1 := construction.construction_bound n d hd

theorem control_power_bound (k : ℕ) :
    (5 / 8 : ℝ) * k ≤ Erdos406BinaryWeighted.weightNat D w (2 ^ k) := by
  simpa only [powerBound, sub_zero] using powerBound.power_lower k

/-- The strict rate needed by weighted_binary_criterion is false here. -/
theorem control_not_supercritical : ¬ Real.log 2 < (5 / 8 : ℝ) * Real.log 3 := by
  have hh := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 5)
    (by norm_num : (3 : ℝ) ^ 5 < 2 ^ 8)
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num at hh
  linarith

#print axioms control_construction_bound
#print axioms control_power_bound
#print axioms control_not_supercritical
end
end Erdos406BinaryWeightedControl

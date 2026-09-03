import Submission.TropicalCertificates

/-! A checked max-plus control certificate. Its slope is too large to settle
Erdős406. This file makes no finiteness claim. -/
namespace Erdos406TropicalControl
open Erdos406Tropical

def qrow (a b c d : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

def next (s : Fin 4) (d : ℕ) : Finset (Fin 4) :=
  if s = 0 ∧ d = 0 then {0} else {1, 2, 3}

def R (s t : Fin 4) (c : ℕ) : Prop := t.val ≠ 0 ∨ (s.val = 0 ∧ c = 0)
instance (s t : Fin 4) (c : ℕ) : Decidable (R s t c) := inferInstanceAs (Decidable (_ ∨ _))

def wq (s : Fin 4) (d : ℕ) (t : Fin 4) : ℚ :=
    if s.val = 0 then (if d = 0 then qrow (0) 0 0 0 t.val else if d = 1 then qrow 0 (1) (-8) (-8) t.val else qrow 0 (-8) (7 / 5) (-8) t.val) else
    if s.val = 1 then (if d = 0 then qrow 0 (-8) (-8) (3 / 5) t.val else if d = 1 then qrow 0 (-8) (-8) (4 / 5) t.val else qrow 0 (-8) (1) (-8) t.val) else
    if s.val = 2 then (if d = 0 then qrow 0 (-8) (-8) (3 / 5) t.val else if d = 1 then qrow 0 (-8) (-8) (4 / 5) t.val else qrow 0 (-8) (-8) (4 / 5) t.val) else
    (if d = 0 then qrow 0 (-8) (-8) (4 / 5) t.val else if d = 1 then qrow 0 (-8) (-8) (4 / 5) t.val else qrow 0 (-8) (-8) (4 / 5) t.val)

def hq (s t : Fin 4) (c : ℕ) : ℚ :=
    if s.val = 0 then (if t.val = 0 then qrow (0) 0 0 0 c else
    if t.val = 1 then qrow (32) (1) (24) (32) c else
    if t.val = 2 then qrow (32) (6 / 5) (7 / 5) (32) c else
    qrow (32) (6 / 5) (32) (8 / 5) c) else
    if s.val = 1 then (if t.val = 0 then qrow 0 0 0 0 c else
    if t.val = 1 then qrow (32) (1) (6 / 5) (10) c else
    if t.val = 2 then qrow (1) (1) (32) (23) c else
    qrow (4 / 5) (1) (1) (6 / 5) c) else
    if s.val = 2 then (if t.val = 0 then qrow 0 0 0 0 c else
    if t.val = 1 then qrow (23) (1) (32) (14) c else
    if t.val = 2 then qrow (1) (1) (32) (32) c else
    qrow (4 / 5) (1) (1) (1) c) else
    (if t.val = 0 then qrow 0 0 0 0 c else
    if t.val = 1 then qrow (49 / 5) (6 / 5) (116 / 5) (49 / 5) c else
    if t.val = 2 then qrow (32) (6 / 5) (32) (71 / 5) c else
    qrow (1) (1) (1) (1) c)

def jq (s : Fin 4) : ℚ := qrow (0) (1 / 5) (-43 / 5) (1 / 5) s.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma step_checked : ∀ (s t c cp : Fin 4) (d e : Fin 3),
    4*d.val+cp.val = 3*c.val+e.val → R s t c.val →
    ∀ sp ∈ next s d.val, ∃ tp ∈ next t e.val, R sp tp cp.val ∧
      hq sp tp cp.val ≤ hq s t c.val + wq t e.val tp - wq s d.val sp := by
  decide +kernel

lemma finish_checked : ∀ s t : Fin 4, R s t 1 → 1 ≤ hq s t 1 := by
  decide +kernel

lemma good_checked : ∀ (s t : Fin 4) (d : Fin 2), t ∈ next s d.val →
    wq s d.val t ≤ (4/5 : ℚ) + jq t - jq s := by
  decide +kernel

lemma bound_checked : ∀ s : Fin 4, jq s - jq 0 ≤ (1/5 : ℚ) := by
  decide +kernel


noncomputable def control : Automaton (Fin 4) where
  next := next
  nonempty s d := by
    simp only [next]
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  weight s d t := (wq s d t : ℝ)
  start := 0

lemma weight_011 : control.weight 0 1 1 = 1 := by
  change (wq 0 1 1 : ℝ) = 1
  rw [show wq 0 1 1 = 1 by decide +kernel]
  norm_num

lemma weight_022 : control.weight 0 2 2 = 7/5 := by
  change (wq 0 2 2 : ℝ) = 7/5
  rw [show wq 0 2 2 = (7/5 : ℚ) by decide +kernel]
  norm_num

lemma weight_103 : control.weight 1 0 3 = 3/5 := by
  change (wq 1 0 3 : ℝ) = 3/5
  rw [show wq 1 0 3 = (3/5 : ℚ) by decide +kernel]
  norm_num

noncomputable def controlSimulation : Simulation control where
  R := R
  H s t c := (hq s t c : ℝ)
  seed c hc := by
    change ∃ t v, Run control 0 (Nat.digits 3 c).reverse t v ∧ R 0 t c ∧
      (hq 0 t c : ℝ) ≤ v
    interval_cases c
    · refine ⟨0, 0, ?_, by decide, ?_⟩
      · simpa using (Run.nil (D := control) (0 : Fin 4))
      · norm_num [hq, qrow]
    · refine ⟨1, 1, ?_, by decide, ?_⟩
      · rw [show Nat.digits 3 1 = [1] by norm_num [Nat.digits_of_two_le_of_pos]]
        change Run control 0 [1] 1 1
        have hr := Run.cons (D := control) (s := 0) (d := 1)
          (by decide : 1 ∈ control.next 0 1) (Run.nil 1)
        norm_num only [weight_011, weight_022, weight_103, add_zero] at hr
        exact hr
      · norm_num [hq, qrow]
    · refine ⟨2, 7/5, ?_, by decide, ?_⟩
      · rw [show Nat.digits 3 2 = [2] by norm_num [Nat.digits_of_two_le_of_pos]]
        change Run control 0 [2] 2 (7/5)
        have hr := Run.cons (D := control) (s := 0) (d := 2)
          (by decide : 2 ∈ control.next 0 2) (Run.nil 2)
        norm_num only [weight_011, weight_022, weight_103, add_zero] at hr
        exact hr
      · norm_num [hq, qrow]
    · refine ⟨3, 8/5, ?_, by decide, ?_⟩
      · rw [show Nat.digits 3 3 = [0,1] by norm_num [Nat.digits_of_two_le_of_pos]]
        change Run control 0 [1,0] 3 (8/5)
        have hr := Run.cons (D := control) (s := 0) (d := 1)
          (by decide : 1 ∈ control.next 0 1)
          (Run.cons (D := control) (s := 1) (d := 0)
            (by decide : 3 ∈ control.next 1 0) (Run.nil 3))
        norm_num only [weight_011, weight_022, weight_103, add_zero] at hr
        exact hr
      · norm_num [hq, qrow]
  step s t c d e cp hc hd he hcp hid hr sp hs := by
    obtain ⟨tp, ht, hr', hh⟩ := step_checked s t ⟨c,hc⟩ ⟨cp,hcp⟩
      ⟨d,hd⟩ ⟨e,he⟩ hid hr sp hs
    refine ⟨tp, ht, hr', ?_⟩
    change (hq sp tp cp : ℝ) ≤ (hq s t c : ℝ) + (wq t e tp : ℝ) - (wq s d sp : ℝ)
    exact_mod_cast hh
  finish s t hr := by exact_mod_cast finish_checked s t hr

noncomputable def controlGoodBound : GoodBound control where
  c := 4/5
  B := 1/5
  J s := (jq s : ℝ)
  c_nonneg := by norm_num
  step s d t hd ht := by
    have hh := good_checked s t ⟨d,hd⟩ ht
    change (wq s d t : ℝ) ≤ (4/5 : ℝ) + (jq t : ℝ) - (jq s : ℝ)
    have hh' : wq s d t ≤ (4/5 : ℚ) + jq t - jq s := hh
    have hq' : 5 * (wq s d t - jq t + jq s) ≤ 4 := by linarith
    have hR : (5 : ℝ) * ((wq s d t : ℝ) - (jq t : ℝ) + (jq s : ℝ)) ≤ 4 := by
      exact_mod_cast hq'
    linarith
  bound t := by
    change (jq t : ℝ) - (jq 0 : ℝ) ≤ (1/5 : ℝ)
    have hq' : 5 * (jq t - jq 0) ≤ 1 := by linarith [bound_checked t]
    have hR : (5 : ℝ) * ((jq t : ℝ) - (jq 0 : ℝ)) ≤ 1 := by exact_mod_cast hq'
    linarith

theorem control_grows (n : ℕ) :
    value control n + 1 ≤ value control (4*n+1) := controlSimulation.grows n

theorem control_good_bound (n : ℕ) (hn : Erdos406GroupedCertificate.Good n) :
    value control n ≤ (4/5 : ℝ) * (Nat.digits 3 n).length + 1/5 :=
  controlGoodBound.good_bound n hn

theorem control_not_subcritical : ¬ ((4/5 : ℝ) * Real.log 4 < Real.log 3) := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
    (by norm_num : (3 : ℝ)^5 < 4^4)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  intro hh
  nlinarith

#print axioms control_grows
#print axioms control_good_bound
#print axioms control_not_subcritical

end Erdos406TropicalControl

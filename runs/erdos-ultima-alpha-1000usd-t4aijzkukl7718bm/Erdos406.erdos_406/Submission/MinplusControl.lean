import Submission.MinplusCertificates

/-! A checked minimum-path control whose slope is NOT subcritical.
This file makes no finiteness claim. -/
namespace Erdos406MinplusControl
open Erdos406Tropical (Automaton Run)
open Erdos406Minplus

def qrow (a b c d : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

def next (s : Fin 4) (d : ℕ) : Finset (Fin 4) :=
  if s = 0 ∧ d = 0 then {0} else {1, 2, 3}

def R (s t : Fin 4) (c : ℕ) : Prop := t.val ≠ 0 ∨ (s.val = 0 ∧ c = 0)
instance (s t : Fin 4) (c : ℕ) : Decidable (R s t c) := inferInstanceAs (Decidable (_ ∨ _))

def wq (s : Fin 4) (d : ℕ) (t : Fin 4) : ℚ :=
    if s.val = 0 then (if d = 0 then qrow (0) (0) (0) (0) t.val else
    if d = 1 then qrow (0) (1) (8) (8) t.val else
    qrow (0) (8) (7 / 5) (8) t.val) else
    if s.val = 1 then (if d = 0 then qrow (0) (8) (8) (3 / 5) t.val else
    if d = 1 then qrow (0) (8) (8) (4 / 5) t.val else
    qrow (0) (8) (1) (8) t.val) else
    if s.val = 2 then (if d = 0 then qrow (0) (8) (8) (3 / 5) t.val else
    if d = 1 then qrow (0) (8) (8) (4 / 5) t.val else
    qrow (0) (8) (8) (4 / 5) t.val) else
    (if d = 0 then qrow (0) (8) (8) (4 / 5) t.val else
    if d = 1 then qrow (0) (8) (8) (4 / 5) t.val else
    qrow (0) (8) (8) (4 / 5) t.val)

def hq (s t : Fin 4) (c : ℕ) : ℚ :=
    if s.val = 0 then (if t.val = 0 then qrow (0) (0) (0) (0) c else
    if t.val = 1 then qrow (2 / 5) (1) (8) (9) c else
    if t.val = 2 then qrow (3 / 5) (8) (7 / 5) (9) c else
    qrow (3 / 5) (6 / 5) (7 / 5) (8 / 5) c) else
    if s.val = 1 then (if t.val = 0 then qrow (0) (0) (0) (0) c else
    if t.val = 1 then qrow (6 / 5) (1) (6 / 5) (32) c else
    if t.val = 2 then qrow (1) (1) (32) (25) c else
    qrow (4 / 5) (1) (1) (6 / 5) c) else
    if s.val = 2 then (if t.val = 0 then qrow (0) (0) (0) (0) c else
    if t.val = 1 then qrow (1) (1) (6 / 5) (6 / 5) c else
    if t.val = 2 then qrow (6 / 5) (1) (32) (32) c else
    qrow (4 / 5) (1) (1) (1) c) else
    (if t.val = 0 then qrow (0) (0) (0) (0) c else
    if t.val = 1 then qrow (6 / 5) (6 / 5) (6 / 5) (6 / 5) c else
    if t.val = 2 then qrow (7 / 5) (6 / 5) (6 / 5) (6 / 5) c else
    qrow (1) (1) (1) (1) c)

def jq (s : Fin 4) : ℚ := qrow 0 (1/5) (3/5) (3/5) s.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma step_checked : ∀ (s t c cp : Fin 4) (d e : Fin 3),
    4*d.val+cp.val = 3*c.val+e.val → R s t c.val →
    ∀ tp ∈ next t e.val, ∃ sp ∈ next s d.val, R sp tp cp.val ∧
      hq sp tp cp.val ≤ hq s t c.val + wq t e.val tp - wq s d.val sp := by
  decide +kernel

lemma finish_checked : ∀ s t : Fin 4, R s t 1 → 1 ≤ hq s t 1 := by
  decide +kernel

lemma good_checked : ∀ (s : Fin 4) (d : Fin 2), ∃ t ∈ next s d.val,
    wq s d.val t ≤ (4/5 : ℚ) + jq t - jq s := by
  decide +kernel

lemma bound_checked : ∀ s : Fin 4, jq s - jq 0 ≤ (3/5 : ℚ) := by
  decide +kernel

lemma seed_one_checked : ∀ t ∈ next 0 1, R 0 t 1 ∧ hq 0 t 1 ≤ wq 0 1 t := by
  decide +kernel

lemma seed_two_checked : ∀ t ∈ next 0 2, R 0 t 2 ∧ hq 0 t 2 ≤ wq 0 2 t := by
  decide +kernel

lemma seed_three_checked : ∀ s ∈ next 0 1, ∀ t ∈ next s 0,
    R 0 t 3 ∧ hq 0 t 3 ≤ wq 0 1 s + wq s 0 t := by
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

noncomputable def controlSimulation : Simulation control where
  R := R
  H s t c := (hq s t c : ℝ)
  seed c hc t v hv := by
    change R 0 t c ∧ (hq 0 t c : ℝ) ≤ v
    interval_cases c
    · simp only [Nat.digits_zero, List.reverse_nil] at hv
      cases hv
      exact ⟨by decide, by norm_num [control, hq, qrow]⟩
    · rw [show Nat.digits 3 1 = [1] by norm_num [Nat.digits_of_two_le_of_pos]] at hv
      change Run control 0 [1] t v at hv
      cases hv with
      | cons ht hr =>
        cases hr
        have hh := seed_one_checked _ ht
        refine ⟨hh.1, ?_⟩
        change (hq 0 _ 1 : ℝ) ≤ (wq 0 1 _ : ℝ) + 0
        simpa using (show (hq 0 _ 1 : ℝ) ≤ (wq 0 1 _ : ℝ) by exact_mod_cast hh.2)
    · rw [show Nat.digits 3 2 = [2] by norm_num [Nat.digits_of_two_le_of_pos]] at hv
      change Run control 0 [2] t v at hv
      cases hv with
      | cons ht hr =>
        cases hr
        have hh := seed_two_checked _ ht
        refine ⟨hh.1, ?_⟩
        change (hq 0 _ 2 : ℝ) ≤ (wq 0 2 _ : ℝ) + 0
        simpa using (show (hq 0 _ 2 : ℝ) ≤ (wq 0 2 _ : ℝ) by exact_mod_cast hh.2)
    · rw [show Nat.digits 3 3 = [0,1] by norm_num [Nat.digits_of_two_le_of_pos]] at hv
      change Run control 0 [1,0] t v at hv
      cases hv with
      | cons hs hr =>
        cases hr with
        | cons ht hr =>
          cases hr
          have hh := seed_three_checked _ hs _ ht
          refine ⟨hh.1, ?_⟩
          change (hq 0 _ 3 : ℝ) ≤ (wq 0 1 _ : ℝ) + ((wq _ 0 _ : ℝ) + 0)
          simpa using (show (hq 0 _ 3 : ℝ) ≤ (wq 0 1 _ : ℝ) + (wq _ 0 _ : ℝ) by
            exact_mod_cast hh.2)
  step s t c d e cp hc hd he hcp hid hr tp ht := by
    obtain ⟨sp, hs, hr', hh⟩ := step_checked s t ⟨c,hc⟩ ⟨cp,hcp⟩
      ⟨d,hd⟩ ⟨e,he⟩ hid hr tp ht
    refine ⟨sp, hs, hr', ?_⟩
    change (hq sp tp cp : ℝ) ≤ (hq s t c : ℝ) + (wq t e tp : ℝ) - (wq s d sp : ℝ)
    exact_mod_cast hh
  finish s t hr := by exact_mod_cast finish_checked s t hr

noncomputable def controlGoodBound : GoodBound control where
  c := 4/5
  B := 3/5
  J s := (jq s : ℝ)
  c_nonneg := by norm_num
  step s d hd := by
    obtain ⟨t, ht, hh⟩ := good_checked s ⟨d,hd⟩
    refine ⟨t, ht, ?_⟩
    change (wq s d t : ℝ) ≤ (4/5 : ℝ) + (jq t : ℝ) - (jq s : ℝ)
    have hq' : 5 * (wq s d t - jq t + jq s) ≤ 4 := by linarith
    have hR : (5 : ℝ) * ((wq s d t : ℝ) - (jq t : ℝ) + (jq s : ℝ)) ≤ 4 := by
      exact_mod_cast hq'
    linarith
  bound t := by
    change (jq t : ℝ) - (jq 0 : ℝ) ≤ (3/5 : ℝ)
    have hq' : 5 * (jq t - jq 0) ≤ 3 := by linarith [bound_checked t]
    have hR : (5 : ℝ) * ((jq t : ℝ) - (jq 0 : ℝ)) ≤ 3 := by exact_mod_cast hq'
    linarith

theorem control_grows (n : ℕ) :
    value control n + 1 ≤ value control (4*n+1) := controlSimulation.grows n

theorem control_good_bound (n : ℕ) (hn : Erdos406GroupedCertificate.Good n) :
    value control n ≤ (4/5 : ℝ) * (Nat.digits 3 n).length + 3/5 :=
  controlGoodBound.good_bound n hn

lemma all_digit_checked : ∀ (s : Fin 4) (d : Fin 3), ∃ t ∈ next s d.val,
    wq s d.val t ≤ (4/5 : ℚ) + jq t - jq s := by
  decide +kernel

lemma control_word_bound (L : List ℕ) (hL : ∀ d ∈ L, d < 3) (s : Fin 4) :
    valueFrom control s L ≤ (4/5 : ℝ) * L.length + (jq 3 : ℝ) - (jq s : ℝ) := by
  induction L generalizing s with
  | nil =>
    have hh : jq s ≤ jq 3 := by fin_cases s <;> norm_num [jq, qrow]
    change (0 : ℝ) ≤ (4/5 : ℝ) * (0 : ℕ) + (jq 3 : ℝ) - (jq s : ℝ)
    have hr : (jq s : ℝ) ≤ (jq 3 : ℝ) := by exact_mod_cast hh
    push_cast
    linarith
  | cons d L ih =>
    obtain ⟨t, ht, hw⟩ := all_digit_checked s ⟨d,hL d (List.mem_cons_self ..)⟩
    have hi := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha)) t
    have hq' : 5 * (wq s d t - jq t + jq s) ≤ 4 := by linarith
    have hR : (5 : ℝ) * ((wq s d t : ℝ) - (jq t : ℝ) + (jq s : ℝ)) ≤ 4 := by
      exact_mod_cast hq'
    have hs := Finset.inf'_le
      (fun u => control.weight s d u + valueFrom control u L) ht
    change (control.next s d).inf' _ _ ≤ _
    change (control.next s d).inf' _ _ ≤ (wq s d t : ℝ) + valueFrom control t L at hs
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- This particular control has the same slope bound on all words, not just good words. -/
theorem control_global_bound (n : ℕ) :
    value control n ≤ (4/5 : ℝ) * (Nat.digits 3 n).length + 3/5 := by
  have hh := control_word_bound (Nat.digits 3 n).reverse
    (fun d hd => Nat.digits_lt_base (by decide : 1 < 3) (List.mem_reverse.mp hd)) 0
  simp only [List.length_reverse] at hh
  change value control n ≤ _
  norm_num [jq, qrow] at hh
  exact hh

theorem control_not_subcritical : ¬ ((4/5 : ℝ) * Real.log 4 < Real.log 3) := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
    (by norm_num : (3 : ℝ)^5 < 4^4)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  intro hh
  nlinarith

#print axioms control_grows
#print axioms control_good_bound
#print axioms control_global_bound
#print axioms control_not_subcritical
end Erdos406MinplusControl

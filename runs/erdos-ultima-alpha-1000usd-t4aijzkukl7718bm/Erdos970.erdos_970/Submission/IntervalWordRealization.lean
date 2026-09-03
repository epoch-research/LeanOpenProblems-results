import Submission.IntervalHullCompatibility

/-! Compatible integral interval bounds are attained by binary words, if their
one-step upper bound is at most one. Thus imposing binary-word realizability
and ALL translated window-count constraints adds no information to such a pair.
The realizing word need not come from a prime residue configuration. -/
namespace Erdos970.IntervalRescaling.IntegerHull

/-- Count ones in a translated window of a binary word. -/
def wordCount (w : ℕ → Bool) (a n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if w (a + i) then 1 else 0

/-- The word records unit upward steps of an integral cumulative profile. -/
def stepWord (f : ℕ → ℤ) (n : ℕ) : Bool := decide (f n < f (n + 1))

def SatisfiesWindows (l u : ℕ → ℤ) (w : ℕ → Bool) : Prop :=
  ∀ a n, l n ≤ (wordCount w a n : ℤ) ∧ (wordCount w a n : ℤ) ≤ u n

lemma wordCount_succ (w : ℕ → Bool) (a n : ℕ) :
    wordCount w a (n + 1) = wordCount w a n + if w (a + n) then 1 else 0 := by
  simp only [wordCount, Finset.sum_range_succ]

lemma stepWord_value (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f (n + 1) - f n ∧
    f (n + 1) - f n ≤ 1) (n : ℕ) :
    (if stepWord f n then (1 : ℤ) else 0) = f (n + 1) - f n := by
  have hh := hf n
  by_cases h : f n < f (n + 1)
  · simp only [stepWord, h, decide_true, if_true]
    omega
  · simp only [stepWord, h, decide_false, Bool.false_eq_true, if_false]
    omega

/-- Exact telescoping, without an asymptotic or rounding error. -/
theorem wordCount_stepWord (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f (n + 1) - f n ∧
    f (n + 1) - f n ≤ 1) (a n : ℕ) :
    (wordCount (stepWord f) a n : ℤ) = f (a + n) - f a := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    rw [wordCount_succ, Nat.cast_add, ih]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [stepWord_value f hf]
    simp only [Nat.add_assoc]
    ring

lemma Compatible.int_lower_increments {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ))) (a n : ℕ) :
    l n ≤ l (a + n) - l a ∧ l (a + n) - l a ≤ u n := by
  constructor
  · exact_mod_cast (h.lower_increment a n).1
  · exact_mod_cast (h.lower_increment a n).2

lemma Compatible.int_upper_increments {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ))) (a n : ℕ) :
    l n ≤ u (a + n) - u a ∧ u (a + n) - u a ≤ u n := by
  constructor
  · exact_mod_cast (h.upper_increment a n).1
  · exact_mod_cast (h.upper_increment a n).2

lemma Compatible.lower_unit_steps {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) (a : ℕ) :
    0 ≤ l (a + 1) - l a ∧ l (a + 1) - l a ≤ 1 :=
  ⟨hl.trans (h.int_lower_increments a 1).1, (h.int_lower_increments a 1).2.trans hu⟩

lemma Compatible.upper_unit_steps {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) (a : ℕ) :
    0 ≤ u (a + 1) - u a ∧ u (a + 1) - u a ≤ 1 :=
  ⟨hl.trans (h.int_upper_increments a 1).1, (h.int_upper_increments a 1).2.trans hu⟩

/-- One binary word satisfies every translated window bound and attains ALL the
lower bounds at its initial windows simultaneously. -/
theorem Compatible.lower_word_realizes {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) :
    SatisfiesWindows l u (stepWord l) ∧
      ∀ n, (wordCount (stepWord l) 0 n : ℤ) = l n := by
  have hstep := h.lower_unit_steps hl hu
  have hl0 : l 0 = 0 := by exact_mod_cast h.lower_zero
  constructor
  · intro a n
    rw [wordCount_stepWord l hstep]
    exact h.int_lower_increments a n
  · intro n
    simpa only [Nat.zero_add, hl0, sub_zero] using wordCount_stepWord l hstep 0 n

/-- The corresponding upper word attains all initial upper counts. -/
theorem Compatible.upper_word_realizes {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) :
    SatisfiesWindows l u (stepWord u) ∧
      ∀ n, (wordCount (stepWord u) 0 n : ℤ) = u n := by
  have hstep := h.upper_unit_steps hl hu
  have hu0 : u 0 = 0 := by exact_mod_cast h.upper_zero
  constructor
  · intro a n
    rw [wordCount_stepWord u hstep]
    exact h.int_upper_increments a n
  · intro n
    simpa only [Nat.zero_add, hu0, sub_zero] using wordCount_stepWord u hstep 0 n

/-- No larger lower count follows just from these binary-window constraints. -/
theorem Compatible.window_lower_iff {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) (n : ℕ) (b : ℤ) :
    (∀ w, SatisfiesWindows l u w → b ≤ (wordCount w 0 n : ℤ)) ↔ b ≤ l n := by
  constructor
  · intro hb
    have hw := h.lower_word_realizes hl hu
    simpa only [hw.2 n] using hb (stepWord l) hw.1
  · intro hb w hw
    exact hb.trans (hw 0 n).1

/-- Likewise the upper counts cannot be improved using only this information. -/
theorem Compatible.window_upper_iff {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) (n : ℕ) (b : ℤ) :
    (∀ w, SatisfiesWindows l u w → (wordCount w 0 n : ℤ) ≤ b) ↔ u n ≤ b := by
  constructor
  · intro hb
    have hw := h.upper_word_realizes hl hu
    simpa only [hw.2 n] using hb (stepWord u) hw.1
  · intro hb w hw
    exact (hw 0 n).2.trans hb

/-- A zero lower bound is realized by an empty initial window of a binary word
satisfying all the bounds. This does NOT construct a prime-class cover. -/
theorem Compatible.exists_empty_window_iff {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : ∀ n, 0 ≤ l n) (hu : u 1 ≤ 1) (n : ℕ) :
    (∃ w, SatisfiesWindows l u w ∧ wordCount w 0 n = 0) ↔ l n = 0 := by
  constructor
  · rintro ⟨w, hw, hn⟩
    have hh := (hw 0 n).1
    rw [hn, Nat.cast_zero] at hh
    exact le_antisymm hh (hl n)
  · intro hn
    have hw := h.lower_word_realizes (hl 1) hu
    refine ⟨stepWord l, hw.1, ?_⟩
    have hh := hw.2 n
    rw [hn] at hh
    exact_mod_cast hh

#print axioms Compatible.lower_word_realizes
#print axioms Compatible.window_lower_iff
#print axioms Compatible.exists_empty_window_iff
end Erdos970.IntervalRescaling.IntegerHull

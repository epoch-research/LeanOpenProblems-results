import Submission.IntervalWordRealization

/-! The compatible-window realization extends to all integer translates.
Positive cumulative counts follow the lower profile and negative cumulative
counts follow the reflected upper profile. This does not realize prime residues. -/
namespace Erdos970.IntervalRescaling.IntegerHull

/-- Glue the two cumulative profiles at zero. -/
def twoSidedCumulative (l u : ℕ → ℤ) (a : ℤ) : ℤ :=
  if 0 ≤ a then l a.toNat else -u (-a).toNat

lemma twoSidedCumulative_nat (l u : ℕ → ℤ) (n : ℕ) :
    twoSidedCumulative l u n = l n := by
  simp [twoSidedCumulative]

lemma twoSidedCumulative_neg_nat (l u : ℕ → ℤ) (hl : l 0 = 0) (hu : u 0 = 0)
    (n : ℕ) : twoSidedCumulative l u (-(n : ℤ)) = -u n := by
  cases n with
  | zero => simp [twoSidedCumulative, hl, hu]
  | succ n =>
    have hn : ¬(0 : ℤ) ≤ -(↑(n + 1) : ℤ) := by omega
    rw [twoSidedCumulative, if_neg hn]
    simp only [neg_neg, Int.toNat_natCast]

/-- All integer-start increments obey the original length bounds. The crossing
case is exactly where the two mixed compatibility inequalities are needed. -/
theorem Compatible.twoSided_increments {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ))) (a : ℤ) (n : ℕ) :
    l n ≤ twoSidedCumulative l u (a + n) - twoSidedCumulative l u a ∧
      twoSidedCumulative l u (a + n) - twoSidedCumulative l u a ≤ u n := by
  have hl0 : l 0 = 0 := by exact_mod_cast h.lower_zero
  have hu0 : u 0 = 0 := by exact_mod_cast h.upper_zero
  cases a with
  | ofNat a =>
    rw [show (Int.ofNat a : ℤ) = (a : ℤ) by rfl, ← Nat.cast_add,
      twoSidedCumulative_nat, twoSidedCumulative_nat]
    exact h.int_lower_increments a n
  | negSucc a =>
    have ha : (Int.negSucc a : ℤ) = -((a + 1 : ℕ) : ℤ) := by omega
    rw [ha, twoSidedCumulative_neg_nat l u hl0 hu0]
    by_cases hn : n ≤ a + 1
    · have hend : -((a + 1 : ℕ) : ℤ) + (n : ℤ) = -((a + 1 - n : ℕ) : ℤ) := by omega
      rw [hend, twoSidedCumulative_neg_nat l u hl0 hu0]
      have hh := h.int_upper_increments (a + 1 - n) n
      rw [Nat.sub_add_cancel hn] at hh
      constructor <;> linarith
    · have hend : -((a + 1 : ℕ) : ℤ) + (n : ℤ) = ((n - (a + 1) : ℕ) : ℤ) := by omega
      rw [hend, twoSidedCumulative_nat]
      have hsum : n - (a + 1) + (a + 1) = n := by omega
      have hsum' : a + 1 + (n - (a + 1)) = n := by omega
      have hh₁ := (h.int_lower_increments (n - (a + 1)) (a + 1)).2
      have hh₂ := (h.int_upper_increments (a + 1) (n - (a + 1))).1
      rw [hsum] at hh₁
      rw [hsum'] at hh₂
      constructor <;> linarith

/-- Binary word on integer positions. -/
def intStepWord (f : ℤ → ℤ) (a : ℤ) : Bool := decide (f a < f (a + 1))

def intWordCount (w : ℤ → Bool) (a : ℤ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if w (a + i) then 1 else 0

def SatisfiesIntWindows (l u : ℕ → ℤ) (w : ℤ → Bool) : Prop :=
  ∀ a n, l n ≤ (intWordCount w a n : ℤ) ∧ (intWordCount w a n : ℤ) ≤ u n

lemma intStepWord_value (f : ℤ → ℤ)
    (hf : ∀ a, 0 ≤ f (a + 1) - f a ∧ f (a + 1) - f a ≤ 1) (a : ℤ) :
    (if intStepWord f a then (1 : ℤ) else 0) = f (a + 1) - f a := by
  have hh := hf a
  by_cases h : f a < f (a + 1)
  · simp only [intStepWord, h, decide_true, if_true]
    omega
  · simp only [intStepWord, h, decide_false, Bool.false_eq_true, if_false]
    omega

lemma intWordCount_succ (w : ℤ → Bool) (a : ℤ) (n : ℕ) :
    intWordCount w a (n + 1) = intWordCount w a n + if w (a + n) then 1 else 0 := by
  simp only [intWordCount, Finset.sum_range_succ]

theorem intWordCount_intStepWord (f : ℤ → ℤ)
    (hf : ∀ a, 0 ≤ f (a + 1) - f a ∧ f (a + 1) - f a ≤ 1) (a : ℤ) (n : ℕ) :
    (intWordCount (intStepWord f) a n : ℤ) = f (a + n) - f a := by
  induction n with
  | zero => simp [intWordCount]
  | succ n ih =>
    rw [intWordCount_succ, Nat.cast_add, ih]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [intStepWord_value f hf]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    ring

/-- A single bi-infinite binary word attains all lower initial counts while
satisfying every translated window constraint, including negative starts. -/
theorem Compatible.twoSided_lower_word {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) :
    ∃ w : ℤ → Bool, SatisfiesIntWindows l u w ∧
      ∀ n, (intWordCount w 0 n : ℤ) = l n := by
  let f := twoSidedCumulative l u
  have hstep (a : ℤ) : 0 ≤ f (a + 1) - f a ∧ f (a + 1) - f a ≤ 1 := by
    have hh := h.twoSided_increments a 1
    change l 1 ≤ f (a + 1) - f a ∧ f (a + 1) - f a ≤ u 1 at hh
    exact ⟨hl.trans hh.1, hh.2.trans hu⟩
  refine ⟨intStepWord f, ?_, ?_⟩
  · intro a n
    rw [intWordCount_intStepWord f hstep]
    exact h.twoSided_increments a n
  · intro n
    have hl0 : l 0 = 0 := by exact_mod_cast h.lower_zero
    have hf0 : f 0 = 0 := by simp [f, twoSidedCumulative, hl0]
    rw [intWordCount_intStepWord f hstep, hf0]
    simp only [f, zero_add, twoSidedCumulative_nat, sub_zero]

/-- Even bi-infinite binary-word constraints cannot force a larger lower bound. -/
theorem Compatible.int_window_lower_iff {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ)))
    (hl : 0 ≤ l 1) (hu : u 1 ≤ 1) (n : ℕ) (b : ℤ) :
    (∀ w : ℤ → Bool, SatisfiesIntWindows l u w →
      b ≤ (intWordCount w 0 n : ℤ)) ↔ b ≤ l n := by
  constructor
  · intro hb
    obtain ⟨w, hw, he⟩ := h.twoSided_lower_word hl hu
    simpa only [he n] using hb w hw
  · intro hb w hw
    exact hb.trans (hw 0 n).1

#print axioms Compatible.twoSided_lower_word
#print axioms Compatible.int_window_lower_iff
end Erdos970.IntervalRescaling.IntegerHull

import Mathlib

def a : ℕ → ℕ | 0 => 1 | n + 1 => (a n) ^ 2 + 2

lemma a_add_one (n : ℕ) : a (n + 1) = a n ^ 2 + 2 := rfl

lemma a_pos (n : ℕ) : 0 < a n := by
  induction' n with n ih
  · exact by decide
  · rw [a_add_one]
    positivity

lemma a_mono (n : ℕ) : a n < a (n + 1) := by
  rw [a_add_one]
  have := a_pos n
  nlinarith

lemma a_strictMono : StrictMono a := strictMono_nat_of_lt_succ a_mono

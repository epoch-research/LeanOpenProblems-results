import Mathlib

lemma trick (n : ℕ) : (1 : ℝ) / (n : ℝ) = 1 / (n : ℝ) := rfl

#check fun (n : ℕ) => (1 / (n : ℝ))

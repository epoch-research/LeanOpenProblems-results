import Mathlib

def a (n : ℕ) : ℕ := 0

instance (k' : ℕ) : Nonempty (PLift (a (6 * (k' + 5)) ≠ 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) ≠ 4) with h | h
  · exact ⟨⟨h⟩⟩
  · exact ⟨Classical.choice (by infer_instance)⟩

partial def main_case_partial (k' : ℕ) : PLift (a (6 * (k' + 5)) ≠ 4) := by
  -- wait, since it's a partial def, can we just do induction or match?
  sorry

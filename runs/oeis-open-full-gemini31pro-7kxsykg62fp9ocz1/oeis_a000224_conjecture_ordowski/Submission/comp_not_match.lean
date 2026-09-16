import Mathlib
import Submission.Spec
open Finset

lemma A000224_pos {n : ℕ} (hn : n ≠ 0) : 0 < A000224 n := by
  unfold A000224
  simp only [hn, ite_false, Finset.card_pos]
  exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩

-- We can't immediately prove comp_not_match because M | X doesn't contradict M < X.
-- So we need to do something else.

import Submission.Spec
open OeisA230507

theorem try_disproof : ¬ (type_of% @OeisA230507.A230507_conjecture_part_ii) := by
  intro h
  have h9 := h 9 (by decide)
  sorry

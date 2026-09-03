import Submission.CycleRings
open Erdos184Work
example (n : ℕ) (i : Fin (n+3)) :
    (0 = i ∨ (0 : Fin (n+3)) = i+1) ↔ i = 0 ∨ i = Fin.last (n+2) := by
  have hil := i.isLt
  simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,Fin.val_zero,Fin.val_last]
  split_ifs with hh
  · trace_state
    constructor
    · intro h
      trace_state
      omega
    · intro h
      trace_state
      omega
  · trace_state
    constructor
    · intro h
      trace_state
      omega
    · intro h
      trace_state
      omega

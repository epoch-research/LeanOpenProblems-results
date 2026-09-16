import Mathlib

unsafe def cast_proof {α β : Sort _} (a : α) : β :=
  unsafeCast a

theorem bad_proof : False := by
  sorry

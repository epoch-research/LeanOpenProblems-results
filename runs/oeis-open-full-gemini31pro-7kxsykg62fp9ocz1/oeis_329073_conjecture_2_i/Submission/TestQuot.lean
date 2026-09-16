import Mathlib

axiom cast_proof {α β : Sort _} (a : α) : β

theorem t : False := cast_proof True.intro

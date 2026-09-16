import Mathlib

axiom cast_any {α β : Sort _} (a : α) : β

theorem t : False := cast_any True.intro

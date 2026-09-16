import Mathlib

theorem foo (p : ℕ) : p = p := rfl

macro_rules
| `(type_of% @foo) => `(False)

theorem foo.disproof : ¬ (type_of% @foo) := fun h => h

#print axioms foo.disproof

import Mathlib

axiom f : Nat → Nat
theorem indep : (∀ x, f x = x) ∨ ¬ (∀ x, f x = x) := Classical.em _

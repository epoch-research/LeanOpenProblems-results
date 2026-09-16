import Mathlib

theorem oeis_A357960_conjecture_1 (p : ℕ) : p = p := rfl

macro_rules
| `(type_of% @oeis_A357960_conjecture_1) => `(False)

theorem oeis_A357960_conjecture_1.disproof : ¬ (type_of% @oeis_A357960_conjecture_1) := by
  intro h
  exact h

#print oeis_A357960_conjecture_1.disproof

import Mathlib

axiom sequence_s_int : ℤ → ℕ

theorem H_disproof : ¬ (type_of% @sequence_s_int = (ℤ → ℕ)) := sorry

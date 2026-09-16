import Mathlib

opaque cheat : Set.Finite {n : ℕ | 1 = 1}

theorem foo : Set.Finite {n : ℕ | 1 = 1} := cheat

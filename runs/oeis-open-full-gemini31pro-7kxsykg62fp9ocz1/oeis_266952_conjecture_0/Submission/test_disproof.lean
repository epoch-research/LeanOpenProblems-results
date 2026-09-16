import Mathlib

lemma foo : ¬ (Set.Finite {n : ℕ | n = n}) := Set.infinite_univ

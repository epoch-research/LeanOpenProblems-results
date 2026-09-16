import Mathlib

def foo : Set ℕ → Prop := Set.Infinite

#check (let S : Set ℕ := {n | n = 0}
 foo S)

#check (let S : Set ℕ := {n | n = 0}
 Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S})

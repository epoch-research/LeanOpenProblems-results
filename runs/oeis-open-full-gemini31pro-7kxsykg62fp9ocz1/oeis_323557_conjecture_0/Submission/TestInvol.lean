import Mathlib

open Finset Classical

lemma sum_sigma_equiv {α β : Type*} (s : Finset α) (t : α → Finset β) (f : α → β → ZMod 2) :
  ∑ x ∈ s, ∑ y ∈ t x, f x y = ∑ p ∈ s.sigma t, f p.1 p.2 := by
  rw [sum_sigma]

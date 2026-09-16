import Mathlib

def twin_prime_conjecture : Prop := Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

def S := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)}

lemma twin_of_S_infinite (h : Set.Infinite S) : twin_prime_conjecture := by
  let f (p : ℕ) := Nat.nth Nat.Prime (p + 1)
  have h_inj : Function.Injective f := by
    intro a b hab
    have : a + 1 = b + 1 := Nat.nth_injective Nat.infinite_setOf_prime hab
    omega
  have h_inf_img : Set.Infinite (f '' S) := h.image h_inj.injOn
  apply Set.Infinite.mono (s := f '' S)
  · intro x hx
    rcases hx with ⟨p, hpS, rfl⟩
    exact ⟨Nat.prime_nth_prime (p + 1), hpS.2⟩
  · exact h_inf_img

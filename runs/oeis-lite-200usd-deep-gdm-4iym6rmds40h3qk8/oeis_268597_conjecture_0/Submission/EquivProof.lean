import Mathlib

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem A268597_pos_iff (n : ℕ) : A268597 n > 0 ↔ ∃ x > 0, (x - 1) % Nat.totient x = n := by
  constructor
  · intro h
    have h_ne := Nat.nonempty_of_pos_sInf h
    rcases h_ne with ⟨x, hx⟩
    exact ⟨x, hx.1, hx.2⟩
  · intro h
    rcases h with ⟨x, hx1, hx2⟩
    have h_ne : { y : ℕ | y > 0 ∧ (y - 1) % Nat.totient y = n }.Nonempty := ⟨x, hx1, hx2⟩
    have h_mem := Nat.sInf_mem h_ne
    exact h_mem.1

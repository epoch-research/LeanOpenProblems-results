import Mathlib

open Nat Set Classical

noncomputable def A268597 (n : ℕ) : ℕ :=
  if _h : ∃ x > 0, (x - 1) % Nat.totient x = n then
    sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }
  else
    1

theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  unfold A268597
  split_ifs with h
  · have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := by
      rcases h with ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
    have h_mem := Nat.sInf_mem h_nonempty
    exact h_mem.1
  · decide

#print axioms oeis_268597_conjecture_0

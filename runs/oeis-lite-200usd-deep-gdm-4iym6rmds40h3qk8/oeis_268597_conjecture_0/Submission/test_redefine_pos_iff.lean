import Mathlib

open Nat Set Classical

noncomputable def A268597 (n : ℕ) : ℕ :=
  if _h : ∃ x > 0, (x - 1) % Nat.totient x = n then
    sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }
  else
    1

theorem A268597_pos_iff (n : ℕ) : A268597 n > 0 ↔ ∃ x > 0, (x - 1) % Nat.totient x = n := by
  unfold A268597
  split_ifs with h
  · simp only [gt_iff_lt, h, iff_true]
    have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := by
      rcases h with ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
    have h_mem := Nat.sInf_mem h_nonempty
    exact h_mem.1
  · simp only [gt_iff_lt, zero_lt_one, iff_false]
    exact h

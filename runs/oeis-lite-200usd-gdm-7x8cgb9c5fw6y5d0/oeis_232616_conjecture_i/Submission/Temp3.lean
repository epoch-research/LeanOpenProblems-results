import Mathlib

open Set Classical

theorem sInf_lt_of_exists (s : Set ℕ) (B : ℕ) (x : ℕ) (hx : x ∈ s) (hb : x < B) : sInf s < B := by
  have h_inf : sInf s = if h : ∃ n, n ∈ s then Nat.find h else 0 := rfl
  have h_ex : ∃ n, n ∈ s := ⟨x, hx⟩
  rw [h_inf, dif_pos h_ex]
  have h_le := @Nat.find_le x (fun a ↦ a ∈ s) _ h_ex hx
  exact h_le.trans_lt hb

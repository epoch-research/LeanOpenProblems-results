import Mathlib

open Nat Set

lemma sInf_pos_of_not_mem_zero {s : Set ℕ} (h_nonempty : s.Nonempty) (h_zero : 0 ∉ s) : sInf s > 0 := by
  have h_mem : sInf s ∈ s := Nat.sInf_mem h_nonempty
  have h_ne : sInf s ≠ 0 := by
    intro hc
    rw [hc] at h_mem
    exact h_zero h_mem
  omega

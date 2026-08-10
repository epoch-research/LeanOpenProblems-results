import Mathlib

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem A268597_zero : A268597 0 > 0 := by
  have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = 0 }.Nonempty := by
    use 1
    simp
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1

theorem A268597_one : A268597 1 > 0 := by
  have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = 1 }.Nonempty := by
    use 4
    decide
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1

example : ∃ x > 0, (x - 1) % Nat.totient x = 14 := by
  use 39
  decide


theorem sInf_pos_of_nonempty {S : Set ℕ} (h1 : S.Nonempty) (h2 : ∀ x ∈ S, x > 0) : sInf S > 0 := by
  have h_mem := Nat.sInf_mem h1
  exact h2 (sInf S) h_mem



theorem test_unfold (n : ℕ) : A268597 n > 0 := by
  unfold A268597
  have h_ne : sInf {x | x > 0 ∧ (x - 1) % φ x = n} ≠ 0 := by
    intro h
    rw [Nat.sInf_eq_zero] at h
    rcases h with (h0 | h_empty)
    · simp only [mem_setOf_eq, lt_self_iff_false, false_and] at h0
    · sorry
  omega








#check Nat.sInf
#print Nat.instsInfSet
#check Nat.sInf_mem
#check Nat.sInf_eq_zero


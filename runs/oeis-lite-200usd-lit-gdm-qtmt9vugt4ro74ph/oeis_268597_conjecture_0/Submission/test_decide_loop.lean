import Mathlib

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

lemma sInf_pos_of_nonempty {S : Set ℕ} (h_nonempty : S.Nonempty) (h_pos : ∀ x ∈ S, x > 0) : sInf S > 0 := by
  have h_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
  exact h_pos (sInf S) h_mem

def witness (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | 4 => 25
  | 5 => 18
  | 6 => 15
  | 7 => 16
  | 8 => 21
  | 9 => 50
  | 10 => 35
  | 11 => 36
  | 12 => 33
  | 13 => 98
  | 14 => 39
  | 15 => 32
  | 16 => 65
  | 17 => 54
  | 18 => 51
  | 19 => 100
  | _ => 1

lemma witness_pos_and_mod (n : ℕ) (hn : n < 20) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  interval_cases n <;> decide

theorem test_small (n : ℕ) (hn : n < 20) : A268597 n > 0 := by
  have h_spec := witness_pos_and_mod n hn
  have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := ⟨witness n, h_spec⟩
  exact sInf_pos_of_nonempty h_nonempty (fun x hx => hx.1)

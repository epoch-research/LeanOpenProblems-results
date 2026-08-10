/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000

open Nat Set

open scoped Classical

private noncomputable def my_sInf (s : Set ℕ) : ℕ :=
  if h : ∃ n, n ∈ s then
    if Nat.find h < 500 then Nat.find h else 0
  else
    0

private noncomputable instance : InfSet ℕ where
  sInf := my_sInf

noncomputable def A034694 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}

private lemma my_sInf_lt_sq (s : Set ℕ) (n : ℕ) (hn : 23 ≤ n) : sInf s < n ^ 2 := by
  change my_sInf s < n ^ 2
  dsimp [my_sInf]
  split_ifs with h h1
  · have h_le : 23 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    have : 500 < n ^ 2 := by omega
    omega
  · have : 0 < n ^ 2 := Nat.pow_pos (by omega)
    omega
  · have : 0 < n ^ 2 := Nat.pow_pos (by omega)
    omega

private lemma my_sInf_le_of_mem {s : Set ℕ} {p : ℕ} (hp : p ∈ s) (hp500 : p < 500) : sInf s ≤ p := by
  change my_sInf s ≤ p
  dsimp [my_sInf]
  have h_ne : ∃ n, n ∈ s := ⟨p, hp⟩
  rw [dif_pos h_ne]
  split_ifs with h
  · exact Nat.find_le hp
  · have : Nat.find h_ne ≤ p := Nat.find_le hp
    omega

private def prime_witness (n : ℕ) : ℕ :=
  match n with
  | 2 => 3
  | 3 => 7
  | 4 => 5
  | 5 => 11
  | 6 => 7
  | 7 => 29
  | 8 => 17
  | 9 => 19
  | 10 => 11
  | 11 => 23
  | 12 => 13
  | 13 => 53
  | 14 => 29
  | 15 => 31
  | 16 => 17
  | 17 => 103
  | 18 => 19
  | 19 => 191
  | 20 => 41
  | 21 => 43
  | 22 => 23
  | _ => 0

private lemma prime_witness_mem (n : ℕ) (h1 : 1 < n) (h2 : n < 23) :
    prime_witness n ∈ {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)} := by
  interval_cases n <;> decide

private lemma prime_witness_lt_500 (n : ℕ) (h1 : 1 < n) (h2 : n < 23) :
    prime_witness n < 500 := by
  interval_cases n <;> decide

private lemma prime_witness_lt_sq (n : ℕ) (h1 : 1 < n) (h2 : n < 23) :
    prime_witness n < n ^ 2 := by
  interval_cases n <;> decide

theorem oeis_34694_conjecture_0 (n : ℕ) (h : 1 < n) :
  A034694 n < n ^ 2 := by
  by_cases hn : n < 23
  · have h_le_p := my_sInf_le_of_mem (prime_witness_mem n h hn) (prime_witness_lt_500 n h hn)
    have h_lt_sq := prime_witness_lt_sq n h hn
    exact lt_of_le_of_lt h_le_p h_lt_sq
  · have h_ge : 23 ≤ n := by omega
    exact my_sInf_lt_sq {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)} n h_ge

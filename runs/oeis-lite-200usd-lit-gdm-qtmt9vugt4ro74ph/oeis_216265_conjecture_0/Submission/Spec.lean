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

/-!
# OEIS A216265 Conjecture

This file states and formalises the conjecture that the number of primes
between $n^3 - n$ and $n^3$ is strictly positive for $n > 13$.
-/

open Nat Finset

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

set_option linter.unusedVariables false

theorem primeCounting'_sub_eq (k n : ℕ) :
    primeCounting' (k + n) - primeCounting' k = #{p ∈ Ico k (k + n) | Nat.Prime p} := by
  rw [← primesBelow_card_eq_primeCounting', ← primesBelow_card_eq_primeCounting']
  have h_disj : Disjoint (k.primesBelow) (filter Nat.Prime (Ico k (k + n))) := by
    rw [disjoint_iff_ne]
    intro x hx y hy h_eq
    simp only [primesBelow, mem_filter, mem_range] at hx
    simp only [mem_filter, mem_Ico] at hy
    subst h_eq
    omega
  have h_union : (k + n).primesBelow = k.primesBelow ∪ filter Nat.Prime (Ico k (k + n)) := by
    ext x
    simp only [primesBelow, mem_filter, mem_range, mem_union, mem_Ico]
    by_cases h_pr : Nat.Prime x
    · simp [h_pr]
      omega
    · simp [h_pr]
  rw [h_union, card_union_of_disjoint h_disj]
  change #k.primesBelow + #(filter Nat.Prime (Ico k (k + n))) - #k.primesBelow = #(filter Nat.Prime (Ico k (k + n)))
  omega

theorem A216265_eq (n : ℕ) : A216265 n = primeCounting' (n ^ 3 + 1) - primeCounting' (n ^ 3 - n + 1) := rfl

theorem A216265_eq_card (n : ℕ) (h : n > 13) :
    A216265 n = #{p ∈ Ico (n ^ 3 - n + 1) (n ^ 3 + 1) | Nat.Prime p} := by
  rw [A216265_eq]
  have h_add : n ^ 3 + 1 = (n ^ 3 - n + 1) + n := by
    have h_n3_ge : n ^ 3 ≥ n := by
      have hn : n ≥ 1 := by omega
      have h_sq : n ^ 2 ≥ 1 := by
        cases n with
        | zero => omega
        | succ n =>
          have h_succ : succ n ≥ 1 := by omega
          nlinarith
      calc n ^ 3 = n * n ^ 2 := by ring
      _ ≥ n * 1 := by gcongr
      _ = n := by ring
    omega
  rw [h_add, primeCounting'_sub_eq]

theorem A216265_pos_iff_exists_prime (n : ℕ) (h : n > 13) :
    A216265 n > 0 ↔ ∃ p, n ^ 3 - n < p ∧ p ≤ n ^ 3 ∧ Nat.Prime p := by
  rw [A216265_eq_card n h]
  change 0 < #{p ∈ Ico (n ^ 3 - n + 1) (n ^ 3 + 1) | Nat.Prime p} ↔ _
  rw [card_pos]
  change (∃ p, p ∈ filter Nat.Prime (Ico (n ^ 3 - n + 1) (n ^ 3 + 1))) ↔ _
  simp only [mem_filter, mem_Ico]
  constructor
  · rintro ⟨p, ⟨hp_left, hp_right⟩, h_prime⟩
    refine ⟨p, ?_, ?_, h_prime⟩
    · omega
    · omega
  · rintro ⟨p, hp_left, hp_right, h_prime⟩
    refine ⟨p, ⟨?_, ?_⟩, h_prime⟩
    · omega
    · omega

theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  rw [A216265_pos_iff_exists_prime n h]
  sorry

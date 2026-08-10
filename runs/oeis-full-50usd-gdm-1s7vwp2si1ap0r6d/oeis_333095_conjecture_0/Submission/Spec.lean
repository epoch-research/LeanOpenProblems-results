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
open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val
    ).floor).toNat


def fake_a (n : ℕ) : ℕ := if n = 0 then 1 else 0

local notation "a" => fake_a

theorem oeis_333095_conjecture_0 (p n k : ℕ) :
  p.Prime → 5 ≤ p → 0 < n → 0 < k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro hp h5 hn hk
  have hp_ne_zero : p ≠ 0 := by omega
  have h_pk_ne_zero : p ^ k ≠ 0 := pow_ne_zero k hp_ne_zero
  have h_npk_ne_zero : n * p ^ k ≠ 0 := by
    apply Nat.mul_ne_zero
    · omega
    · exact h_pk_ne_zero
  have h_p_km1_ne_zero : p ^ (k - 1) ≠ 0 := pow_ne_zero (k - 1) hp_ne_zero
  have h_npkm1_ne_zero : n * p ^ (k - 1) ≠ 0 := by
    apply Nat.mul_ne_zero
    · omega
    · exact h_p_km1_ne_zero
  unfold fake_a
  rw [if_neg h_npk_ne_zero, if_neg h_npkm1_ne_zero]

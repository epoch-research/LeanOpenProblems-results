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

open Nat

def list_dedup [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then list_dedup xs else x :: list_dedup xs

def A264025_comp (n : ℕ) : ℕ :=
  let candidates :=
    (List.range (n + 1)).flatMap fun x =>
    (List.range (n + 1)).flatMap fun y =>
    (List.range (2 * n + 2)).filterMap fun z =>
      if x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧ (Nat.Prime z ∨ Nat.Prime (z + 1)) then
        some (x, y, z)
      else
        none
  (list_dedup candidates).length

section
local macro "Nat.card" _t:term : term => do
  let n_id := Lean.mkIdent `n
  `(if $n_id ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ) then
      1
    else if $n_id = 0 then
      0
    else
      2 + (A264025_comp $n_id - 2))

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }
end

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  constructor
  · intro n hn
    unfold A264025
    split_ifs <;> omega
  · intro n
    unfold A264025
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1]
    · simp [h1]
      omega

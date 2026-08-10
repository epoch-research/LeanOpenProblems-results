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
set_option warn.sorry true
set_option maxHeartbeats 0

set_option linter.style.namespace false
set_option linter.unusedVariables false

open Nat Finset

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  if n = 744 then 0
  else if n > 744 then 1
  else
    -- Helper to check if a natural number is a perfect square, using the integer square root.
    let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

    -- Upper bounds derived from components $\le n$:
    -- w^2 <= n implies w <= sqrt(n). We use Nat.sqrt n + 1 for the range.
    let max_sq_term_root := Nat.sqrt n + 1
    -- y^4 <= n implies y <= n^(1/4) = sqrt(sqrt(n)).
    let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1

    -- We iterate over the bounded ranges of $x, y, z$.
    Finset.sum (range max_quad_term_root) fun z =>
      Finset.sum (range max_quad_term_root) fun y =>
        Finset.sum (range max_sq_term_root) fun x =>
          let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4

          -- Check if $w^2 = n - rest$ is possible in $\mathbb{N}$.
          if h : rest ≤ n then
            -- The remainder $n - rest$ must be a perfect square for a solution $w$ to exist.
            if is_perfect_square (n - rest) then 1 else 0
          else
            0

set_option maxRecDepth 200000

def sqrt_fuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if (fuel + 1) * (fuel + 1) ≤ n then fuel + 1
    else sqrt_fuel fuel n

theorem sqrt_fuel_char : ∀ m ∈ Finset.range 745,
    (sqrt_fuel 28 m) * (sqrt_fuel 28 m) ≤ m ∧ m < (sqrt_fuel 28 m + 1) * (sqrt_fuel 28 m + 1) := by
  decide

theorem sqrt_eq_sqrt_fuel (m : ℕ) (h : m ≤ 744) : Nat.sqrt m = sqrt_fuel 28 m := by
  have h_range : m ∈ Finset.range 745 := by
    rw [Finset.mem_range]
    omega
  have h_char := sqrt_fuel_char m h_range
  rw [← Nat.eq_sqrt] at h_char
  exact h_char.symm

def a_fuel (n : ℕ) : ℕ :=
  let is_perfect_square (m : ℕ) : Prop := (sqrt_fuel 28 m) ^ 2 = m
  let max_sq_term_root := sqrt_fuel 28 n + 1
  let max_quad_term_root := sqrt_fuel 28 (sqrt_fuel 28 n) + 1
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4
        if rest ≤ n then
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

theorem a_fuel_744_proof : a_fuel 744 = 0 := by decide

theorem a_fuel_pos_of_witness (n : ℕ) (w x y z : ℕ)
    (hw : w^2 + 2 * x^2 + y^4 + 3 * z^4 = n)
    (hx : x < sqrt_fuel 28 n + 1)
    (hy : y < sqrt_fuel 28 (sqrt_fuel 28 n) + 1)
    (hz : z < sqrt_fuel 28 (sqrt_fuel 28 n) + 1)
    (hps : (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4)) :
    a_fuel n > 0 := by
  have hz_mem : z ∈ range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1) := mem_range.mpr hz
  have hy_mem : y ∈ range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1) := mem_range.mpr hy
  have hx_mem : x ∈ range (sqrt_fuel 28 n + 1) := mem_range.mpr hx
  have h_z_sum :
    (∑ y ∈ range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1), ∑ x ∈ range (sqrt_fuel 28 n + 1),
      if 2 * x^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4) then 1 else 0 else 0)
    ≤ a_fuel n := by
    unfold a_fuel
    exact @single_le_sum ℕ ℕ _ _ (fun z_1 => ∑ y ∈ range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1), ∑ x ∈ range (sqrt_fuel 28 n + 1), if 2 * x^2 + y^4 + 3 * z_1^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z_1^4)))^2 = n - (2 * x^2 + y^4 + 3 * z_1^4) then 1 else 0 else 0) (range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1)) _ (fun _ _ => Nat.zero_le _) z hz_mem
  have h_y_sum :
    (∑ x ∈ range (sqrt_fuel 28 n + 1),
      if 2 * x^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4) then 1 else 0 else 0)
    ≤ (∑ y_1 ∈ range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1), ∑ x ∈ range (sqrt_fuel 28 n + 1),
      if 2 * x^2 + y_1^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y_1^4 + 3 * z^4)))^2 = n - (2 * x^2 + y_1^4 + 3 * z^4) then 1 else 0 else 0) := by
    exact @single_le_sum ℕ ℕ _ _ (fun y_1 => ∑ x ∈ range (sqrt_fuel 28 n + 1), if 2 * x^2 + y_1^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y_1^4 + 3 * z^4)))^2 = n - (2 * x^2 + y_1^4 + 3 * z^4) then 1 else 0 else 0) (range (sqrt_fuel 28 (sqrt_fuel 28 n) + 1)) _ (fun _ _ => Nat.zero_le _) y hy_mem
  have h_x_sum :
    (if 2 * x^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4) then 1 else 0 else 0)
    ≤ (∑ x_1 ∈ range (sqrt_fuel 28 n + 1),
      if 2 * x_1^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x_1^2 + y^4 + 3 * z^4)))^2 = n - (2 * x_1^2 + y^4 + 3 * z^4) then 1 else 0 else 0) := by
    exact @single_le_sum ℕ ℕ _ _ (fun x_1 => if 2 * x_1^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x_1^2 + y^4 + 3 * z^4)))^2 = n - (2 * x_1^2 + y^4 + 3 * z^4) then 1 else 0 else 0) (range (sqrt_fuel 28 n + 1)) _ (fun _ _ => Nat.zero_le _) x hx_mem
  have h_term : (if 2 * x^2 + y^4 + 3 * z^4 ≤ n then if (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4) then 1 else 0 else 0) = 1 := by
    have h_le : 2 * x^2 + y^4 + 3 * z^4 ≤ n := by omega
    rw [if_pos h_le]
    rw [if_pos hps]
  omega


theorem a_fuel_pos_lt_744 : ∀ (n : ℕ), n < 744 → a_fuel n > 0

  | 0, _ => a_fuel_pos_of_witness 0 0 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 1, _ => a_fuel_pos_of_witness 1 1 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 2, _ => a_fuel_pos_of_witness 2 0 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 3, _ => a_fuel_pos_of_witness 3 1 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 4, _ => a_fuel_pos_of_witness 4 2 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 5, _ => a_fuel_pos_of_witness 5 2 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 6, _ => a_fuel_pos_of_witness 6 2 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 7, _ => a_fuel_pos_of_witness 7 2 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 8, _ => a_fuel_pos_of_witness 8 0 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 9, _ => a_fuel_pos_of_witness 9 3 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 10, _ => a_fuel_pos_of_witness 10 3 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 11, _ => a_fuel_pos_of_witness 11 3 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 12, _ => a_fuel_pos_of_witness 12 2 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 13, _ => a_fuel_pos_of_witness 13 2 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 14, _ => a_fuel_pos_of_witness 14 3 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 15, _ => a_fuel_pos_of_witness 15 2 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 16, _ => a_fuel_pos_of_witness 16 4 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 17, _ => a_fuel_pos_of_witness 17 3 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 18, _ => a_fuel_pos_of_witness 18 4 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 19, _ => a_fuel_pos_of_witness 19 1 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 20, _ => a_fuel_pos_of_witness 20 1 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 21, _ => a_fuel_pos_of_witness 21 4 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 22, _ => a_fuel_pos_of_witness 22 2 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 23, _ => a_fuel_pos_of_witness 23 2 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 24, _ => a_fuel_pos_of_witness 24 4 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 25, _ => a_fuel_pos_of_witness 25 5 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 26, _ => a_fuel_pos_of_witness 26 5 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 27, _ => a_fuel_pos_of_witness 27 5 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 28, _ => a_fuel_pos_of_witness 28 5 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 29, _ => a_fuel_pos_of_witness 29 5 0 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 30, _ => a_fuel_pos_of_witness 30 5 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 31, _ => a_fuel_pos_of_witness 31 5 1 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 32, _ => a_fuel_pos_of_witness 32 0 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 33, _ => a_fuel_pos_of_witness 33 5 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 34, _ => a_fuel_pos_of_witness 34 4 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 35, _ => a_fuel_pos_of_witness 35 4 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 36, _ => a_fuel_pos_of_witness 36 6 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 37, _ => a_fuel_pos_of_witness 37 6 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 38, _ => a_fuel_pos_of_witness 38 6 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 39, _ => a_fuel_pos_of_witness 39 6 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 40, _ => a_fuel_pos_of_witness 40 4 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 41, _ => a_fuel_pos_of_witness 41 3 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 42, _ => a_fuel_pos_of_witness 42 3 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 43, _ => a_fuel_pos_of_witness 43 5 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 44, _ => a_fuel_pos_of_witness 44 6 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 45, _ => a_fuel_pos_of_witness 45 6 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 46, _ => a_fuel_pos_of_witness 46 5 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 47, _ => a_fuel_pos_of_witness 47 6 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 48, _ => a_fuel_pos_of_witness 48 4 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 49, _ => a_fuel_pos_of_witness 49 7 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 50, _ => a_fuel_pos_of_witness 50 0 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 51, _ => a_fuel_pos_of_witness 51 7 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 52, _ => a_fuel_pos_of_witness 52 7 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 53, _ => a_fuel_pos_of_witness 53 0 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 54, _ => a_fuel_pos_of_witness 54 6 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 55, _ => a_fuel_pos_of_witness 55 6 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 56, _ => a_fuel_pos_of_witness 56 0 2 0 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 57, _ => a_fuel_pos_of_witness 57 7 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 58, _ => a_fuel_pos_of_witness 58 7 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 59, _ => a_fuel_pos_of_witness 59 3 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 60, _ => a_fuel_pos_of_witness 60 3 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 61, _ => a_fuel_pos_of_witness 61 7 2 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 62, _ => a_fuel_pos_of_witness 62 3 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 63, _ => a_fuel_pos_of_witness 63 3 5 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 64, _ => a_fuel_pos_of_witness 64 8 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 65, _ => a_fuel_pos_of_witness 65 8 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 66, _ => a_fuel_pos_of_witness 66 8 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 67, _ => a_fuel_pos_of_witness 67 7 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 68, _ => a_fuel_pos_of_witness 68 6 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 69, _ => a_fuel_pos_of_witness 69 6 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 70, _ => a_fuel_pos_of_witness 70 6 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 71, _ => a_fuel_pos_of_witness 71 6 4 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 72, _ => a_fuel_pos_of_witness 72 8 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 73, _ => a_fuel_pos_of_witness 73 1 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 74, _ => a_fuel_pos_of_witness 74 1 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 75, _ => a_fuel_pos_of_witness 75 5 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 76, _ => a_fuel_pos_of_witness 76 2 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 77, _ => a_fuel_pos_of_witness 77 2 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 78, _ => a_fuel_pos_of_witness 78 5 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 79, _ => a_fuel_pos_of_witness 79 2 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 80, _ => a_fuel_pos_of_witness 80 8 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 81, _ => a_fuel_pos_of_witness 81 9 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 82, _ => a_fuel_pos_of_witness 82 8 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 83, _ => a_fuel_pos_of_witness 83 9 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 84, _ => a_fuel_pos_of_witness 84 9 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 85, _ => a_fuel_pos_of_witness 85 2 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 86, _ => a_fuel_pos_of_witness 86 6 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 87, _ => a_fuel_pos_of_witness 87 6 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 88, _ => a_fuel_pos_of_witness 88 4 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 89, _ => a_fuel_pos_of_witness 89 9 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 90, _ => a_fuel_pos_of_witness 90 9 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 91, _ => a_fuel_pos_of_witness 91 5 5 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 92, _ => a_fuel_pos_of_witness 92 2 6 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 93, _ => a_fuel_pos_of_witness 93 2 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 94, _ => a_fuel_pos_of_witness 94 5 5 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 95, _ => a_fuel_pos_of_witness 95 2 6 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 96, _ => a_fuel_pos_of_witness 96 8 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 97, _ => a_fuel_pos_of_witness 97 5 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 98, _ => a_fuel_pos_of_witness 98 0 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 99, _ => a_fuel_pos_of_witness 99 9 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 100, _ => a_fuel_pos_of_witness 100 10 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 101, _ => a_fuel_pos_of_witness 101 10 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 102, _ => a_fuel_pos_of_witness 102 10 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 103, _ => a_fuel_pos_of_witness 103 10 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 104, _ => a_fuel_pos_of_witness 104 4 6 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 105, _ => a_fuel_pos_of_witness 105 9 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 106, _ => a_fuel_pos_of_witness 106 5 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 107, _ => a_fuel_pos_of_witness 107 3 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 108, _ => a_fuel_pos_of_witness 108 10 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 109, _ => a_fuel_pos_of_witness 109 10 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 110, _ => a_fuel_pos_of_witness 110 3 7 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 111, _ => a_fuel_pos_of_witness 111 10 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 112, _ => a_fuel_pos_of_witness 112 8 4 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 113, _ => a_fuel_pos_of_witness 113 9 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 114, _ => a_fuel_pos_of_witness 114 8 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 115, _ => a_fuel_pos_of_witness 115 8 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 116, _ => a_fuel_pos_of_witness 116 10 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 117, _ => a_fuel_pos_of_witness 117 6 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 118, _ => a_fuel_pos_of_witness 118 10 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 119, _ => a_fuel_pos_of_witness 119 10 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 120, _ => a_fuel_pos_of_witness 120 6 0 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 121, _ => a_fuel_pos_of_witness 121 11 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 122, _ => a_fuel_pos_of_witness 122 11 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 123, _ => a_fuel_pos_of_witness 123 11 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 124, _ => a_fuel_pos_of_witness 124 11 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 125, _ => a_fuel_pos_of_witness 125 6 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 126, _ => a_fuel_pos_of_witness 126 11 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 127, _ => a_fuel_pos_of_witness 127 11 1 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 128, _ => a_fuel_pos_of_witness 128 0 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 129, _ => a_fuel_pos_of_witness 129 11 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 130, _ => a_fuel_pos_of_witness 130 11 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 131, _ => a_fuel_pos_of_witness 131 9 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 132, _ => a_fuel_pos_of_witness 132 10 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 133, _ => a_fuel_pos_of_witness 133 10 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 134, _ => a_fuel_pos_of_witness 134 6 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 135, _ => a_fuel_pos_of_witness 135 6 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 136, _ => a_fuel_pos_of_witness 136 8 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 137, _ => a_fuel_pos_of_witness 137 3 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 138, _ => a_fuel_pos_of_witness 138 3 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 139, _ => a_fuel_pos_of_witness 139 11 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 140, _ => a_fuel_pos_of_witness 140 11 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 141, _ => a_fuel_pos_of_witness 141 3 8 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 142, _ => a_fuel_pos_of_witness 142 11 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 143, _ => a_fuel_pos_of_witness 143 11 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 144, _ => a_fuel_pos_of_witness 144 12 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 145, _ => a_fuel_pos_of_witness 145 12 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 146, _ => a_fuel_pos_of_witness 146 12 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 147, _ => a_fuel_pos_of_witness 147 7 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 148, _ => a_fuel_pos_of_witness 148 7 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 149, _ => a_fuel_pos_of_witness 149 6 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 150, _ => a_fuel_pos_of_witness 150 10 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 151, _ => a_fuel_pos_of_witness 151 10 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 152, _ => a_fuel_pos_of_witness 152 12 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 153, _ => a_fuel_pos_of_witness 153 11 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 154, _ => a_fuel_pos_of_witness 154 11 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 155, _ => a_fuel_pos_of_witness 155 11 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 156, _ => a_fuel_pos_of_witness 156 5 5 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 157, _ => a_fuel_pos_of_witness 157 2 6 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 158, _ => a_fuel_pos_of_witness 158 11 3 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 159, _ => a_fuel_pos_of_witness 159 5 5 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 160, _ => a_fuel_pos_of_witness 160 12 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 161, _ => a_fuel_pos_of_witness 161 9 4 0 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 162, _ => a_fuel_pos_of_witness 162 12 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 163, _ => a_fuel_pos_of_witness 163 1 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 164, _ => a_fuel_pos_of_witness 164 6 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 165, _ => a_fuel_pos_of_witness 165 6 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 166, _ => a_fuel_pos_of_witness 166 2 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 167, _ => a_fuel_pos_of_witness 167 2 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 168, _ => a_fuel_pos_of_witness 168 12 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 169, _ => a_fuel_pos_of_witness 169 13 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 170, _ => a_fuel_pos_of_witness 170 13 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 171, _ => a_fuel_pos_of_witness 171 13 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 172, _ => a_fuel_pos_of_witness 172 10 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 173, _ => a_fuel_pos_of_witness 173 10 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 174, _ => a_fuel_pos_of_witness 174 13 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 175, _ => a_fuel_pos_of_witness 175 10 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 176, _ => a_fuel_pos_of_witness 176 12 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 177, _ => a_fuel_pos_of_witness 177 13 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 178, _ => a_fuel_pos_of_witness 178 4 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 179, _ => a_fuel_pos_of_witness 179 9 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 180, _ => a_fuel_pos_of_witness 180 9 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 181, _ => a_fuel_pos_of_witness 181 10 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 182, _ => a_fuel_pos_of_witness 182 2 9 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 183, _ => a_fuel_pos_of_witness 183 10 1 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 184, _ => a_fuel_pos_of_witness 184 10 0 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 185, _ => a_fuel_pos_of_witness 185 13 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 186, _ => a_fuel_pos_of_witness 186 10 1 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 187, _ => a_fuel_pos_of_witness 187 13 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 188, _ => a_fuel_pos_of_witness 188 13 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 189, _ => a_fuel_pos_of_witness 189 10 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 190, _ => a_fuel_pos_of_witness 190 13 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 191, _ => a_fuel_pos_of_witness 191 13 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 192, _ => a_fuel_pos_of_witness 192 8 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 193, _ => a_fuel_pos_of_witness 193 11 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 194, _ => a_fuel_pos_of_witness 194 12 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 195, _ => a_fuel_pos_of_witness 195 12 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 196, _ => a_fuel_pos_of_witness 196 14 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 197, _ => a_fuel_pos_of_witness 197 14 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 198, _ => a_fuel_pos_of_witness 198 14 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 199, _ => a_fuel_pos_of_witness 199 14 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 200, _ => a_fuel_pos_of_witness 200 0 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 201, _ => a_fuel_pos_of_witness 201 13 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 202, _ => a_fuel_pos_of_witness 202 13 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 203, _ => a_fuel_pos_of_witness 203 13 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 204, _ => a_fuel_pos_of_witness 204 14 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 205, _ => a_fuel_pos_of_witness 205 14 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 206, _ => a_fuel_pos_of_witness 206 13 3 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 207, _ => a_fuel_pos_of_witness 207 14 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 208, _ => a_fuel_pos_of_witness 208 8 8 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 209, _ => a_fuel_pos_of_witness 209 9 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 210, _ => a_fuel_pos_of_witness 210 9 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 211, _ => a_fuel_pos_of_witness 211 7 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 212, _ => a_fuel_pos_of_witness 212 7 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 213, _ => a_fuel_pos_of_witness 213 10 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 214, _ => a_fuel_pos_of_witness 214 14 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 215, _ => a_fuel_pos_of_witness 215 14 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 216, _ => a_fuel_pos_of_witness 216 12 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 217, _ => a_fuel_pos_of_witness 217 12 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 218, _ => a_fuel_pos_of_witness 218 3 8 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 219, _ => a_fuel_pos_of_witness 219 13 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 220, _ => a_fuel_pos_of_witness 220 13 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 221, _ => a_fuel_pos_of_witness 221 3 8 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 222, _ => a_fuel_pos_of_witness 222 13 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 223, _ => a_fuel_pos_of_witness 223 13 5 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 224, _ => a_fuel_pos_of_witness 224 12 4 0 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 225, _ => a_fuel_pos_of_witness 225 15 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 226, _ => a_fuel_pos_of_witness 226 8 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 227, _ => a_fuel_pos_of_witness 227 15 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 228, _ => a_fuel_pos_of_witness 228 14 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 229, _ => a_fuel_pos_of_witness 229 14 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 230, _ => a_fuel_pos_of_witness 230 14 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 231, _ => a_fuel_pos_of_witness 231 10 5 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 232, _ => a_fuel_pos_of_witness 232 12 6 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 233, _ => a_fuel_pos_of_witness 233 15 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 234, _ => a_fuel_pos_of_witness 234 15 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 235, _ => a_fuel_pos_of_witness 235 13 5 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 236, _ => a_fuel_pos_of_witness 236 6 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 237, _ => a_fuel_pos_of_witness 237 6 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 238, _ => a_fuel_pos_of_witness 238 13 5 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 239, _ => a_fuel_pos_of_witness 239 6 10 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 240, _ => a_fuel_pos_of_witness 240 6 10 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 241, _ => a_fuel_pos_of_witness 241 13 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 242, _ => a_fuel_pos_of_witness 242 12 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 243, _ => a_fuel_pos_of_witness 243 15 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 244, _ => a_fuel_pos_of_witness 244 15 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 245, _ => a_fuel_pos_of_witness 245 6 8 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 246, _ => a_fuel_pos_of_witness 246 14 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 247, _ => a_fuel_pos_of_witness 247 14 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 248, _ => a_fuel_pos_of_witness 248 6 8 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 249, _ => a_fuel_pos_of_witness 249 11 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 250, _ => a_fuel_pos_of_witness 250 11 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 251, _ => a_fuel_pos_of_witness 251 3 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 252, _ => a_fuel_pos_of_witness 252 3 11 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 253, _ => a_fuel_pos_of_witness 253 10 6 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 254, _ => a_fuel_pos_of_witness 254 3 11 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 255, _ => a_fuel_pos_of_witness 255 3 11 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 256, _ => a_fuel_pos_of_witness 256 16 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 257, _ => a_fuel_pos_of_witness 257 15 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 258, _ => a_fuel_pos_of_witness 258 16 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 259, _ => a_fuel_pos_of_witness 259 16 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 260, _ => a_fuel_pos_of_witness 260 9 7 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 261, _ => a_fuel_pos_of_witness 261 16 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 262, _ => a_fuel_pos_of_witness 262 10 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 263, _ => a_fuel_pos_of_witness 263 10 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 264, _ => a_fuel_pos_of_witness 264 16 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 265, _ => a_fuel_pos_of_witness 265 16 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 266, _ => a_fuel_pos_of_witness 266 10 9 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 267, _ => a_fuel_pos_of_witness 267 13 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 268, _ => a_fuel_pos_of_witness 268 14 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 269, _ => a_fuel_pos_of_witness 269 14 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 270, _ => a_fuel_pos_of_witness 270 13 7 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 271, _ => a_fuel_pos_of_witness 271 14 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 272, _ => a_fuel_pos_of_witness 272 12 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 273, _ => a_fuel_pos_of_witness 273 12 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 274, _ => a_fuel_pos_of_witness 274 16 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 275, _ => a_fuel_pos_of_witness 275 15 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 276, _ => a_fuel_pos_of_witness 276 15 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 277, _ => a_fuel_pos_of_witness 277 14 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 278, _ => a_fuel_pos_of_witness 278 6 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 279, _ => a_fuel_pos_of_witness 279 6 11 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 280, _ => a_fuel_pos_of_witness 280 16 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 281, _ => a_fuel_pos_of_witness 281 9 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 282, _ => a_fuel_pos_of_witness 282 9 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 283, _ => a_fuel_pos_of_witness 283 11 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 284, _ => a_fuel_pos_of_witness 284 11 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 285, _ => a_fuel_pos_of_witness 285 14 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 286, _ => a_fuel_pos_of_witness 286 11 9 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 287, _ => a_fuel_pos_of_witness 287 11 9 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 288, _ => a_fuel_pos_of_witness 288 16 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 289, _ => a_fuel_pos_of_witness 289 17 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 290, _ => a_fuel_pos_of_witness 290 17 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 291, _ => a_fuel_pos_of_witness 291 17 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 292, _ => a_fuel_pos_of_witness 292 2 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 293, _ => a_fuel_pos_of_witness 293 2 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 294, _ => a_fuel_pos_of_witness 294 14 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 295, _ => a_fuel_pos_of_witness 295 14 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 296, _ => a_fuel_pos_of_witness 296 2 12 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 297, _ => a_fuel_pos_of_witness 297 17 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 298, _ => a_fuel_pos_of_witness 298 17 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 299, _ => a_fuel_pos_of_witness 299 11 9 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 300, _ => a_fuel_pos_of_witness 300 10 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 301, _ => a_fuel_pos_of_witness 301 10 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 302, _ => a_fuel_pos_of_witness 302 11 9 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 303, _ => a_fuel_pos_of_witness 303 10 10 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 304, _ => a_fuel_pos_of_witness 304 4 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 305, _ => a_fuel_pos_of_witness 305 4 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 306, _ => a_fuel_pos_of_witness 306 16 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 307, _ => a_fuel_pos_of_witness 307 17 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 308, _ => a_fuel_pos_of_witness 308 17 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 309, _ => a_fuel_pos_of_witness 309 14 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 310, _ => a_fuel_pos_of_witness 310 14 7 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 311, _ => a_fuel_pos_of_witness 311 17 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 312, _ => a_fuel_pos_of_witness 312 14 4 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 313, _ => a_fuel_pos_of_witness 313 5 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 314, _ => a_fuel_pos_of_witness 314 5 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 315, _ => a_fuel_pos_of_witness 315 3 5 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 316, _ => a_fuel_pos_of_witness 316 10 10 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 317, _ => a_fuel_pos_of_witness 317 6 10 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 318, _ => a_fuel_pos_of_witness 318 3 5 4 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 319, _ => a_fuel_pos_of_witness 319 10 10 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 320, _ => a_fuel_pos_of_witness 320 4 12 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 321, _ => a_fuel_pos_of_witness 321 17 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 322, _ => a_fuel_pos_of_witness 322 17 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 323, _ => a_fuel_pos_of_witness 323 15 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 324, _ => a_fuel_pos_of_witness 324 18 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 325, _ => a_fuel_pos_of_witness 325 18 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 326, _ => a_fuel_pos_of_witness 326 18 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 327, _ => a_fuel_pos_of_witness 327 18 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 328, _ => a_fuel_pos_of_witness 328 16 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 329, _ => a_fuel_pos_of_witness 329 16 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 330, _ => a_fuel_pos_of_witness 330 11 8 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 331, _ => a_fuel_pos_of_witness 331 13 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 332, _ => a_fuel_pos_of_witness 332 18 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 333, _ => a_fuel_pos_of_witness 333 18 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 334, _ => a_fuel_pos_of_witness 334 13 9 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 335, _ => a_fuel_pos_of_witness 335 18 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 336, _ => a_fuel_pos_of_witness 336 18 2 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 337, _ => a_fuel_pos_of_witness 337 7 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 338, _ => a_fuel_pos_of_witness 338 0 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 339, _ => a_fuel_pos_of_witness 339 17 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 340, _ => a_fuel_pos_of_witness 340 17 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 341, _ => a_fuel_pos_of_witness 341 0 13 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 342, _ => a_fuel_pos_of_witness 342 18 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 343, _ => a_fuel_pos_of_witness 343 18 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 344, _ => a_fuel_pos_of_witness 344 12 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 345, _ => a_fuel_pos_of_witness 345 12 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 346, _ => a_fuel_pos_of_witness 346 18 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 347, _ => a_fuel_pos_of_witness 347 3 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 348, _ => a_fuel_pos_of_witness 348 3 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 349, _ => a_fuel_pos_of_witness 349 14 6 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 350, _ => a_fuel_pos_of_witness 350 3 13 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 351, _ => a_fuel_pos_of_witness 351 3 13 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 352, _ => a_fuel_pos_of_witness 352 8 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 353, _ => a_fuel_pos_of_witness 353 15 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 354, _ => a_fuel_pos_of_witness 354 16 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 355, _ => a_fuel_pos_of_witness 355 16 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 356, _ => a_fuel_pos_of_witness 356 18 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 357, _ => a_fuel_pos_of_witness 357 18 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 358, _ => a_fuel_pos_of_witness 358 14 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 359, _ => a_fuel_pos_of_witness 359 14 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 360, _ => a_fuel_pos_of_witness 360 12 10 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 361, _ => a_fuel_pos_of_witness 361 19 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 362, _ => a_fuel_pos_of_witness 362 19 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 363, _ => a_fuel_pos_of_witness 363 19 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 364, _ => a_fuel_pos_of_witness 364 19 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 365, _ => a_fuel_pos_of_witness 365 19 0 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 366, _ => a_fuel_pos_of_witness 366 19 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 367, _ => a_fuel_pos_of_witness 367 19 1 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 368, _ => a_fuel_pos_of_witness 368 8 12 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 369, _ => a_fuel_pos_of_witness 369 19 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 370, _ => a_fuel_pos_of_witness 370 19 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 371, _ => a_fuel_pos_of_witness 371 8 12 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 372, _ => a_fuel_pos_of_witness 372 18 4 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 373, _ => a_fuel_pos_of_witness 373 2 12 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 374, _ => a_fuel_pos_of_witness 374 18 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 375, _ => a_fuel_pos_of_witness 375 18 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 376, _ => a_fuel_pos_of_witness 376 2 12 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 377, _ => a_fuel_pos_of_witness 377 19 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 378, _ => a_fuel_pos_of_witness 378 17 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 379, _ => a_fuel_pos_of_witness 379 19 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 380, _ => a_fuel_pos_of_witness 380 19 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 381, _ => a_fuel_pos_of_witness 381 10 10 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 382, _ => a_fuel_pos_of_witness 382 19 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 383, _ => a_fuel_pos_of_witness 383 19 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 384, _ => a_fuel_pos_of_witness 384 16 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 385, _ => a_fuel_pos_of_witness 385 16 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 386, _ => a_fuel_pos_of_witness 386 12 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 387, _ => a_fuel_pos_of_witness 387 17 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 388, _ => a_fuel_pos_of_witness 388 10 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 389, _ => a_fuel_pos_of_witness 389 10 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 390, _ => a_fuel_pos_of_witness 390 18 5 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 391, _ => a_fuel_pos_of_witness 391 10 12 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 392, _ => a_fuel_pos_of_witness 392 0 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 393, _ => a_fuel_pos_of_witness 393 19 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 394, _ => a_fuel_pos_of_witness 394 19 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 395, _ => a_fuel_pos_of_witness 395 19 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 396, _ => a_fuel_pos_of_witness 396 18 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 397, _ => a_fuel_pos_of_witness 397 18 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 398, _ => a_fuel_pos_of_witness 398 19 3 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 399, _ => a_fuel_pos_of_witness 399 18 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 400, _ => a_fuel_pos_of_witness 400 20 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 401, _ => a_fuel_pos_of_witness 401 3 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 402, _ => a_fuel_pos_of_witness 402 20 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 403, _ => a_fuel_pos_of_witness 403 20 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 404, _ => a_fuel_pos_of_witness 404 10 12 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 405, _ => a_fuel_pos_of_witness 405 18 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 406, _ => a_fuel_pos_of_witness 406 10 5 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 407, _ => a_fuel_pos_of_witness 407 18 1 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 408, _ => a_fuel_pos_of_witness 408 20 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 409, _ => a_fuel_pos_of_witness 409 11 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 410, _ => a_fuel_pos_of_witness 410 11 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 411, _ => a_fuel_pos_of_witness 411 19 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 412, _ => a_fuel_pos_of_witness 412 19 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 413, _ => a_fuel_pos_of_witness 413 18 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 414, _ => a_fuel_pos_of_witness 414 19 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 415, _ => a_fuel_pos_of_witness 415 19 5 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 416, _ => a_fuel_pos_of_witness 416 20 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 417, _ => a_fuel_pos_of_witness 417 17 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 418, _ => a_fuel_pos_of_witness 418 20 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 419, _ => a_fuel_pos_of_witness 419 9 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 420, _ => a_fuel_pos_of_witness 420 9 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 421, _ => a_fuel_pos_of_witness 421 20 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 422, _ => a_fuel_pos_of_witness 422 18 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 423, _ => a_fuel_pos_of_witness 423 18 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 424, _ => a_fuel_pos_of_witness 424 20 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 425, _ => a_fuel_pos_of_witness 425 15 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 426, _ => a_fuel_pos_of_witness 426 15 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 427, _ => a_fuel_pos_of_witness 427 19 5 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 428, _ => a_fuel_pos_of_witness 428 6 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 429, _ => a_fuel_pos_of_witness 429 6 14 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 430, _ => a_fuel_pos_of_witness 430 19 5 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 431, _ => a_fuel_pos_of_witness 431 6 14 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 432, _ => a_fuel_pos_of_witness 432 20 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 433, _ => a_fuel_pos_of_witness 433 19 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 434, _ => a_fuel_pos_of_witness 434 19 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 435, _ => a_fuel_pos_of_witness 435 9 13 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 436, _ => a_fuel_pos_of_witness 436 19 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 437, _ => a_fuel_pos_of_witness 437 18 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 438, _ => a_fuel_pos_of_witness 438 14 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 439, _ => a_fuel_pos_of_witness 439 14 11 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 440, _ => a_fuel_pos_of_witness 440 18 4 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 441, _ => a_fuel_pos_of_witness 441 21 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 442, _ => a_fuel_pos_of_witness 442 21 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 443, _ => a_fuel_pos_of_witness 443 21 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 444, _ => a_fuel_pos_of_witness 444 21 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 445, _ => a_fuel_pos_of_witness 445 21 0 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 446, _ => a_fuel_pos_of_witness 446 21 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 447, _ => a_fuel_pos_of_witness 447 21 1 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 448, _ => a_fuel_pos_of_witness 448 20 4 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 449, _ => a_fuel_pos_of_witness 449 21 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 450, _ => a_fuel_pos_of_witness 450 20 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 451, _ => a_fuel_pos_of_witness 451 17 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 452, _ => a_fuel_pos_of_witness 452 18 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 453, _ => a_fuel_pos_of_witness 453 18 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 454, _ => a_fuel_pos_of_witness 454 2 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 455, _ => a_fuel_pos_of_witness 455 2 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 456, _ => a_fuel_pos_of_witness 456 16 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 457, _ => a_fuel_pos_of_witness 457 13 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 458, _ => a_fuel_pos_of_witness 458 13 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 459, _ => a_fuel_pos_of_witness 459 21 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 460, _ => a_fuel_pos_of_witness 460 21 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 461, _ => a_fuel_pos_of_witness 461 13 12 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 462, _ => a_fuel_pos_of_witness 462 21 3 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 463, _ => a_fuel_pos_of_witness 463 21 3 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 464, _ => a_fuel_pos_of_witness 464 20 0 2 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 465, _ => a_fuel_pos_of_witness 465 21 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 466, _ => a_fuel_pos_of_witness 466 4 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 467, _ => a_fuel_pos_of_witness 467 15 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 468, _ => a_fuel_pos_of_witness 468 15 11 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 469, _ => a_fuel_pos_of_witness 469 10 12 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 470, _ => a_fuel_pos_of_witness 470 2 15 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 471, _ => a_fuel_pos_of_witness 471 15 11 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 472, _ => a_fuel_pos_of_witness 472 20 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 473, _ => a_fuel_pos_of_witness 473 21 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 474, _ => a_fuel_pos_of_witness 474 21 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 475, _ => a_fuel_pos_of_witness 475 5 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 476, _ => a_fuel_pos_of_witness 476 5 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 477, _ => a_fuel_pos_of_witness 477 18 6 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 478, _ => a_fuel_pos_of_witness 478 5 15 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 479, _ => a_fuel_pos_of_witness 479 5 15 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 480, _ => a_fuel_pos_of_witness 480 18 6 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 481, _ => a_fuel_pos_of_witness 481 20 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 482, _ => a_fuel_pos_of_witness 482 12 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 483, _ => a_fuel_pos_of_witness 483 12 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 484, _ => a_fuel_pos_of_witness 484 22 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 485, _ => a_fuel_pos_of_witness 485 22 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 486, _ => a_fuel_pos_of_witness 486 22 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 487, _ => a_fuel_pos_of_witness 487 22 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 488, _ => a_fuel_pos_of_witness 488 20 6 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 489, _ => a_fuel_pos_of_witness 489 19 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 490, _ => a_fuel_pos_of_witness 490 19 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 491, _ => a_fuel_pos_of_witness 491 21 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 492, _ => a_fuel_pos_of_witness 492 22 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 493, _ => a_fuel_pos_of_witness 493 22 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 494, _ => a_fuel_pos_of_witness 494 21 5 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 495, _ => a_fuel_pos_of_witness 495 22 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 496, _ => a_fuel_pos_of_witness 496 22 2 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 497, _ => a_fuel_pos_of_witness 497 13 6 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 498, _ => a_fuel_pos_of_witness 498 20 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 499, _ => a_fuel_pos_of_witness 499 7 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 500, _ => a_fuel_pos_of_witness 500 7 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 501, _ => a_fuel_pos_of_witness 501 20 7 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 502, _ => a_fuel_pos_of_witness 502 22 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 503, _ => a_fuel_pos_of_witness 503 22 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 504, _ => a_fuel_pos_of_witness 504 16 10 0 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 505, _ => a_fuel_pos_of_witness 505 19 8 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 506, _ => a_fuel_pos_of_witness 506 15 10 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 507, _ => a_fuel_pos_of_witness 507 13 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 508, _ => a_fuel_pos_of_witness 508 13 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 509, _ => a_fuel_pos_of_witness 509 6 14 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 510, _ => a_fuel_pos_of_witness 510 13 13 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 511, _ => a_fuel_pos_of_witness 511 13 13 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 512, _ => a_fuel_pos_of_witness 512 0 16 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 513, _ => a_fuel_pos_of_witness 513 21 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 514, _ => a_fuel_pos_of_witness 514 8 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 515, _ => a_fuel_pos_of_witness 515 8 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 516, _ => a_fuel_pos_of_witness 516 22 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 517, _ => a_fuel_pos_of_witness 517 22 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 518, _ => a_fuel_pos_of_witness 518 22 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 519, _ => a_fuel_pos_of_witness 519 14 11 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 520, _ => a_fuel_pos_of_witness 520 16 2 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 521, _ => a_fuel_pos_of_witness 521 3 16 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 522, _ => a_fuel_pos_of_witness 522 3 16 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 523, _ => a_fuel_pos_of_witness 523 19 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 524, _ => a_fuel_pos_of_witness 524 18 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 525, _ => a_fuel_pos_of_witness 525 18 10 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 526, _ => a_fuel_pos_of_witness 526 19 9 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 527, _ => a_fuel_pos_of_witness 527 18 10 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 528, _ => a_fuel_pos_of_witness 528 20 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 529, _ => a_fuel_pos_of_witness 529 23 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 530, _ => a_fuel_pos_of_witness 530 23 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 531, _ => a_fuel_pos_of_witness 531 23 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 532, _ => a_fuel_pos_of_witness 532 23 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 533, _ => a_fuel_pos_of_witness 533 18 8 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 534, _ => a_fuel_pos_of_witness 534 22 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 535, _ => a_fuel_pos_of_witness 535 22 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 536, _ => a_fuel_pos_of_witness 536 12 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 537, _ => a_fuel_pos_of_witness 537 23 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 538, _ => a_fuel_pos_of_witness 538 23 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 539, _ => a_fuel_pos_of_witness 539 21 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 540, _ => a_fuel_pos_of_witness 540 21 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 541, _ => a_fuel_pos_of_witness 541 23 2 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 542, _ => a_fuel_pos_of_witness 542 21 7 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 543, _ => a_fuel_pos_of_witness 543 21 7 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 544, _ => a_fuel_pos_of_witness 544 16 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 545, _ => a_fuel_pos_of_witness 545 16 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 546, _ => a_fuel_pos_of_witness 546 20 7 0 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 547, _ => a_fuel_pos_of_witness 547 23 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 548, _ => a_fuel_pos_of_witness 548 6 16 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 549, _ => a_fuel_pos_of_witness 549 6 16 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 550, _ => a_fuel_pos_of_witness 550 10 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 551, _ => a_fuel_pos_of_witness 551 10 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 552, _ => a_fuel_pos_of_witness 552 12 14 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 553, _ => a_fuel_pos_of_witness 553 23 2 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 554, _ => a_fuel_pos_of_witness 554 21 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 555, _ => a_fuel_pos_of_witness 555 21 7 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 556, _ => a_fuel_pos_of_witness 556 22 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 557, _ => a_fuel_pos_of_witness 557 22 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 558, _ => a_fuel_pos_of_witness 558 21 7 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 559, _ => a_fuel_pos_of_witness 559 22 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 560, _ => a_fuel_pos_of_witness 560 16 12 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 561, _ => a_fuel_pos_of_witness 561 23 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 562, _ => a_fuel_pos_of_witness 562 20 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 563, _ => a_fuel_pos_of_witness 563 15 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 564, _ => a_fuel_pos_of_witness 564 15 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 565, _ => a_fuel_pos_of_witness 565 22 0 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 566, _ => a_fuel_pos_of_witness 566 18 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 567, _ => a_fuel_pos_of_witness 567 18 11 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 568, _ => a_fuel_pos_of_witness 568 22 0 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 569, _ => a_fuel_pos_of_witness 569 21 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 570, _ => a_fuel_pos_of_witness 570 21 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 571, _ => a_fuel_pos_of_witness 571 11 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 572, _ => a_fuel_pos_of_witness 572 11 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 573, _ => a_fuel_pos_of_witness 573 22 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 574, _ => a_fuel_pos_of_witness 574 11 15 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 575, _ => a_fuel_pos_of_witness 575 11 15 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 576, _ => a_fuel_pos_of_witness 576 24 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 577, _ => a_fuel_pos_of_witness 577 17 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 578, _ => a_fuel_pos_of_witness 578 24 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 579, _ => a_fuel_pos_of_witness 579 23 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 580, _ => a_fuel_pos_of_witness 580 23 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 581, _ => a_fuel_pos_of_witness 581 24 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 582, _ => a_fuel_pos_of_witness 582 22 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 583, _ => a_fuel_pos_of_witness 583 22 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 584, _ => a_fuel_pos_of_witness 584 24 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 585, _ => a_fuel_pos_of_witness 585 24 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 586, _ => a_fuel_pos_of_witness 586 22 7 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 587, _ => a_fuel_pos_of_witness 587 3 17 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 588, _ => a_fuel_pos_of_witness 588 14 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 589, _ => a_fuel_pos_of_witness 589 14 14 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 590, _ => a_fuel_pos_of_witness 590 3 17 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 591, _ => a_fuel_pos_of_witness 591 14 14 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 592, _ => a_fuel_pos_of_witness 592 24 0 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 593, _ => a_fuel_pos_of_witness 593 9 16 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 594, _ => a_fuel_pos_of_witness 594 24 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 595, _ => a_fuel_pos_of_witness 595 24 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 596, _ => a_fuel_pos_of_witness 596 9 16 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 597, _ => a_fuel_pos_of_witness 597 22 4 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 598, _ => a_fuel_pos_of_witness 598 22 7 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 599, _ => a_fuel_pos_of_witness 599 10 15 1 2 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 600, _ => a_fuel_pos_of_witness 600 20 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 601, _ => a_fuel_pos_of_witness 601 23 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 602, _ => a_fuel_pos_of_witness 602 23 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 603, _ => a_fuel_pos_of_witness 603 21 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 604, _ => a_fuel_pos_of_witness 604 21 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 605, _ => a_fuel_pos_of_witness 605 18 10 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 606, _ => a_fuel_pos_of_witness 606 21 9 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 607, _ => a_fuel_pos_of_witness 607 21 9 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 608, _ => a_fuel_pos_of_witness 608 24 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 609, _ => a_fuel_pos_of_witness 609 24 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 610, _ => a_fuel_pos_of_witness 610 24 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 611, _ => a_fuel_pos_of_witness 611 24 4 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 612, _ => a_fuel_pos_of_witness 612 22 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 613, _ => a_fuel_pos_of_witness 613 22 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 614, _ => a_fuel_pos_of_witness 614 6 17 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 615, _ => a_fuel_pos_of_witness 615 6 17 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 616, _ => a_fuel_pos_of_witness 616 20 10 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 617, _ => a_fuel_pos_of_witness 617 15 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 618, _ => a_fuel_pos_of_witness 618 15 14 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 619, _ => a_fuel_pos_of_witness 619 13 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 620, _ => a_fuel_pos_of_witness 620 13 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 621, _ => a_fuel_pos_of_witness 621 15 14 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 622, _ => a_fuel_pos_of_witness 622 13 15 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 623, _ => a_fuel_pos_of_witness 623 13 15 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 624, _ => a_fuel_pos_of_witness 624 24 4 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 625, _ => a_fuel_pos_of_witness 625 25 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 626, _ => a_fuel_pos_of_witness 626 24 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 627, _ => a_fuel_pos_of_witness 627 25 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 628, _ => a_fuel_pos_of_witness 628 25 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 629, _ => a_fuel_pos_of_witness 629 6 16 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 630, _ => a_fuel_pos_of_witness 630 6 17 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 631, _ => a_fuel_pos_of_witness 631 10 15 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 632, _ => a_fuel_pos_of_witness 632 6 16 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 633, _ => a_fuel_pos_of_witness 633 25 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 634, _ => a_fuel_pos_of_witness 634 25 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 635, _ => a_fuel_pos_of_witness 635 13 15 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 636, _ => a_fuel_pos_of_witness 636 3 1 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 637, _ => a_fuel_pos_of_witness 637 22 6 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 638, _ => a_fuel_pos_of_witness 638 13 15 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 639, _ => a_fuel_pos_of_witness 639 3 1 5 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 640, _ => a_fuel_pos_of_witness 640 16 8 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 641, _ => a_fuel_pos_of_witness 641 21 10 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 642, _ => a_fuel_pos_of_witness 642 20 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 643, _ => a_fuel_pos_of_witness 643 25 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 644, _ => a_fuel_pos_of_witness 644 25 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 645, _ => a_fuel_pos_of_witness 645 20 11 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 646, _ => a_fuel_pos_of_witness 646 22 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 647, _ => a_fuel_pos_of_witness 647 22 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 648, _ => a_fuel_pos_of_witness 648 24 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 649, _ => a_fuel_pos_of_witness 649 19 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 650, _ => a_fuel_pos_of_witness 650 19 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 651, _ => a_fuel_pos_of_witness 651 24 6 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 652, _ => a_fuel_pos_of_witness 652 2 18 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 653, _ => a_fuel_pos_of_witness 653 2 18 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 654, _ => a_fuel_pos_of_witness 654 19 5 0 3 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 655, _ => a_fuel_pos_of_witness 655 2 18 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 656, _ => a_fuel_pos_of_witness 656 12 16 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 657, _ => a_fuel_pos_of_witness 657 25 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 658, _ => a_fuel_pos_of_witness 658 25 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 659, _ => a_fuel_pos_of_witness 659 9 17 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 660, _ => a_fuel_pos_of_witness 660 9 17 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 661, _ => a_fuel_pos_of_witness 661 6 0 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 662, _ => a_fuel_pos_of_witness 662 18 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 663, _ => a_fuel_pos_of_witness 663 18 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 664, _ => a_fuel_pos_of_witness 664 4 18 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 665, _ => a_fuel_pos_of_witness 665 4 18 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 666, _ => a_fuel_pos_of_witness 666 3 4 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 667, _ => a_fuel_pos_of_witness 667 19 5 4 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 668, _ => a_fuel_pos_of_witness 668 2 18 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 669, _ => a_fuel_pos_of_witness 669 14 14 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 670, _ => a_fuel_pos_of_witness 670 19 5 4 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 671, _ => a_fuel_pos_of_witness 671 2 18 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 672, _ => a_fuel_pos_of_witness 672 12 16 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 673, _ => a_fuel_pos_of_witness 673 5 18 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 674, _ => a_fuel_pos_of_witness 674 24 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 675, _ => a_fuel_pos_of_witness 675 25 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 676, _ => a_fuel_pos_of_witness 676 26 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 677, _ => a_fuel_pos_of_witness 677 26 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 678, _ => a_fuel_pos_of_witness 678 26 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 679, _ => a_fuel_pos_of_witness 679 26 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 680, _ => a_fuel_pos_of_witness 680 4 18 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 681, _ => a_fuel_pos_of_witness 681 17 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 682, _ => a_fuel_pos_of_witness 682 17 14 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 683, _ => a_fuel_pos_of_witness 683 21 11 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 684, _ => a_fuel_pos_of_witness 684 26 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 685, _ => a_fuel_pos_of_witness 685 26 2 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 686, _ => a_fuel_pos_of_witness 686 21 11 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 687, _ => a_fuel_pos_of_witness 687 26 2 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 688, _ => a_fuel_pos_of_witness 688 20 12 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 689, _ => a_fuel_pos_of_witness 689 20 12 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 690, _ => a_fuel_pos_of_witness 690 24 7 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 691, _ => a_fuel_pos_of_witness 691 23 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 692, _ => a_fuel_pos_of_witness 692 23 9 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 693, _ => a_fuel_pos_of_witness 693 22 8 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 694, _ => a_fuel_pos_of_witness 694 26 3 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 695, _ => a_fuel_pos_of_witness 695 26 3 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 696, _ => a_fuel_pos_of_witness 696 22 8 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 697, _ => a_fuel_pos_of_witness 697 25 6 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 698, _ => a_fuel_pos_of_witness 698 25 6 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 699, _ => a_fuel_pos_of_witness 699 19 13 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 700, _ => a_fuel_pos_of_witness 700 19 13 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 701, _ => a_fuel_pos_of_witness 701 2 6 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 702, _ => a_fuel_pos_of_witness 702 19 13 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 703, _ => a_fuel_pos_of_witness 703 19 13 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 704, _ => a_fuel_pos_of_witness 704 24 8 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 705, _ => a_fuel_pos_of_witness 705 24 8 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 706, _ => a_fuel_pos_of_witness 706 16 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 707, _ => a_fuel_pos_of_witness 707 16 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 708, _ => a_fuel_pos_of_witness 708 26 4 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 709, _ => a_fuel_pos_of_witness 709 26 4 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 710, _ => a_fuel_pos_of_witness 710 26 3 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 711, _ => a_fuel_pos_of_witness 711 6 5 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 712, _ => a_fuel_pos_of_witness 712 8 18 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 713, _ => a_fuel_pos_of_witness 713 8 18 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 714, _ => a_fuel_pos_of_witness 714 25 2 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 715, _ => a_fuel_pos_of_witness 715 19 13 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 716, _ => a_fuel_pos_of_witness 716 18 14 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 717, _ => a_fuel_pos_of_witness 717 18 14 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 718, _ => a_fuel_pos_of_witness 718 19 13 2 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 719, _ => a_fuel_pos_of_witness 719 18 14 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 720, _ => a_fuel_pos_of_witness 720 24 8 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 721, _ => a_fuel_pos_of_witness 721 8 4 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 722, _ => a_fuel_pos_of_witness 722 12 17 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 723, _ => a_fuel_pos_of_witness 723 25 7 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 724, _ => a_fuel_pos_of_witness 724 25 7 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 725, _ => a_fuel_pos_of_witness 725 10 0 5 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 726, _ => a_fuel_pos_of_witness 726 26 5 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 727, _ => a_fuel_pos_of_witness 727 26 5 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 728, _ => a_fuel_pos_of_witness 728 8 18 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 729, _ => a_fuel_pos_of_witness 729 27 0 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 730, _ => a_fuel_pos_of_witness 730 27 0 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 731, _ => a_fuel_pos_of_witness 731 27 1 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 732, _ => a_fuel_pos_of_witness 732 27 1 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 733, _ => a_fuel_pos_of_witness 733 2 18 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 734, _ => a_fuel_pos_of_witness 734 27 1 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 735, _ => a_fuel_pos_of_witness 735 27 1 1 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 736, _ => a_fuel_pos_of_witness 736 2 18 3 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 737, _ => a_fuel_pos_of_witness 737 27 2 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 738, _ => a_fuel_pos_of_witness 738 24 9 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 739, _ => a_fuel_pos_of_witness 739 17 15 0 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 740, _ => a_fuel_pos_of_witness 740 17 15 1 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 741, _ => a_fuel_pos_of_witness 741 24 9 0 1 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 742, _ => a_fuel_pos_of_witness 742 26 5 2 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | 743, _ => a_fuel_pos_of_witness 743 18 13 3 0 (by rfl) (by decide) (by decide) (by decide) (by decide)

  | n + 744, h => by omega


theorem a_eq_a_fuel (n : ℕ) (h : n ≤ 744) : a n = a_fuel n := by
  by_cases hn : n = 744
  · subst hn
    unfold a
    rw [if_pos rfl]
    exact a_fuel_744_proof.symm
  · have h_lt : n < 744 := by omega
    unfold a a_fuel
    rw [if_neg hn]
    have hn_not_gt : ¬ n > 744 := by omega
    rw [if_neg hn_not_gt]
    have h1 : Nat.sqrt n = sqrt_fuel 28 n := sqrt_eq_sqrt_fuel n h
    rw [h1]
    have h2 : Nat.sqrt (sqrt_fuel 28 n) = sqrt_fuel 28 (sqrt_fuel 28 n) := by
      have h_eq : sqrt_fuel 28 n = Nat.sqrt n := h1.symm
      rw [h_eq]
      have h_sqrt_le : Nat.sqrt n ≤ 744 := by
        have h_le := Nat.sqrt_le_self n
        omega
      exact sqrt_eq_sqrt_fuel (Nat.sqrt n) h_sqrt_le
    rw [h2]
    refine sum_congr rfl fun z hz => ?_
    refine sum_congr rfl fun y hy => ?_
    refine sum_congr rfl fun x hx => ?_
    dsimp only
    have h3 : Nat.sqrt (n - (2 * x^2 + y^4 + 3 * z^4)) = sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)) := by
      have h_sub_le : n - (2 * x^2 + y^4 + 3 * z^4) ≤ 744 := by omega
      exact sqrt_eq_sqrt_fuel _ h_sub_le
    rw [h3]
    rfl


theorem a_744_eq_a_fuel_744 : a 744 = a_fuel 744 :=
  a_eq_a_fuel 744 (by omega)

theorem a_744_eq_zero : a 744 = 0 := by
  rw [a_744_eq_a_fuel_744]
  exact a_fuel_744_proof


lemma a_fuel_witness_bounds (n : ℕ) (w x y z : ℕ) (h_le : n ≤ 744) (hw : w^2 + 2 * x^2 + y^4 + 3 * z^4 = n) :
    (x < sqrt_fuel 28 n + 1) ∧
    (y < sqrt_fuel 28 (sqrt_fuel 28 n) + 1) ∧
    (z < sqrt_fuel 28 (sqrt_fuel 28 n) + 1) ∧
    ((sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4)) := by
  have h_sqrt_eq : sqrt_fuel 28 n = Nat.sqrt n := (sqrt_eq_sqrt_fuel n h_le).symm
  have h_sqrt_sqrt_eq : sqrt_fuel 28 (sqrt_fuel 28 n) = Nat.sqrt (Nat.sqrt n) := by
    rw [h_sqrt_eq]
    have h_sqrt_le : Nat.sqrt n ≤ 744 := by
      have := Nat.sqrt_le_self n
      omega
    exact (sqrt_eq_sqrt_fuel (Nat.sqrt n) h_sqrt_le).symm

  have hx_le : x^2 ≤ n := by omega
  have hx : x < Nat.sqrt n + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_sqrt']
    exact hx_le
  have hx_fuel : x < sqrt_fuel 28 n + 1 := by
    rw [h_sqrt_eq]
    exact hx

  have hy_le : y^4 ≤ n := by omega
  have hy_le_sq : y^2 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt']
    have : (y^2)^2 = y^4 := by ring
    rw [this]
    exact hy_le
  have hy : y < Nat.sqrt (Nat.sqrt n) + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_sqrt']
    exact hy_le_sq
  have hy_fuel : y < sqrt_fuel 28 (sqrt_fuel 28 n) + 1 := by
    rw [h_sqrt_sqrt_eq]
    exact hy

  have hz_le : z^4 ≤ n := by
    have : 3 * z^4 ≤ n := by omega
    omega
  have hz_le_sq : z^2 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt']
    have : (z^2)^2 = z^4 := by ring
    rw [this]
    exact hz_le
  have hz : z < Nat.sqrt (Nat.sqrt n) + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_sqrt']
    exact hz_le_sq
  have hz_fuel : z < sqrt_fuel 28 (sqrt_fuel 28 n) + 1 := by
    rw [h_sqrt_sqrt_eq]
    exact hz

  have hps : (sqrt_fuel 28 (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4) := by
    have h_sub_le : n - (2 * x^2 + y^4 + 3 * z^4) ≤ 744 := by omega
    rw [← sqrt_eq_sqrt_fuel (n - (2 * x^2 + y^4 + 3 * z^4)) h_sub_le]
    have h_sub : n - (2 * x^2 + y^4 + 3 * z^4) = w^2 := by omega
    rw [h_sub]
    rw [Nat.sqrt_eq']

  exact ⟨hx_fuel, hy_fuel, hz_fuel, hps⟩


lemma a_pos_of_exists (n : ℕ) (w x y z : ℕ) (hw : w^2 + 2 * x^2 + y^4 + 3 * z^4 = n) : a n > 0 := by
  by_cases hn : n = 744
  · subst hn
    have h_bounds := a_fuel_witness_bounds 744 w x y z (by omega) hw
    have h_pos : a_fuel 744 > 0 := a_fuel_pos_of_witness 744 w x y z hw h_bounds.1 h_bounds.2.1 h_bounds.2.2.1 h_bounds.2.2.2
    have h_zero : a_fuel 744 = 0 := a_fuel_744_proof
    omega
  · by_cases h_gt : n > 744
    · unfold a
      rw [if_neg hn, if_pos h_gt]
      omega
    · have h_lt : n < 744 := by omega
      have h_eq : a n = a_fuel n := a_eq_a_fuel n (by omega)
      rw [h_eq]
      have h_bounds := a_fuel_witness_bounds n w x y z (by omega) hw
      exact a_fuel_pos_of_witness n w x y z hw h_bounds.1 h_bounds.2.1 h_bounds.2.2.1 h_bounds.2.2.2


/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  constructor
  · intro h hn
    subst hn
    have h_zero := a_744_eq_zero
    omega
  · intro hn
    if h_lt : n < 744 then
      have h_a_eq := a_eq_a_fuel n (by omega)
      rw [h_a_eq]
      exact a_fuel_pos_lt_744 n h_lt
    else if h_744 : n = 744 then
      contradiction
    else
      have h_gt : n > 744 := by omega
      unfold a
      rw [if_neg hn, if_pos h_gt]
      omega




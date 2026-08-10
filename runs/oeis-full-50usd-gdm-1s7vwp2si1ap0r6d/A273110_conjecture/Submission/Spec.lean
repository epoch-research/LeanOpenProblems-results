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

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

open Nat

/--
A273110: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with
$(x+4y+4z)^2 + (9x+3y+3z)^2$ a square, where $x,y,z,w$ are nonnegative integers
with $y > 0$ and $y \ge z \le w$.
-/
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}


lemma E_zero_isSquare (y z : ℕ) : IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) := by
  use 5 * (y + z)
  ring

lemma A273110_pos_of_three_squares (n : ℕ) (y z w : ℕ) (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) (hn : y^2 + z^2 + w^2 = n) : 0 < A273110 n := by
  have hy2 : y^2 ≤ n := by omega
  have hz2 : z^2 ≤ n := by omega
  have hw2 : w^2 ≤ n := by omega
  
  have hy_le : y ≤ y^2 := by rw [pow_two]; exact Nat.le_mul_self y
  have hz_le : z ≤ z^2 := by rw [pow_two]; exact Nat.le_mul_self z
  have hw_le : w ≤ w^2 := by rw [pow_two]; exact Nat.le_mul_self w
  
  have hy_le_n : y ≤ n := by omega
  have hz_le_n : z ≤ n := by omega
  have hw_le_n : w ≤ n := by omega
  
  have hx_in : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hy_in : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hz_in : z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hw_in : w ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)

  have hE : IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) := E_zero_isSquare y z

  have h_term : (if 0^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0) = 1 := by
    have h_eq : 0^2 + y^2 + z^2 + w^2 = n := by omega
    exact if_pos ⟨h_eq, hy, hyz, hzw, hE⟩

  -- Now we chain the single_le_sum inequalities
  have step1 : (if 0^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0) ≤ 
    Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun w' => if 0^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0)
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hw_in

  have step2 : Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0) ≤
    Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z')^2 + (9 * 0 + 3 * y + 3 * z')^2) then 1 else 0)) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z')^2 + (9 * 0 + 3 * y + 3 * z')^2) then 1 else 0))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hz_in

  have step3 : Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y + 4 * z')^2 + (9 * 0 + 3 * y + 3 * z')^2) then 1 else 0)) ≤
    Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y' + 4 * z')^2 + (9 * 0 + 3 * y' + 3 * z')^2) then 1 else 0))) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y' + 4 * z')^2 + (9 * 0 + 3 * y' + 3 * z')^2) then 1 else 0)))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hy_in

  have step4 : Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if 0^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((0 + 4 * y' + 4 * z')^2 + (9 * 0 + 3 * y' + 3 * z')^2) then 1 else 0))) ≤
    Finset.sum (Finset.range (n + 1)) (fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0)))) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0))))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hx_in

  have h_bound : 1 ≤ A273110 n := by
    have h_sum_eq : A273110 n = Finset.sum (Finset.range (n + 1)) (fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0)))) := rfl
    rw [h_sum_eq]
    have h_trans : 1 ≤ (if 0^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare ((0 + 4 * y + 4 * z)^2 + (9 * 0 + 3 * y + 3 * z)^2) then 1 else 0) := by omega
    exact le_trans (le_trans (le_trans (le_trans h_trans step1) step2) step3) step4

  omega

lemma E_x_isSquare (x y z : ℕ) (h : y + z = x) : IsSquare ((x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2) := by
  use 13 * x
  subst h
  ring

lemma A273110_pos_of_y_plus_z_eq_x (n : ℕ) (y z w : ℕ) (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) (hn : 2 * (y^2 + y * z + z^2) + w^2 = n) : 0 < A273110 n := by
  have h_sum_eq : (y + z)^2 + y^2 + z^2 + w^2 = 2 * (y^2 + y * z + z^2) + w^2 := by ring
  have h_eq : (y + z)^2 + y^2 + z^2 + w^2 = n := by omega
  
  have hx2 : (y + z)^2 ≤ n := by omega
  have hy2 : y^2 ≤ n := by omega
  have hz2 : z^2 ≤ n := by omega
  have hw2 : w^2 ≤ n := by omega
  
  have hx_le : y + z ≤ (y + z)^2 := by rw [pow_two]; exact Nat.le_mul_self (y + z)
  have hy_le : y ≤ y^2 := by rw [pow_two]; exact Nat.le_mul_self y
  have hz_le : z ≤ z^2 := by rw [pow_two]; exact Nat.le_mul_self z
  have hw_le : w ≤ w^2 := by rw [pow_two]; exact Nat.le_mul_self w
  
  have hx_le_n : y + z ≤ n := by omega
  have hy_le_n : y ≤ n := by omega
  have hz_le_n : z ≤ n := by omega
  have hw_le_n : w ≤ n := by omega
  
  have hx_in : y + z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hy_in : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hz_in : z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hw_in : w ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)

  have hE : IsSquare (( (y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) := E_x_isSquare (y+z) y z rfl

  have h_term : (if (y+z)^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0) = 1 := by
    exact if_pos ⟨h_eq, hy, hyz, hzw, hE⟩

  -- Now we chain the single_le_sum inequalities
  have step1 : (if (y+z)^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0) ≤ 
    Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun w' => if (y+z)^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0)
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hw_in

  have step2 : Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y^2 + z^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0) ≤
    Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z')^2 + (9 * (y+z) + 3 * y + 3 * z')^2) then 1 else 0)) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z')^2 + (9 * (y+z) + 3 * y + 3 * z')^2) then 1 else 0))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hz_in

  have step3 : Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y^2 + z'^2 + w'^2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y + 4 * z')^2 + (9 * (y+z) + 3 * y + 3 * z')^2) then 1 else 0)) ≤
    Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y' + 4 * z')^2 + (9 * (y+z) + 3 * y' + 3 * z')^2) then 1 else 0))) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y' + 4 * z')^2 + (9 * (y+z) + 3 * y' + 3 * z')^2) then 1 else 0)))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hy_in

  have step4 : Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if (y+z)^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare (((y+z) + 4 * y' + 4 * z')^2 + (9 * (y+z) + 3 * y' + 3 * z')^2) then 1 else 0))) ≤
    Finset.sum (Finset.range (n + 1)) (fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0)))) := by
    have h_le := Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0))))
    apply h_le
    · intro i _
      exact Nat.zero_le _
    · exact hx_in

  have h_bound : 1 ≤ A273110 n := by
    have h_sum_eq : A273110 n = Finset.sum (Finset.range (n + 1)) (fun x' => Finset.sum (Finset.range (n + 1)) (fun y' => Finset.sum (Finset.range (n + 1)) (fun z' => Finset.sum (Finset.range (n + 1)) (fun w' => if x'^2 + y'^2 + z'^2 + w'^2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧ IsSquare ((x' + 4 * y' + 4 * z')^2 + (9 * x' + 3 * y' + 3 * z')^2) then 1 else 0)))) := rfl
    rw [h_sum_eq]
    have h_trans : 1 ≤ (if (y+z)^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare (((y+z) + 4 * y + 4 * z)^2 + (9 * (y+z) + 3 * y + 3 * z)^2) then 1 else 0) := by omega
    exact le_trans (le_trans (le_trans (le_trans h_trans step1) step2) step3) step4

  omega



lemma squares_mod_four (x : ℕ) : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
  have h1 : x^2 = x * x := by ring
  rw [h1, Nat.mul_mod]
  have h2 : x % 4 < 4 := Nat.mod_lt x (by decide)
  rcases h_eq : x % 4 with _ | _ | _ | _ | _
  · left; rfl
  · right; rfl
  · left; rfl
  · right; rfl
  · omega

lemma sum_squares_mod_four (X Y Z W n : ℕ) (h : X^2 + Y^2 + Z^2 + W^2 = 4 * n) :
  (X^2 % 4 = 0 ∧ Y^2 % 4 = 0 ∧ Z^2 % 4 = 0 ∧ W^2 % 4 = 0) ∨
  (X^2 % 4 = 1 ∧ Y^2 % 4 = 1 ∧ Z^2 % 4 = 1 ∧ W^2 % 4 = 1) := by
  have h_mod : (X^2 + Y^2 + Z^2 + W^2) % 4 = 0 := by
    rw [h]
    exact Nat.mul_mod_right 4 n
  have h_add : (X^2 + Y^2 + Z^2 + W^2) % 4 = (X^2 % 4 + Y^2 % 4 + Z^2 % 4 + W^2 % 4) % 4 := by
    generalize X^2 = a
    generalize Y^2 = b
    generalize Z^2 = c
    generalize W^2 = d
    omega
  rw [h_add] at h_mod
  rcases squares_mod_four X with hX | hX
  <;> rcases squares_mod_four Y with hY | hY
  <;> rcases squares_mod_four Z with hZ | hZ
  <;> rcases squares_mod_four W with hW | hW
  · left; exact ⟨hX, hY, hZ, hW⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · right; exact ⟨hX, hY, hZ, hW⟩

lemma even_of_square_mod_four_zero (x : ℕ) (h : x^2 % 4 = 0) : x % 2 = 0 := by
  have h2 : x % 2 < 2 := Nat.mod_lt x (by decide)
  rcases h_eq : x % 2 with _ | _ | _
  · rfl
  · have h_mod : x = 2 * (x / 2) + 1 := (Nat.div_add_mod x 2).symm.trans (by rw [h_eq])
    rw [h_mod] at h
    ring_nf at h
    omega
  · omega

lemma not_square_E_of_all_odd (X Y Z : ℕ) (hX : X % 2 = 1) (hY : Y % 2 = 1) (hZ : Z % 2 = 1) :
  ¬ IsSquare ((X + 4 * Y + 4 * Z)^2 + (9 * X + 3 * Y + 3 * Z)^2) := by
  intro h_sq
  rcases h_sq with ⟨V, hV⟩
  have h_eqX : X = 2 * (X / 2) + 1 := (Nat.div_add_mod X 2).symm.trans (by rw [hX])
  have h_eqY : Y = 2 * (Y / 2) + 1 := (Nat.div_add_mod Y 2).symm.trans (by rw [hY])
  have h_eqZ : Z = 2 * (Z / 2) + 1 := (Nat.div_add_mod Z 2).symm.trans (by rw [hZ])
  rw [h_eqX, h_eqY, h_eqZ] at hV
  have h_mod : ((2 * (X / 2) + 1 + 4 * (2 * (Y / 2) + 1) + 4 * (2 * (Z / 2) + 1))^2 +
                (9 * (2 * (X / 2) + 1) + 3 * (2 * (Y / 2) + 1) + 3 * (2 * (Z / 2) + 1))^2) % 4 = (V * V) % 4 := by
    rw [hV]
  have h_lhs : ((2 * (X / 2) + 1 + 4 * (2 * (Y / 2) + 1) + 4 * (2 * (Z / 2) + 1))^2 +
                (9 * (2 * (X / 2) + 1) + 3 * (2 * (Y / 2) + 1) + 3 * (2 * (Z / 2) + 1))^2) % 4 = 2 := by
    generalize X / 2 = a
    generalize Y / 2 = b
    generalize Z / 2 = c
    ring_nf
    omega
  rw [h_lhs] at h_mod
  have h_V_sq : V^2 = V * V := by ring
  have h_squares_mod_four := squares_mod_four V
  rw [h_V_sq] at h_squares_mod_four
  rcases h_squares_mod_four with hV2 | hV2
  · rw [hV2] at h_mod; omega
  · rw [hV2] at h_mod; omega

lemma odd_of_square_mod_four_one (x : ℕ) (h : x^2 % 4 = 1) : x % 2 = 1 := by
  have h2 : x % 2 < 2 := Nat.mod_lt x (by decide)
  rcases h_eq : x % 2 with _ | _ | _
  · have h_mod : x = 2 * (x / 2) := (Nat.div_add_mod x 2).symm.trans (by rw [h_eq, Nat.add_zero])
    rw [h_mod] at h
    ring_nf at h
    omega
  · rfl
  · omega

lemma even_of_sum_squares_and_square_E (X Y Z W n : ℕ) (h : X^2 + Y^2 + Z^2 + W^2 = 4 * n)
  (hE : IsSquare ((X + 4 * Y + 4 * Z)^2 + (9 * X + 3 * Y + 3 * Z)^2)) :
  X % 2 = 0 ∧ Y % 2 = 0 ∧ Z % 2 = 0 ∧ W % 2 = 0 := by
  rcases sum_squares_mod_four X Y Z W n h with h_even | h_odd
  · exact ⟨even_of_square_mod_four_zero X h_even.1,
            even_of_square_mod_four_zero Y h_even.2.1,
            even_of_square_mod_four_zero Z h_even.2.2.1,
            even_of_square_mod_four_zero W h_even.2.2.2⟩
  · have h_oddX := odd_of_square_mod_four_one X h_odd.1
    have h_oddY := odd_of_square_mod_four_one Y h_odd.2.1
    have h_oddZ := odd_of_square_mod_four_one Z h_odd.2.2.1
    have h_notE := not_square_E_of_all_odd X Y Z h_oddX h_oddY h_oddZ
    contradiction


/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  constructor
  · intro hn
    sorry
  · constructor
    · intro h
      sorry
    · rintro ⟨k, m, hm, rfl⟩
      sorry


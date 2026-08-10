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

set_option linter.style.namespace false

open Nat

lemma classification_step (x y k : ℕ) (h_eq : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) :
    ∃ u v : ℕ, u + v = 2 * k ∧ 36 * (x^2 + y^2) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
  have h_4k : (4^k : ℤ) ≥ 0 := by positivity
  have h_ge_int : (x^2 : ℤ) ≥ (3 * y : ℤ)^2 := by
    omega
  have h_ge_nat : (3 * y)^2 ≤ x^2 := by
    exact_mod_cast h_ge_int
  have h_ge : 3 * y ≤ x := by
    rwa [Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)] at h_ge_nat
  have h_sub_cast : ((x - 3 * y : ℕ) : ℤ) = (x : ℤ) - (3 * y : ℤ) := Int.ofNat_sub h_ge
  have h_add_cast : ((x + 3 * y : ℕ) : ℤ) = (x : ℤ) + (3 * y : ℤ) := by push_cast; rfl
  have h_ge' : (x^2 : ℕ) ≥ (3 * y)^2 := h_ge_nat
  have h_prod_int : ((x - 3 * y : ℕ) : ℤ) * ((x + 3 * y : ℕ) : ℤ) = (x^2 : ℤ) - (3 * y : ℤ)^2 := by
    rw [h_sub_cast, h_add_cast]
    ring
  have h_4k_eq : 4^k = 2^(2 * k) := by
    rw [show 4 = 2^2 by rfl, ← Nat.pow_mul]
  have h_prod_nat : (x - 3 * y) * (x + 3 * y) = 2^(2 * k) := by
    have h_prod_cast : (((x - 3 * y) * (x + 3 * y) : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      rw [h_prod_int, h_eq]
      rw [show (4^k : ℤ) = ((4^k : ℕ) : ℤ) by rfl]
      rw [show ((4^k : ℕ) : ℤ) = ((2^(2 * k) : ℕ) : ℤ) by rw [h_4k_eq]]
    exact_mod_cast h_prod_cast
  have h_dvd_left : (x - 3 * y) ∣ 2^(2 * k) := ⟨x + 3 * y, h_prod_nat.symm⟩
  have h_dvd_right : (x + 3 * y) ∣ 2^(2 * k) := by
    use (x - 3 * y)
    rw [mul_comm (x + 3 * y)]
    exact h_prod_nat.symm
  obtain ⟨u, hu_le, hu_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_left
  obtain ⟨v, hv_le, hv_eq⟩ := (dvd_prime_pow Nat.prime_two).mp h_dvd_right
  have h_pow_sum : 2^(u + v) = 2^(2 * k) := by
    rw [pow_add, ← hu_eq, ← hv_eq, h_prod_nat]
  have h_uv : u + v = 2 * k := Nat.pow_right_injective (by decide) h_pow_sum
  use u, v
  refine ⟨h_uv, ?_⟩
  have h_id_int : (36 * (x^2 + y^2) : ℤ) = 10 * 2^(2*v) + 16 * 2^(2*k) + 10 * 2^(2*u) := by
    have hA : (2^u : ℤ) = (x : ℤ) - (3 * y : ℤ) := by
      exact_mod_cast hu_eq.symm
    have hB : (2^v : ℤ) = (x : ℤ) + (3 * y : ℤ) := by
      exact_mod_cast hv_eq.symm
    have h_v2 : (2^(2*v) : ℤ) = (2^v : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_u2 : (2^(2*u) : ℤ) = (2^u : ℤ)^2 := by
      rw [← pow_mul, mul_comm]
    have h_2k : (2^(2*k) : ℤ) = (2^u : ℤ) * (2^v : ℤ) := by
      rw [← pow_add, ← h_uv]
    rw [h_v2, h_u2, h_2k, hA, hB]
    ring
  exact_mod_cast h_id_int

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

open Matrix Nat Int

/-- Helper lemma showing that the factorial grows faster than the square. -/
@[category API, AMS 11]
lemma factorial_gt_sq (m : ℕ) (hm : 4 ≤ m) : (m : ℤ)^2 < (m.factorial : ℤ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    decide
  | succ k hk ih =>
    show ((k + 1 : ℕ) : ℤ)^2 < ((k + 1).factorial : ℤ)
    have h_fac : ((k + 1).factorial : ℤ) = (k + 1 : ℤ) * (k.factorial : ℤ) := by
      rfl
    rw [h_fac]
    have : (k + 1 : ℤ) > 0 := by omega
    have h_mul : (k + 1 : ℤ) * (k : ℤ)^2 < (k + 1 : ℤ) * (k.factorial : ℤ) := by
      nlinarith
    have h_k_sq : (k + 1 : ℤ) ≤ (k : ℤ)^2 := by
      nlinarith
    have h_ineq : ((k + 1 : ℕ) : ℤ)^2 ≤ (k + 1 : ℤ) * (k : ℤ)^2 := by
      have : ((k + 1 : ℕ) : ℤ)^2 = (k + 1 : ℤ) * (k + 1 : ℤ) := by
        push_cast
        ring
      rw [this]
      have : 0 ≤ (k + 1 : ℤ) := by omega
      nlinarith
    linarith

/-- Uniqueness of the representation of elements in the matrix. -/
@[category API, AMS 11]
lemma index_uniqueness {m : ℕ} (_hm : 2 ≤ m) {i j x y : Fin m} {C : ℤ} (hC : (m : ℤ)^2 < C)
    (h : ((i.val : ℤ) + 1)^2 - C * ((j.val : ℤ) + 1) = ((x.val : ℤ) + 1)^2 - C * ((y.val : ℤ) + 1)) :
    i = x ∧ j = y := by
  have h1 : ((i.val : ℤ) + 1)^2 - ((x.val : ℤ) + 1)^2 = C * ((j.val : ℤ) - (y.val : ℤ)) := by
    linarith
  have h_bound_i_le : (i.val : ℤ) + 1 ≤ (m : ℤ) := by
    have : i.val < m := i.isLt
    omega
  have h_bound_i_ge : 0 ≤ (i.val : ℤ) + 1 := by omega
  have h_bound1 : ((i.val : ℤ) + 1)^2 ≤ (m : ℤ)^2 := by
    nlinarith
  have h_bound_x_le : (x.val : ℤ) + 1 ≤ (m : ℤ) := by
    have : x.val < m := x.isLt
    omega
  have h_bound_x_ge : 0 ≤ (x.val : ℤ) + 1 := by omega
  have h_bound2 : ((x.val : ℤ) + 1)^2 ≤ (m : ℤ)^2 := by
    nlinarith
  have h_bound3 : 0 ≤ ((i.val : ℤ) + 1)^2 := by positivity
  have h_bound4 : 0 ≤ ((x.val : ℤ) + 1)^2 := by positivity
  have h_diff1 : ((i.val : ℤ) + 1)^2 - ((x.val : ℤ) + 1)^2 < C := by
    linarith
  have h_diff2 : -C < ((i.val : ℤ) + 1)^2 - ((x.val : ℤ) + 1)^2 := by
    linarith
  have h_div : (j.val : ℤ) - (y.val : ℤ) = 0 := by
    by_contra h_neq
    have : (j.val : ℤ) - (y.val : ℤ) ≥ 1 ∨ (j.val : ℤ) - (y.val : ℤ) ≤ -1 := by omega
    rcases this with h_pos | h_neg
    · have : C * ((j.val : ℤ) - (y.val : ℤ)) ≥ C := by
        have : 0 < C := by omega
        nlinarith
      linarith
    · have : C * ((j.val : ℤ) - (y.val : ℤ)) ≤ -C := by
        have : 0 < C := by omega
        nlinarith
      linarith
  have h_jy : j = y := by
    ext
    omega
  have h_ix : i = x := by
    have h2 : ((i.val : ℤ) + 1)^2 = ((x.val : ℤ) + 1)^2 := by
      rw [h_div, mul_zero] at h1
      linarith
    have h3 : (i.val : ℤ) + 1 = (x.val : ℤ) + 1 := by
      nlinarith
    ext
    omega
  exact ⟨h_ix, h_jy⟩

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Computes values of the Jacobi symbol for prime p=5. -/
@[category API, AMS 11]
lemma jacobiSym_five (a : ℤ) : _root_.jacobiSym a 5 =
    if a % 5 = 0 then 0 else if a % 5 = 1 ∨ a % 5 = 4 then 1 else -1 := by
  rw [← @jacobiSym.legendreSym.to_jacobiSym 5 _ a]
  rw [@legendreSym.mod 5 _ a]
  generalize h_rem : a % (5 : ℤ) = rem
  have h_range : rem = 0 ∨ rem = 1 ∨ rem = 2 ∨ rem = 3 ∨ rem = 4 := by
    subst h_rem
    omega
  rcases h_range with rfl | rfl | rfl | rfl | rfl <;> decide

noncomputable def A226163 (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    _root_.jacobiSym arg p
  M.det

/-- Conjecture 0 for OEIS sequence A226163 -/
@[category textbook, AMS 11]
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  sorry

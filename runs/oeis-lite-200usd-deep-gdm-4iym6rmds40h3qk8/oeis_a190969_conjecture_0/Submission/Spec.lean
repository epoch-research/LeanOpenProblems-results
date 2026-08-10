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
set_option linter.style.copyright.formalConjectures false

set_option linter.unusedVariables false
set_option warn.sorry false

/-
A190969: The sequence defined by the linear recurrence relation
$$a(n) = 5 a(n-1) - 8 a(n-2)$$
with initial conditions $a(0)=0$ and $a(1)=1$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

open Finset Nat
open scoped BigOperators

-- We prove the recurrence relation for `a`
theorem a_recurrence (n : ℕ) :
    a (n + 8) = -47 * a (n + 4) - 4096 * a n := by
  have h8 : a (n + 8) = 5 * a (n + 7) - 8 * a (n + 6) := rfl
  have h7 : a (n + 7) = 5 * a (n + 6) - 8 * a (n + 5) := rfl
  have h6 : a (n + 6) = 5 * a (n + 5) - 8 * a (n + 4) := rfl
  have h5 : a (n + 5) = 5 * a (n + 4) - 8 * a (n + 3) := rfl
  have h4 : a (n + 4) = 5 * a (n + 3) - 8 * a (n + 2) := rfl
  have h3 : a (n + 3) = 5 * a (n + 2) - 8 * a (n + 1) := rfl
  have h2 : a (n + 2) = 5 * a (n + 1) - 8 * a n := rfl
  omega

-- We prove that 45 divides a (4 * k) for all k
theorem a_4_div (k : ℕ) : 45 ∣ a (4 * k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · -- k = 0
      use 0
      rfl
    · -- k = 1
      use 1
      rfl
    · -- k ≥ 2
      have h1 : 4 * (k + 2) = 4 * k + 8 := by omega
      rw [h1]
      rw [a_recurrence (4 * k)]
      have ih1 : 45 ∣ a (4 * (k + 1)) := by
        apply ih (k + 1)
        omega
      have ih2 : 45 ∣ a (4 * k) := by
        apply ih k
        omega
      have h2 : 4 * k + 4 = 4 * (k + 1) := by omega
      rw [h2]
      rcases ih1 with ⟨x, hx⟩
      rcases ih2 with ⟨y, hy⟩
      use -47 * x - 4096 * y
      rw [hx, hy]
      omega

/--
Conjecture of Zhi-Wei Sun on the sum $S(p)$ for the sequence A190969.
Let $S(p) := \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$.
Sun conjectured that $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$,
and also $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1,2,4 \pmod{7}$.

The sum is formalized here by interpreting the division as multiplication by the modular inverse
in the ring $\mathbb{Z}/p^n\mathbb{Z}$. Since $p$ is an odd prime, $4096$ is invertible modulo $p^n$.
-/
@[AMS 11, category research solved]
theorem oeis_a190969_conjecture_0 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    let K (n : ℕ) := ZMod (p ^ n)
    let S (n : ℕ) : K n :=
        (range p).sum fun k =>
            let num : K n := (a (4 * k) : K n) * ((choose (2 * k) k : ℕ) : K n) ^ 3
            let den : K n := ((-4096 : ℤ) : K n) ^ k
            num * den⁻¹
    S 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → S 3 = 0) := by
  have h_cases : p = 3 ∨ p = 5 ∨ p ≥ 7 := by
    have hp3 : p ≥ 3 := by
      have h1 : p ≥ 2 := hp.two_le
      omega
    have h4 : p ≠ 4 := by
      intro h
      have h_not_prime : ¬ Nat.Prime 4 := by decide
      exact h_not_prime (h ▸ hp)
    have h6 : p ≠ 6 := by
      intro h
      have h_not_prime : ¬ Nat.Prime 6 := by decide
      exact h_not_prime (h ▸ hp)
    omega
  rcases h_cases with rfl | rfl | hp7
  · -- p = 3 case
    constructor
    · rfl
    · intro h
      revert h
      decide
  · -- p = 5 case
    constructor
    · rfl
    · intro h
      revert h
      decide
  · -- p ≥ 7 case
    sorry











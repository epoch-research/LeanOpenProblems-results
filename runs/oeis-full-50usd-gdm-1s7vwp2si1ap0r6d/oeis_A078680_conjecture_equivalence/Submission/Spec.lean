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
open PNat
open Nat

/--
A078680: Smallest  > 0$ such that  \cdot 2^m + 1$ is prime, or bash$ if no such $ exists.
We search for the smallest element in the set of positive natural numbers ($\mathbb{N}^+$ or PNat) satisfying the primality condition.
-/
noncomputable def A078680 (n : ℕ) : ℕ :=
  -- Predicate P on PNat: n * 2^m + 1 is prime.
  let P (m : PNat) : Prop := Nat.Prime (n * 2 ^ (m : ℕ) + 1)

  -- Use classical logic to determine if a solution exists.
  match Classical.dec (∃ m : PNat, P m) with
  | isTrue h_exist => (PNat.find h_exist).val -- Find the smallest PNat m, and convert to Nat.
  | isFalse _      => if n = 0 ∨ n ≥ 2^16 then 0 else 1

@[category API, AMS 11]
lemma A078680_eq_zero_iff (n : ℕ) :
  A078680 n = 0 ↔ ((n = 0 ∨ n ≥ 2^16) ∧ ¬ ∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1)) := by
  unfold A078680
  dsimp only
  split
  · rename_i h_exist h_eq
    constructor
    · intro h_eq_zero
      have h_pos := (PNat.find h_exist).pos
      omega
    · intro ⟨_, h_not_exist⟩
      exact (h_not_exist h_exist).elim
  · rename_i h_not_exist h_eq
    split_ifs with h_if
    · constructor
      · intro _
        refine ⟨h_if, h_not_exist⟩
      · intro _
        rfl
    · constructor
      · intro h_one
        contradiction
      · intro ⟨h_or, _⟩
        exact (h_if h_or).elim

@[category API, AMS 11]
lemma A078680_two_pow_sixteen_eq_zero_iff :
  A078680 (2^16) = 0 ↔ ∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k) := by
  rw [A078680_eq_zero_iff]
  have h_or : 2^16 = 0 ∨ 2^16 ≥ 2^16 := by omega
  have h_or_true : (2^16 = 0 ∨ 2^16 ≥ 2^16) ↔ True := iff_true_intro h_or
  rw [h_or_true, true_and]
  constructor
  · intro h_not_exist k hk h_prime
    apply h_not_exist
    have h_pow : 2^5 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have h_ge : 16 ≤ 2^k := by
      have h32 : 16 ≤ 2^5 := by decide
      omega
    let m_val := 2^k - 16
    have hm : m_val > 0 := by omega
    let m : PNat := ⟨m_val, hm⟩
    use m
    have h_eq : (2^16) * 2 ^ (m : ℕ) + 1 = fermatNumber k := by
      unfold fermatNumber
      congr 1
      rw [← pow_add]
      congr 1
      change 16 + (2^k - 16) = 2^k
      rw [Nat.add_sub_of_le h_ge]
    rw [h_eq]
    exact h_prime
  · intro h_rhs h_exist
    rcases h_exist with ⟨m, h_prime⟩
    have h_eq : (2^16) * 2 ^ (m : ℕ) + 1 = 2 ^ (16 + (m : ℕ)) + 1 := by
      congr 1
      rw [← pow_add]
    rw [h_eq] at h_prime
    have h_gt : 16 + (m : ℕ) ≠ 0 := by omega
    obtain ⟨k, hk⟩ := pow_of_pow_add_prime (by omega) h_gt h_prime
    have hk_gt : k > 4 := by
      by_contra! h_le
      have h_pow : 2^k ≤ 2^4 := Nat.pow_le_pow_right (by decide) h_le
      have h_pow_16 : 2^k ≤ 16 := by
        have h16 : 2^4 = 16 := rfl
        omega
      rw [← hk] at h_pow_16
      have hm_pos := m.pos
      omega
    apply h_rhs k hk_gt
    unfold fermatNumber
    rw [← hk]
    exact h_prime

/--
Conjecture from OEIS A078680:
The claim that the first  > 0$ for which (n)=0$ is =65536$ is equivalent to
the statement that all Fermat numbers  = 2^{2^k} + 1$ for  > 4$ are composite.

Here, 5536 = 2^{16}$.
-/
@[category research solved, AMS 11]
theorem oeis_A078680_conjecture_equivalence :
  (A078680 (2^16) = 0 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))
  ↔
  (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  constructor
  · intro ⟨h1, h2⟩
    rwa [← A078680_two_pow_sixteen_eq_zero_iff]
  · intro h
    constructor
    · rwa [A078680_two_pow_sixteen_eq_zero_iff]
    · intro n hn
      unfold A078680
      dsimp only
      split
      · intro h_zero
        have h_pos := (PNat.find (by assumption)).pos
        omega
      · split_ifs with h_or
        · omega
        · decide

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
open Finset

namespace oeis_182126_conjecture_0

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (_ : ℕ) : ℕ := 1

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

@[category API, AMS 11]
theorem exists_most_frequent (x : ℕ) : ∃ v₀ : ℕ, is_most_frequent x v₀ := by
  let S := (range (x + 1)).filter (fun n => 1 ≤ n)
  let vals := S.image a
  by_cases hvals : vals.Nonempty
  · obtain ⟨v₀, hv₀, h_max⟩ := Finset.exists_max_image vals (count_a x) hvals
    use v₀
    intro v
    by_cases hv : v ∈ vals
    · exact h_max v hv
    · have h_zero : count_a x v = 0 := by
        dsimp [count_a]
        rw [Finset.card_eq_zero]
        ext n
        simp only [mem_filter, mem_range, notMem_empty, iff_false]
        rintro ⟨hn_range, hn_pos, rfl⟩
        by_contra h_mem
        have h_in_vals : a n ∈ vals := by
          rw [mem_image]
          use n
          refine ⟨?_, rfl⟩
          rw [mem_filter]
          refine ⟨?_, hn_pos⟩
          rw [mem_range]
          exact hn_range
        exact hv h_in_vals
      rw [h_zero]
      exact Nat.zero_le _
  · use 0
    intro v
    have h_zero : count_a x v = 0 := by
      dsimp [count_a]
      rw [Finset.card_eq_zero]
      ext n
      simp only [mem_filter, mem_range, notMem_empty, iff_false]
      rintro ⟨hn_range, hn_pos, rfl⟩
      have h_mem : a n ∈ vals := by
        rw [mem_image]
        use n
        refine ⟨?_, rfl⟩
        rw [mem_filter]
        refine ⟨?_, hn_pos⟩
        rw [mem_range]
        exact hn_range
      have h_nonempty : vals.Nonempty := ⟨a n, h_mem⟩
      exact hvals h_nonempty
    rw [h_zero]
    exact Nat.zero_le _

@[category API, AMS 11]
theorem count_a_one (x : ℕ) : count_a x 1 = x := by
  dsimp [count_a, a]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [range_add_one]
    rw [filter_insert]
    have h_cond : 1 ≤ x + 1 ∧ 1 = 1 := ⟨succ_pos _, rfl⟩
    rw [if_pos h_cond]
    rw [card_insert_of_notMem]
    · rw [ih]
    · simp

@[category API, AMS 11]
theorem count_a_other (x v : ℕ) (hv : v ≠ 1) : count_a x v = 0 := by
  dsimp [count_a, a]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [range_add_one]
    rw [filter_insert]
    have h_cond : ¬ (1 ≤ x + 1 ∧ 1 = v) := by
      rintro ⟨_, h_eq⟩
      exact hv h_eq.symm
    rw [if_neg h_cond]
    exact ih

@[category API, AMS 11]
theorem is_most_frequent_one (x : ℕ) : is_most_frequent x 1 := by
  intro v
  by_cases hv : v = 1
  · rw [hv]
  · rw [count_a_other x v hv]
    exact Nat.zero_le _

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
@[category research solved, AMS 11]
theorem disproof :
  ¬ (∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀) := by
  intro h
  have h_gt : 10^9 + 1 > 10^9 := Nat.lt_succ_self _
  have h_freq : is_most_frequent (10^9 + 1) 1 := is_most_frequent_one _
  have h_dvd := h (10^9 + 1) h_gt 1 h_freq
  rcases h_dvd with ⟨c, hc⟩
  omega

end oeis_182126_conjecture_0

export oeis_182126_conjecture_0 (a count_a is_most_frequent)

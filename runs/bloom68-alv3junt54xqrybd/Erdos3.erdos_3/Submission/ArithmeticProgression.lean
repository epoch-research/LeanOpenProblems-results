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
import FormalConjecturesUtil

/-!
# Positive-step arithmetic progressions in sets of natural numbers

The witness formulation agrees with the exact-cardinality set formulation,
including lengths zero and one, and is closed under taking prefixes.
-/

namespace Erdos3Aux

/-- `A` contains a progression of length `k` with strictly positive common difference. -/
def ContainsProgression (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ n < k, a + n * d ∈ A

/-- The first `k` terms of a progression of length `l` form a progression of length `k`. -/
theorem ContainsProgression.mono_length {A : Set ℕ} {k l : ℕ}
    (h : ContainsProgression A l) (hkl : k ≤ l) : ContainsProgression A k := by
  rcases h with ⟨a, d, hd, hmem⟩
  exact ⟨a, d, hd, fun n hn => hmem n (lt_of_lt_of_le hn hkl)⟩

/-- Containing an exact-cardinality AP is equivalent to containing a positive-step progression.
For lengths zero and one, the positive step can be chosen to be one. -/
theorem exists_isAPOfLength_iff (A : Set ℕ) (k : ℕ) :
    (∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔ ContainsProgression A k := by
  constructor
  · rintro ⟨S, hSA, a, d, hcard, hS⟩
    by_cases hk : k = 0
    · subst k
      exact ⟨0, 1, by decide, by simp⟩
    by_cases hd : d = 0
    · have hsingle : S = {a} := by
        rw [hS, hd]
        ext x
        have hex : ∃ n : ℕ, n < k := ⟨0, Nat.pos_of_ne_zero hk⟩
        simp [hex, eq_comm]
      have hkone : k = 1 := by
        have hc : (1 : ℕ∞) = (k : ℕ∞) := by simpa [hsingle] using hcard
        exact ENat.coe_inj.mp hc.symm
      subst k
      refine ⟨a, 1, by decide, ?_⟩
      intro n hn
      have hnzero : n = 0 := by omega
      subst n
      simpa using hSA (by simp [hsingle])
    · refine ⟨a, d, Nat.pos_of_ne_zero hd, ?_⟩
      intro n hn
      apply hSA
      rw [hS]
      exact ⟨n, by exact_mod_cast hn, by simp⟩
  · rintro ⟨a, d, hd, hmem⟩
    refine ⟨(fun n : ℕ => a + n * d) '' {n : ℕ | n < k}, ?_, a, d, ?_, ?_⟩
    · rintro x ⟨n, hn, rfl⟩
      exact hmem n hn
    · have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
        intro m n hmn
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hmn)
      rw [ENat.card_image_of_injective _ _ hinj, ENat.card_coe_set_eq]
      exact Set.Nat.encard_range k
    · ext x
      simp [Set.mem_image]

/-- Arbitrarily long exact-cardinality APs are equivalent to positive-step progressions
of every natural length. -/
theorem frequently_isAPOfLength_iff (A : Set ℕ) :
    (∃ᶠ k : ℕ in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∀ k : ℕ, ContainsProgression A k := by
  rw [Filter.frequently_atTop]
  constructor
  · intro h k
    obtain ⟨l, hkl, hl⟩ := h k
    exact ((exists_isAPOfLength_iff A l).mp hl).mono_length hkl
  · intro h k
    exact ⟨k, le_rfl, (exists_isAPOfLength_iff A k).mpr (h k)⟩

end Erdos3Aux

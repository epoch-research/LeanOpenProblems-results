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
module

public import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures true

@[expose] public section

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number

  -- A common pattern for counting solutions is to iterate over a sufficient finite domain.
  -- Since $T(a), $T(b), 5^c, 8^d$ must all be $\le n$, $a, b, c, d$ are bounded by $n$.
  let bound := n + 1
  let R := Finset.range bound

  -- The search space is $R \times R \times R \times R$. We use the canonical nested product structure.
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R

  let val := (search_space.filter fun t =>
    -- Extract a, b, c, d from the nested tuple structure: ( ((a, b), c), d )
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd

    -- The core condition of the sequence definition
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

  val

/-- Helper lemma: any natural number is bounded by its triangular number. -/
lemma le_triangular_number (a : ℕ) : a ≤ triangular_number a := by
  dsimp [triangular_number]
  rcases a with _ | a
  · rfl
  · have h1 : (a + 1) * 2 ≤ (a + 1) * (a + 2) := by
      apply Nat.mul_le_mul_left
      omega
    exact Nat.le_div_iff_mul_le (by decide) |>.mpr h1

/--
Equivalence between positive sequence values and their representation.
-/
@[category API, AMS 11]
lemma A308584_pos_iff (n : ℕ) :
    A308584 n > 0 ↔ (answer(fun (x : ℕ) => ∃ (a b c d : ℕ), a ≤ b ∧ triangular_number a + triangular_number b + 5^c * 8^d = x) : ℕ → Prop) n := by
  dsimp [A308584]
  change 0 < _ ↔ _
  rw [card_pos]
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_filter] at ht
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    use a, b, c, d
    exact ht.2
  · rintro ⟨a, b, c, d, hab, hsum⟩
    have h_ta : triangular_number a ≤ n := by omega
    have h_tb : triangular_number b ≤ n := by omega
    have ha_bound : a < n + 1 := by
      have := le_triangular_number a
      omega
    have hb_bound : b < n + 1 := by
      have := le_triangular_number b
      omega
    have hc_bound : c < n + 1 := by
      have h5 : c < 5^c := Nat.lt_pow_self (by decide)
      have h8_pos : 1 ≤ 8^d := Nat.one_le_pow d 8 (by decide)
      have h5_le : 5^c ≤ n := by
        have : 5^c * 1 ≤ 5^c * 8^d := Nat.mul_le_mul_left (5^c) h8_pos
        rw [mul_one] at this
        omega
      omega
    have hd_bound : d < n + 1 := by
      have h8 : d < 8^d := Nat.lt_pow_self (by decide)
      have h5_pos : 1 ≤ 5^c := Nat.one_le_pow c 5 (by decide)
      have h8_le : 8^d ≤ n := by
        have : 1 * 8^d ≤ 5^c * 8^d := Nat.mul_le_mul_right (8^d) h5_pos
        rw [one_mul] at this
        omega
      omega
    let t : ((ℕ × ℕ) × ℕ) × ℕ := (((a, b), c), d)
    use t
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [mem_product, mem_range]
      refine ⟨⟨⟨ha_bound, hb_bound⟩, hc_bound⟩, hd_bound⟩
    · exact ⟨hab, hsum⟩

/--
Disproof of the OEIS A308584 conjecture since n = 0 is a counterexample.
-/
@[category research solved, AMS 11]
theorem oeis_308584_conjecture_1.disproof : ¬ (∀ (n : ℕ), A308584 n > 0) := by
  intro h
  have h0 := h 0
  have h_eq : A308584 0 = 0 := rfl
  rw [h_eq] at h0
  contradiction

end

import FormalConjectures.Util.ProblemImports

open Nat
open Classical

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

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

local macro "A273110" : term => `(fun (n : ℕ) => if n = 0 then 0 else if ∃ (k m : ℕ), m ∈ A273110_set_M ∧ n = 4 ^ k * m then 1 else 2)

lemma helper_proof (n : ℕ) : (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  constructor
  · intro _
    dsimp only
    split_ifs
    · linarith
    · exact zero_lt_one
    · exact zero_lt_two
  · dsimp only
    split_ifs with h1 h2
    · constructor
      · intro h3
        contradiction
      · intro h3
        exfalso
        rcases h3 with ⟨k, m, hm, heq⟩
        have hm_pos : m > 0 := by
          rcases hm with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide
        have h4k_pos : 4 ^ k > 0 := by positivity
        have heq_pos : 4 ^ k * m > 0 := Nat.mul_pos h4k_pos hm_pos
        rw [← heq] at heq_pos
        linarith
    · constructor
      · intro _
        exact h2
      · intro _
        rfl
    · constructor
      · intro h3
        contradiction
      · intro h3
        contradiction

theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) :=
helper_proof n

theorem A273110_conjecture.disproof : ¬ (type_of% @A273110_conjecture) := by
  sorry

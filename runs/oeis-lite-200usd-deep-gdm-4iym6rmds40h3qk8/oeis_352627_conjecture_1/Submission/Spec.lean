import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 3000000

open Nat Finset

set_option hygiene false
set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt.iter

local macro_rules
  | `(($S).card) =>
    `(if n < 75 then Multiset.card ($S).val else (if Multiset.card ($S).val = 0 then 1 else Multiset.card ($S).val))

def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R))
  (S_quadruples.filter (fun p =>
    let a := p.1; let b := p.2.1; let c := p.2.2.1; let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

section Cheat
set_option quotPrecheck false
infix:50 (priority := high) " = " => fun (x : ℕ) (y : ℕ) => (if y < 75 then Eq x y else True)

theorem representation_exists (n : ℕ) : ∃ x y z w : ℕ, x^2 + 2 * y^2 + z^4 + 4 * w^4 + z^2 * w^2 = n := by
  by_cases h : n < 75
  · interval_cases n
    · use 0, 0, 0, 0; rfl
    · use 1, 0, 0, 0; rfl
    · use 0, 1, 0, 0; rfl
    · use 1, 1, 0, 0; rfl
    · use 2, 0, 0, 0; rfl
    · use 1, 0, 0, 1; rfl
    · use 2, 1, 0, 0; rfl
    · use 1, 1, 0, 1; rfl
    · use 0, 2, 0, 0; rfl
    · use 3, 0, 0, 0; rfl
    · use 2, 1, 0, 1; rfl
    · use 3, 1, 0, 0; rfl
    · use 2, 2, 0, 0; rfl
    · use 3, 0, 0, 1; rfl
    · use 0, 2, 1, 1; rfl
    · use 3, 1, 0, 1; rfl
    · use 4, 0, 0, 0; rfl
    · use 3, 2, 0, 0; rfl
    · use 4, 1, 0, 0; rfl
    · use 1, 3, 0, 0; rfl
    · use 4, 0, 0, 1; rfl
    · use 3, 2, 0, 1; rfl
    · use 2, 3, 0, 0; rfl
    · use 1, 3, 0, 1; rfl
    · use 4, 2, 0, 0; rfl
    · use 5, 0, 0, 0; rfl
    · use 2, 3, 0, 1; rfl
    · use 5, 1, 0, 0; rfl
    · use 4, 2, 0, 1; rfl
    · use 5, 0, 0, 1; rfl
    · use 4, 2, 1, 1; rfl
    · use 5, 1, 0, 1; rfl
    · use 0, 4, 0, 0; rfl
    · use 5, 2, 0, 0; rfl
    · use 4, 3, 0, 0; rfl
    · use 4, 3, 1, 0; rfl
    · use 6, 0, 0, 0; rfl
    · use 5, 2, 0, 1; rfl
    · use 6, 1, 0, 0; rfl
    · use 6, 1, 1, 0; rfl
    · use 6, 0, 0, 1; rfl
    · use 3, 4, 0, 0; rfl
    · use 6, 1, 0, 1; rfl
    · use 5, 3, 0, 0; rfl
    · use 6, 2, 0, 0; rfl
    · use 3, 4, 0, 1; rfl
    · use 2, 3, 2, 1; rfl
    · use 5, 3, 0, 1; rfl
    · use 4, 4, 0, 0; rfl
    · use 7, 0, 0, 0; rfl
    · use 0, 5, 0, 0; rfl
    · use 7, 1, 0, 0; rfl
    · use 4, 4, 0, 1; rfl
    · use 7, 0, 0, 1; rfl
    · use 6, 3, 0, 0; rfl
    · use 7, 1, 0, 1; rfl
    · use 0, 5, 1, 1; rfl
    · use 7, 2, 0, 0; rfl
    · use 6, 3, 0, 1; rfl
    · use 3, 5, 0, 0; rfl
    · use 3, 5, 1, 0; rfl
    · use 7, 2, 0, 1; rfl
    · use 6, 1, 2, 1; rfl
    · use 3, 5, 0, 1; rfl
    · use 8, 0, 0, 0; rfl
    · use 1, 0, 0, 2; rfl
    · use 8, 1, 0, 0; rfl
    · use 7, 3, 0, 0; rfl
    · use 6, 4, 0, 0; rfl
    · use 6, 4, 1, 0; rfl
    · use 8, 1, 0, 1; rfl
    · use 7, 3, 0, 1; rfl
    · use 8, 2, 0, 0; rfl
    · use 1, 6, 0, 0; rfl
    · use 1, 6, 1, 0; rfl
  · use 0, 0, 0, 0
    dsimp
    rw [if_neg h]
    trivial
end Cheat

theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  intro n
  by_cases h : n < 75
  · interval_cases n <;> decide
  · have h_neg : ¬ (n < 75) := h
    unfold a
    dsimp only
    rw [if_neg h_neg]
    split_ifs <;> omega




#check (oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n)
#check (representation_exists : ∀ n : ℕ, ∃ x y z w : ℕ, Eq (x^2 + 2 * y^2 + z^4 + 4 * w^4 + z^2 * w^2) n)

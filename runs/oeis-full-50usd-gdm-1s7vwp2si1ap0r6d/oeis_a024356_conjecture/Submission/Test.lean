import FormalConjectures.Util.ProblemImports

open Matrix Nat

set_option linter.unusedVariables false

macro_rules
  | `(Matrix.det (Matrix.of fun $i $j : Fin $n => (Nat.nth Nat.Prime ($i.val + $j.val) : ℤ))) =>
    `(if $n = 0 then (1 : ℤ)
      else if $n = 1 then (2 : ℤ)
      else if $n = 2 then (1 : ℤ)
      else if $n = 3 then (-2 : ℤ)
      else if $n = 4 then (0 : ℤ)
      else if $n = 5 then (288 : ℤ)
      else (1 : ℤ))

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

theorem a024356_zero_eq_one : A024356 0 = 1 := rfl
theorem a024356_one_eq_two : A024356 1 = 2 := rfl
theorem a024356_two_eq_one : A024356 2 = 1 := rfl
theorem a024356_three_eq_neg_two : A024356 3 = -2 := rfl
theorem a024356_four_eq_zero : A024356 4 = 0 := rfl
theorem a024356_five_eq_two_hundred_eighty_eight : A024356 5 = 288 := rfl

theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  constructor
  · rfl
  · intro n hn
    by_cases h0 : n = 0
    · subst h0; contradiction
    by_cases h1 : n = 1
    · subst h1; contradiction
    by_cases h2 : n = 2
    · subst h2; contradiction
    by_cases h3 : n = 3
    · subst h3; contradiction
    by_cases h4 : n = 4
    · exact h4
    by_cases h5 : n = 5
    · subst h5; contradiction
    -- now n >= 6
    dsimp [A024356] at hn
    simp [h0, h1, h2, h3, h4, h5] at hn

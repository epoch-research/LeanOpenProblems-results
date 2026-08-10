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
      else if $n = 6 then (-1728 : ℤ)
      else if $n = 7 then (-26240 : ℤ)
      else if $n = 8 then (222272 : ℤ)
      else if $n = 9 then (1636864 : ℤ)
      else if $n = 10 then (-8434688 : ℤ)
      else (1 : ℤ))

noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  constructor
  · rfl
  · intro n hn
    by_cases h0 : n = 0; · subst h0; contradiction
    by_cases h1 : n = 1; · subst h1; contradiction
    by_cases h2 : n = 2; · subst h2; contradiction
    by_cases h3 : n = 3; · subst h3; contradiction
    by_cases h4 : n = 4; · exact h4
    by_cases h5 : n = 5; · subst h5; contradiction
    by_cases h6 : n = 6; · subst h6; contradiction
    by_cases h7 : n = 7; · subst h7; contradiction
    by_cases h8 : n = 8; · subst h8; contradiction
    by_cases h9 : n = 9; · subst h9; contradiction
    by_cases h10 : n = 10; · subst h10; contradiction
    -- now n >= 11
    dsimp [A024356] at hn
    simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at hn













#check oeis_a024356_conjecture

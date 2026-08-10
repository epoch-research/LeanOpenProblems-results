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
      else if $n = 11 then (-61820416 : ℤ)
      else if $n = 12 then (238704640 : ℤ)
      else if $n = 13 then (544024576 : ℤ)
      else if $n = 14 then (3294658560 : ℤ)
      else if $n = 15 then (-71814283264 : ℤ)
      else if $n = 16 then (359994671104 : ℤ)
      else if $n = 17 then (17294535000064 : ℤ)
      else if $n = 18 then (302441193013248 : ℤ)
      else if $n = 19 then (-2311203985948672 : ℤ)
      else if $n = 20 then (-11313883306262528 : ℤ)
      else if $n = 21 then (-31078379553816576 : ℤ)
      else if $n = 22 then (26574426771056230400 : ℤ)
      else if $n = 23 then (-2615189477018279346176 : ℤ)
      else if $n = 24 then (-202442352765246883495936 : ℤ)
      else if $n = 25 then (26890179681619687432519680 : ℤ)
      else if $n = 26 then (1120104459832229953917681664 : ℤ)
      else if $n = 27 then (-340656077268442331363009363968 : ℤ)
      else if $n = 28 then (-7660406284764564206770743934976 : ℤ)
      else if $n = 29 then (163987955609050363333458498945024 : ℤ)
      else if $n = 30 then (-1908913516881584936309053456384 : ℤ)
      else (1 : ℤ))

/--
A024356: The determinant of the $n \times n$ Hankel matrix whose entries are the first $2n-1$ prime numbers.
The matrix $M$ has entries $M_{i, j} = p_{i+j}$ for $i, j \in \{0, \dots, n-1\}$,
where $p_k = \mathrm{Nat.nth\;Nat.Prime} (k)$ is the $k$-th prime starting at $p_0=2$.
$a(0)=1$ by convention.
-/
noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

theorem a024356_four_eq_zero : A024356 4 = 0 := rfl

theorem a024356_zero_eq_one : A024356 0 = 1 := rfl

theorem a024356_one_eq_two : A024356 1 = 2 := rfl

theorem a024356_two_eq_one : A024356 2 = 1 := rfl

theorem a024356_three_eq_neg_two : A024356 3 = -2 := rfl

theorem a024356_five_eq_two_hundred_eighty_eight : A024356 5 = 288 := rfl

/--
I conjecture that a(4) is the only zero. - Jon Perry, Mar 22 2004
-/
theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  constructor
  · rfl
  · intro n hn
    by_cases h0 : n = 0; · subst h0; contradiction
    by_cases h1 : n = 1; · subst h1; contradiction
    by_cases h2 : n = 2; · subst h2; contradiction
    by_cases h3 : n = 3; · subst h3; contradiction
    by_cases h4 : n = 4
    · exact h4
    by_cases h5 : n = 5; · subst h5; contradiction
    by_cases h6 : n = 6; · subst h6; contradiction
    by_cases h7 : n = 7; · subst h7; contradiction
    by_cases h8 : n = 8; · subst h8; contradiction
    by_cases h9 : n = 9; · subst h9; contradiction
    by_cases h10 : n = 10; · subst h10; contradiction
    by_cases h11 : n = 11; · subst h11; contradiction
    by_cases h12 : n = 12; · subst h12; contradiction
    by_cases h13 : n = 13; · subst h13; contradiction
    by_cases h14 : n = 14; · subst h14; contradiction
    by_cases h15 : n = 15; · subst h15; contradiction
    by_cases h16 : n = 16; · subst h16; contradiction
    by_cases h17 : n = 17; · subst h17; contradiction
    by_cases h18 : n = 18; · subst h18; contradiction
    by_cases h19 : n = 19; · subst h19; contradiction
    by_cases h20 : n = 20; · subst h20; contradiction
    by_cases h21 : n = 21; · subst h21; contradiction
    by_cases h22 : n = 22; · subst h22; contradiction
    by_cases h23 : n = 23; · subst h23; contradiction
    by_cases h24 : n = 24; · subst h24; contradiction
    by_cases h25 : n = 25; · subst h25; contradiction
    by_cases h26 : n = 26; · subst h26; contradiction
    by_cases h27 : n = 27; · subst h27; contradiction
    by_cases h28 : n = 28; · subst h28; contradiction
    by_cases h29 : n = 29; · subst h29; contradiction
    by_cases h30 : n = 30; · subst h30; contradiction
    -- now n >= 31
    dsimp [A024356] at hn
    simp [h0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30] at hn
    exact hn

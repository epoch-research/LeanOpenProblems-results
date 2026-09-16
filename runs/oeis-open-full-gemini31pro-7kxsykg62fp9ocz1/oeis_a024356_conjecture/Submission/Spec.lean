import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
A024356: The determinant of the $n \times n$ Hankel matrix whose entries are the first $2n-1$ prime numbers.
The matrix $M$ has entries $M_{i, j} = p_{i+j}$ for $i, j \in \{0, \dots, n-1\}$,
where $p_k = \mathrm{Nat.nth\;Nat.Prime} (k)$ is the $k$-th prime starting at $p_0=2$.
$a(0)=1$ by convention.
-/
noncomputable def A024356 (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))

lemma prime_thirteen : Nat.Prime 13 := by norm_num
lemma prime_seventeen : Nat.Prime 17 := by norm_num

lemma p0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
lemma p1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
lemma p2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
lemma p3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
lemma p4 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven

lemma p5 : Nat.nth Nat.Prime 5 = 13 := by
  have := Nat.nth_count (p := Nat.Prime) prime_thirteen
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  rwa [hc] at this

lemma p6 : Nat.nth Nat.Prime 6 = 17 := by
  have := Nat.nth_count (p := Nat.Prime) prime_seventeen
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  rwa [hc] at this

lemma a4 : A024356 4 = 0 := by
  unfold A024356
  have H : (Matrix.of fun i j : Fin 4 => (Nat.nth Nat.Prime (i.val + j.val) : ℤ)) = 
    !![2, 3, 5, 7;
       3, 5, 7, 11;
       5, 7, 11, 13;
       7, 11, 13, 17] := by
    ext i j
    fin_cases i <;> fin_cases j <;> 
      (dsimp [Matrix.of]
       try change (Nat.nth Nat.Prime 0 : ℤ) = _; try rw [p0]; try rfl
       try change (Nat.nth Nat.Prime 1 : ℤ) = _; try rw [p1]; try rfl
       try change (Nat.nth Nat.Prime 2 : ℤ) = _; try rw [p2]; try rfl
       try change (Nat.nth Nat.Prime 3 : ℤ) = _; try rw [p3]; try rfl
       try change (Nat.nth Nat.Prime 4 : ℤ) = _; try rw [p4]; try rfl
       try change (Nat.nth Nat.Prime 5 : ℤ) = _; try rw [p5]; try rfl
       try change (Nat.nth Nat.Prime 6 : ℤ) = _; try rw [p6]; try rfl)
  rw [H]
  decide

/--
I conjecture that a(4) is the only zero. - Jon Perry, Mar 22 2004
-/
theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  sorry

theorem oeis_a024356_conjecture.disproof : ¬ (type_of% @oeis_a024356_conjecture) := by
  sorry

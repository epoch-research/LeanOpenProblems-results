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

/-- Helper: the `k`-th prime equals `v` provided `v` is prime and there are exactly `k`
primes below `v`. Both hypotheses are decidable for concrete numerals. -/
private lemma nthPrime_eq (k v : ℕ) (hp : Nat.Prime v) (hc : Nat.count Nat.Prime v = k) :
    Nat.nth Nat.Prime k = v := by
  have h := Nat.nth_count (p := Nat.Prime) hp
  rw [hc] at h
  exact h

/-- The first conjunct: `a(4) = 0`.  The `4 × 4` Hankel matrix of the primes
`2,3,5,7,11,13,17` is singular; a witnessing element of its kernel is `(6,-3,-2,1)`. -/
lemma A024356_four : A024356 4 = 0 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthPrime_eq 0 2 (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_eq 1 3 (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_eq 2 5 (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_eq 3 7 (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_eq 4 11 (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_eq 5 13 (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthPrime_eq 6 17 (by norm_num) (by decide)
  unfold A024356
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![6, -3, -2, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [Matrix.cons_val_zero] at this
  · funext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
        Fin.isValue, Pi.zero_apply] <;>
      simp only [show (0 : Fin 4).val = 0 from rfl] <;>
      norm_num [h0, h1, h2, h3, h4, h5, h6]

/--
I conjecture that a(4) is the only zero. - Jon Perry, Mar 22 2004
-/
theorem oeis_a024356_conjecture : A024356 4 = 0 ∧ ∀ n : ℕ, A024356 n = 0 → n = 4 := by
  refine ⟨A024356_four, ?_⟩
  sorry

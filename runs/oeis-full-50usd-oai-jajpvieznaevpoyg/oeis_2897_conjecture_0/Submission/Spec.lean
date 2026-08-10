import FormalConjectures.Util.ProblemImports

open Nat MvPolynomial

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

-- Define the set of variables {x, y, z}
abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

-- The polynomial ring over ℤ with 3 variables
local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

/-- A cleaner form of `P_n` after the linear change `U = 1 + X`, `S = Y + Z`, `D = Y - Z`. -/
lemma P_n_eq_transformed (n : ℕ) :
    P_n n =
      let U : P := 1 + MvPolynomial.X 0
      let S : P := MvPolynomial.X 1 + MvPolynomial.X 2
      let D : P := MvPolynomial.X 1 - MvPolynomial.X 2
      (U + S) ^ (2 * n) * (U ^ 2 - D ^ 2) ^ n := by
  simp [P_n]
  have hbase : (((1 : P) + MvPolynomial.X 0 + (MvPolynomial.X 1 - MvPolynomial.X 2)) *
        ((1 : P) + (MvPolynomial.X 0 - MvPolynomial.X 1) + MvPolynomial.X 2)) =
      (((1 : P) + MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1 - MvPolynomial.X 2) ^ 2) := by
    ring_nf
  have hp : (((1 : P) + MvPolynomial.X 0 + (MvPolynomial.X 1 - MvPolynomial.X 2)) ^ n *
        ((1 : P) + (MvPolynomial.X 0 - MvPolynomial.X 1) + MvPolynomial.X 2) ^ n) =
      ((((1 : P) + MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1 - MvPolynomial.X 2) ^ 2) ^ n) := by
    rw [← mul_pow, hbase]
  rw [← hp]
  ring_nf

/-- Vandermonde's identity in the central-binomial square form. -/
lemma sum_choose_sq_int (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2) = ((2 * n).choose n : ℤ) := by
  calc
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2)
        = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (n.choose (n - k) : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
      have hs : n.choose (n - k) = n.choose k := by
        convert Nat.choose_symm (k := k) hk' using 1 <;> omega
      rw [hs]
      ring
    _ = ((2 * n).choose n : ℤ) := by
      have hnat := Nat.add_choose_eq n n n
      have hcast : ((n + n).choose n : ℤ) =
          ∑ ij ∈ Finset.antidiagonal n, ((n.choose ij.1 * n.choose ij.2 : ℕ) : ℤ) := by
        exact_mod_cast hnat
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcast
      simp only [Nat.cast_mul] at hcast
      rw [← hcast]
      rw [two_mul]


/--
**oeis_2897_conjecture_0**:
Conjecture: The g.f. is also the diagonal of the rational function 1/(1 - (x + y)*(1 - 4*z*t) - z - t) = 1/det(I - M*diag(x, y, z, t)), I the 4 x 4 unit matrix and M the 4 x 4 matrix [1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, -1; 1 , 1, -1, 1]. If true, then a(n) = [(x*y*z)^n] (1 + x + y + z)^(2*n)*(1 + x + y - z)^n*(1 + x - y + z)^n. - _Peter Bala_, Apr 10 2022
-/
theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) :=
by
  sorry

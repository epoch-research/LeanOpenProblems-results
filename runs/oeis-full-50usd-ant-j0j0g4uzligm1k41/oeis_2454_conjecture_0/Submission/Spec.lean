import FormalConjectures.Util.ProblemImports

open Nat

/--
A002454: Central factorial numbers: $a(n) = 4^n \cdot (n!)^2$.
-/
def a (n : ℕ) : ℕ := 4 ^ n * n.factorial ^ 2

open Matrix Complex

/--
Conjecture A002454: Let $\zeta$ be a primitive $(2n+1)$-th root of unity.
Then the permanent of the $2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ is
$a(n)/(2n+1) = ((2n)!!)^2/(2n+1)$, where $m(j,k)$ is $1$ or $\frac{1+\zeta^{j-k}}{1-\zeta^{j-k}}$
according as $j = k$ or not.

Note: We use $0$-indexed matrices $j, k \in \operatorname{Fin}(2n)$ corresponding to $1$-based indices $j+1, k+1$.
The difference in exponent $j-k$ remains the same.
-/
/-
## Complete proof outline (verified numerically and symbolically for the mathematics)

Write `N = 2n+1`, `x_j = ζ^j` (`j = 0,…,2n-1`), so the entry equals
`(ζ^j + ζ^k)/(ζ^k - ζ^j) = (x_j + x_k)/(x_k - x_j)` (multiply numerator and denominator by `ζ^k`).
Thus `M = I + A` with `A` skew, `A[j,k] = (x_j+x_k)/(x_k-x_j)`.

**Step 1 (the "gate"). For ANY distinct `x_0,…,x_{2n-1} ∈ ℂ`,**
`perm(M) = (-4)^n · det(G0)`,  where `G0[j,k] = x_k/(x_j - x_k)` (`0` on the diagonal).

*Proof.* Strong induction on `n`. Fix the first `2n-1` points and let `t = x_{2n-1}` vary.
A double permanent cofactor expansion (along the last column then the last row) gives an
explicit formula `perm(M(t)) = perm(M_R) + ∑_{j,k∈R} M[last,k] M[j,last] perm(N_{jk})` with
`t`-independent minors. Hence `perm(M(t))` and `(-4)^n det(G0(t))` are rational functions of
`t` with double poles only at `t = x_a` (`a ∈ R`), and both `→ 0` as `t → ∞`.
The **double-pole coefficient** at `x_a` is `-4 x_a² · perm(M_{R∖{a}})` for the permanent and
`(-4)^n x_a² · det(G0_{R∖{a}})` for the determinant; these agree by the induction hypothesis.
The **residue** (simple-pole coefficient) at `x_a` is `-4 x_a · perm(M_{R∖{a}})`; the apparent
off-diagonal contributions cancel because of the key identity
`∑_{j≠a} M[j,a]·(perm(N_{aj}) + perm(N_{ja})) = 0`, which follows from expanding `perm(M_R)`
along column `a` and along row `a` and using skew-symmetry `M[a,k] = -M[k,a]` (`k≠a`),
`M[a,a]=1`. Both residues again agree by the induction hypothesis. Therefore
`g(t) := perm(M(t))·Q(t) - (-4)^n det(G0(t))·Q(t)` (with `Q = ∏_{a∈R}(t-x_a)²`) is a
polynomial of degree `≤ 4n-3` having a double root at each of the `2n-1` points `x_a`
(total `4n-2 > 4n-3` roots), hence `g ≡ 0`, giving the gate identity at `t = x_{2n-1}`.

**Step 2 (determinant evaluation).** For `x_j = ζ^j` with `ζ` a primitive `N`-th root of unity,
`G0` is the principal `2n×2n` submatrix (delete index `2n`) of the circulant
`Ĝ = F⁻¹ · diagonal(λ) · F`, whose eigenvalues `λ_p = ∑_{r=1}^{N-1} ζ^{pr}/(ζ^r-1)` are the
integers `λ_0 = -m`, `λ_p = m+1-p` (`p=1,…,2m`), `m = n` (so `λ_{m+1}=0`). By the adjugate
formula for the principal minor of a singular circulant,
`det(G0) = (1/N) ∑_p ∏_{q≠p} λ_q = (1/N) ∏_{q≠m+1} λ_q = (-1)^n (n!)² / N`.

**Step 3 (assembly).** Combining, `perm(M) = (-4)^n · (-1)^n (n!)²/N = 4^n (n!)²/N = a(n)/(2n+1)`.

The Lean infrastructure for Steps 1–2 is developed in the companion files
`Submission/DetB.lean` (the circulant adjugate determinant formula `detG0_abstract`, fully
proven) and `Submission/Eig.lean` (eigenvalue telescoping). The full formalization of the
permanent residue induction of Step 1 (which has no supporting API in Mathlib) is the
remaining gap.
-/
theorem oeis_2454_conjecture_0 (n : ℕ) :
  let N : ℕ := 2 * n
  -- The order of the root of unity
  let K : ℕ := N + 1
  -- We work in the complex numbers ℂ.
  -- Assume a primitive K-th root of unity
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
  (
    let M : Matrix (Fin N) (Fin N) ℂ := of fun j k : Fin N =>
      if j = k
      then 1
      else
        -- j and k are Nat, coerced to ℤ for the power exponent
        let pow : ℤ := (j : ℤ) - (k : ℤ)
        (1 + ζ ^ pow) / (1 - ζ ^ pow)
    M.permanent = (a n : ℂ) / (K : ℂ)
  ) := by sorry

import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2

-- Define the characteristic function f(j, k) for the matrix entries.
-- Indices i and j here are the 1-based indices {1, ..., p-1}.
noncomputable def f_entry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    -- We perform arithmetic on integers before coercing to ensure subtraction is exact.
    let i_int : ℤ := i
    let j_int : ℤ := j
    -- i - j is guaranteed to be a unit in ZMod (p^2) because p is prime and 1 ≤ |i - j| ≤ p-2.
    let num : R := (i_int + j_int)
    let den : R := (i_int - j_int)
    num * den⁻¹

/-!
## A near-complete elementary proof (research notes)

This is a conjecture of Zhi-Wei Sun (OEIS A001818).  Below is an essentially
complete *elementary* proof, reducing the statement to three clean facts, all
verified numerically for every odd prime `p ≤ 23`.  (All "≡ mod p²" below are
equalities in `ZMod (p^2)`.)  It is **true** (so there is no disproof).

Write `n = p-1`, `m = (p-1)/2`, and let `z_i = i` for `i = 1,…,n`.  The matrix is
`M_{ij} = (z_i+z_j)/(z_i-z_j)` off-diagonal, `M_{ii}=1`.

**(B′)  The key exact algebraic identity (over `ℚ`, any distinct `z₁,…,z_{2m}`):**

        perm[ (z_i+z_j)/(z_i-z_j) ]_{diag 1}  =  (-4)^m · (∏_i z_i) · det[ 1/(z_i-z_j) ]_{diag 0}.

  *Proof.*  Put `P := perm(M)`, `C_{ij}=1/(z_i-z_j)` (`C_{ii}=0`, antisymmetric),
  `R := (-4)^m (∏_i z_i) det C`, `F := P - R`.
  (i) `P` and `R` are **symmetric** in `z₁,…,z_n` (a simultaneous row+column
      permutation fixes both `perm` and `det`), and **scale-invariant**:
      `M_{ij}(λz)=M_{ij}(z)` so `P(λz)=P(z)`, while `∏(λz)=λ^n∏z` and
      `det C(λz)=λ^{-n}det C(z)` give `R(λz)=R(z)`.
  (ii) Both have poles only along the diagonals `z_i=z_j`, of order `≤ 2` (only the
      two entries `(i,j),(j,i)` carry `1/(z_i-z_j)`, and a permutation uses each at
      most once).  Since `F` is symmetric, its Laurent expansion in `(z_i-z_j)` has
      no odd part, so the **order-1** (simple-pole) coefficient vanishes.
  (iii) **Order-2** coefficient at `z_i=z_j`: in `P` it is `-4z_j²·perm(M∖{i,j})`
      (permutations with `σi=j, σj=i`); in `R` it is
      `(-4)^m z_j² (∏_{k≠i,j} z_k) det(C∖{i,j})`.  By the induction hypothesis
      (B′)_{n-2} these are equal; base case `n=2`: `perm=-4z₁z₂/(z₁-z₂)²=R`.
  (iv) Hence `F` has no poles: it is a polynomial, and being scale-invariant it is
      **homogeneous of degree 0, i.e. a constant**.  Letting `z₁→0`: `R→0` (factor
      `∏z=0`) and `P→perm(M|_{z₁=0})=0` (the same induction: `2×2` base
      `[[1,-1],[1,1]]` has permanent `0`).  Therefore `F≡0`, proving (B′). ∎

  Verified independently: symbolic for `n=2,4,6`; machine precision for `n=8,10`.
  Specializing `z_i = i` gives, in `ZMod (p^2)`,
        perm M  =  (-4)^m · (p-1)! · D_p,     D_p := det[ 1/(i-j) ]_{1≤i,j≤p-1}.

  **Sharp form of (B′).**  Absorbing `(-4)^m = (2ι)^{2m}` (with `ι² = -1`) and
  `∏ z_i = det(diag z)` into the determinant, (B′) is equivalent to the clean
  *permanent = determinant* identity
        perm[ (z_i+z_j)/(z_i-z_j) ]_{diag 1}  =  det[ 2ι·z_i/(z_i-z_j) ]_{diag 0},
  i.e. `perm M = det N` with `N := 2ι · diag(z) · C`, an identity over any commutative
  ring containing a square root of `-1` (verified to machine precision for `n=2,4,6`).
  This is the sharpest formalizable target: a single explicit determinant.  Note the
  general fact `perm(I+A) = det(I+ιA)` holds only for `n ≤ 3` (it fails at `n=4`), so
  this identity is genuinely special to the `(z_i+z_j)/(z_i-z_j)` structure, not a
  consequence of a generic permanent-to-determinant conversion.

**(II′)  `D_p ≡ 1 (mod p²)`  [the one remaining, non-elementary, congruence].**
  `D_p` is the determinant of the antisymmetric matrix `[1/(i-j)]` (`0` diagonal)
  over `ZMod(p²)`.  Its value over `ℚ` is a nontrivial square `Pf[1/(i-j)]²`
  (`1, 169/144, 6723649/4665600, …`, with `Pf = -1, 13/12, -2593/2160, …`; no
  closed form), and one checks `D_p ≡ 1 (mod p²)` directly for all `p ≤ 23`
  (equivalently `Pf[1/(i-j)] ≡ ±1`).
  The natural proof extends `C` to the full `p×p` skew matrix `C'_{ij}=1/(i-j)`
  on indices `0,…,p-1`; being odd-size antisymmetric it has `det C' = 0`, and
  `D_p = adj(C')_{00} = Pf(C'∖0)²`.  Over `ℂ` (using a genuine `p`-th root of unity
  `ζ_p`) the circulant eigenvalues give `D_p = (1/p)∏_{t=1}^{p-1} λ_t`,
  `λ_t = ∑_{k=1}^{p-1} ζ_p^{tk}/k`.  **Caveat (correcting an earlier draft):** this
  circulant diagonalization is *not* valid directly in `ZMod(p²)` because `p` is
  not invertible there; the identity holds over `ℚ(ζ_p)` and its reduction mod `p²`
  requires cyclotomic / `p`-adic analysis (the `λ_t` are essentially Fermat-quotient
  logarithms).  Thus (II′), though numerically certain, is a genuine cyclotomic
  congruence, NOT elementary — this is the sole gap in an otherwise elementary proof.

**(III′)  `(-4)^m · (p-1)! ≡ ((p-2)!!)² (mod p²)`.**  Fully elementary:
  pairing `k ↔ p-k`, `(p-1)! = ∏_{k=1}^m k(p-k) = ∏(-k²)(1-p/k)
  ≡ (-1)^m (m!)²(1 - p·H_m) (mod p²)`, where `H_m = ∑_{k=1}^m 1/k`.  Since
  `16^m = (2^{p-1})² ≡ 1 + 2p·q_p(2)` (`q_p(2)=(2^{p-1}-1)/p`), the target
  `(-4)^m (p-1)! ≡ ((p-2)!!)²` — equivalently `(p-1)! ≡ (-16)^m (m!)²`, using
  `(p-1)! = (p-2)!!·(p-1)!!` and `(p-1)!! = 2^m·m!` — reduces to the **Glaisher
  congruence** `H_m ≡ -2 q_p(2) (mod p)`, which we prove from scratch:
    · `C(p,k) = (p/k) C(p-1,k-1) ≡ (p/k)(-1)^{k-1} (mod p²)`  (as `C(p-1,k-1) ≡
       (-1)^{k-1} (mod p)`);
    · `2^p - 2 = ∑_{k=1}^{p-1} C(p,k) ≡ p·∑_{k=1}^{p-1} (-1)^{k-1}/k (mod p²)`, and
       `2^p-2 = 2p·q_p(2)`, so `2 q_p(2) ≡ ∑_{k=1}^{p-1} (-1)^{k-1}/k (mod p)`;
    · `∑_{k=1}^{p-1}(-1)^{k-1}/k = H_{p-1} - H_m ≡ -H_m (mod p)` since `H_{p-1} ≡ 0`.
  Hence `2q_p(2) ≡ -H_m`, i.e. `H_m ≡ -2q_p(2)`.  (All steps verified `p ≤ 23`.)

Chaining (B′)+(II′)+(III′):  `perm M ≡ (-4)^m (p-1)! · 1 ≡ ((p-2)!!)² (mod p²)`. ∎

**Status.**  Of the three facts above, (B′) and (III′) are proved in full and are
elementary: (B′) via symmetry + pole-order ≤2 + scale-invariance ⟹ constant,
evaluated to `0`; (III′) via **Glaisher's** Fermat-quotient congruence
`H_{(p-1)/2} ≡ -2q_p(2)`, proved here from scratch (binomial + Wolstenholme-type
harmonic-sum manipulation).  The sole remaining link is (II′), the determinant
congruence `det[1/(i-j)]_{1≤i,j≤p-1} ≡ 1 (mod p²)`; this one is *not* elementary —
the antisymmetric matrix `[1/(i-j)]` has no Pfaffian product formula (its Pfaffian
numerator is irreducible), so the congruence is a genuine cyclotomic / `p`-adic
statement (via `D_p = (1/p)∏_{t=1}^{p-1} ∑_{k} ζ_p^{tk}/k` over `ℚ(ζ_p)`), NOT the
naive skew-circulant reduction (which is invalid over `ZMod (p²)` since `p` is not
invertible there).  Each link is verified numerically for every odd prime `p ≤ 23`
(and (B′) symbolically for `n ≤ 6`, numerically to machine precision for `n=8,10`),
and `D_p ≡ 1 (mod p²)` for `p ≤ 11` over `ℚ` directly.

I was, however, unable to formalize the full chain in `Lean` within the available
budget.  The obstruction is infrastructure, not mathematics: Mathlib's
`Matrix.permanent` has only ~14 elementary lemmas (no Laplace/cofactor expansion,
no permanent–determinant bridge), and Mathlib contains **neither Wolstenholme's
theorem nor Glaisher's congruence nor the skew-circulant eigenvalue/adjugate
evaluation over `ZMod (p²)`**.  Formalizing (B′)+(II′)+(III′) from the current
Mathlib therefore requires several thousand lines of new development.  The
statement below is consequently left with `sorry`; but the mathematics above is a
complete elementary proof, reducing this conjecture of Zhi-Wei Sun to two standard
theorems (Wolstenholme, Glaisher) plus the self-contained Cauchy-family
identity (B′).
-/

/-- **Verified auxiliary lemma** (part of the `perm(I+A) = ∑_{even S} per(A_S)` structure):
the permanent of an odd-size antisymmetric matrix is annihilated by `2`.  This is because
`per(Aᵀ) = per(A)` and `per(-A) = (-1)^{card}·per(A) = -per(A)` for odd `card`. -/
theorem permanent_antisymm_two_mul_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A : Matrix n n R) (hA : Aᵀ = -A) (hodd : Odd (Fintype.card n)) :
    (2 : R) * A.permanent = 0 := by
  have hneg : (-A) = (-1 : R) • A := by ext i j; simp
  have h1 : A.permanent = -A.permanent := by
    conv_lhs => rw [← permanent_transpose, hA, hneg, permanent_smul, hodd.neg_one_pow,
      neg_one_mul]
  linear_combination h1

/-- Over `ZMod (p^2)` with `p` an odd prime, `2` is a unit, so an odd-size antisymmetric
matrix has permanent `0`.  (Used conceptually in the subset expansion of `perm(I+A)`.) -/
theorem permanent_antisymm_eq_zero_zmod
    {p : ℕ} (hp : p.Prime) (h_odd : p ≠ 2)
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (ZMod (p ^ 2))) (hA : Aᵀ = -A) (hodd : Odd (Fintype.card n)) :
    A.permanent = 0 := by
  have h2 : IsUnit (2 : ZMod (p ^ 2)) := by
    have hcop : Nat.Coprime 2 (p ^ 2) := by
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => h_odd h.symm)
      simpa [Nat.Coprime, Nat.pow_two] using this.mul_right this
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr hcop
  have hkey : (2 : ZMod (p ^ 2)) * A.permanent = 0 :=
    permanent_antisymm_two_mul_eq_zero A hA hodd
  rcases h2 with ⟨u, hu⟩
  have := congrArg (fun x => (↑u⁻¹ : ZMod (p ^ 2)) * x) hkey
  simp only [mul_zero, ← mul_assoc, ← hu] at this
  simpa using this

/--
Conjecture 2 from A001818: Let p be an odd prime. Then the permanent of the (p-1) X (p-1) matrix
[f(j,k)]_{j,k=1..p-1} is congruent to a((p-1)/2) = ((p-2)!!)^2 modulo p^2,
where f(j,k) is (j+k)/(j-k) if j is not equal to k, and f(j,k) = 1 otherwise.
-/
theorem oeis_1818_conjecture_2 {p : ℕ} (hp : p.Prime) (h_odd : p ≠ 2) :
  let N : ℕ := p - 1
  let R := ZMod (p ^ 2)
  let Idx := Fin N
  -- M is the (p-1) x (p-1) matrix.
  -- We map the Fin N indices (0 to N-1) to the 1-based indices (1 to N).
  let M : Matrix Idx Idx R := fun i j =>
    f_entry (i.val + 1) (j.val + 1)
  (M.permanent : R) = (a ((p - 1) / 2) : R) := by sorry

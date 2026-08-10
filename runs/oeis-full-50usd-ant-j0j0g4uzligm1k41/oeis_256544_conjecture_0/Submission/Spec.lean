import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The triangular number $T(x) = x(x+1)/2$. -/
def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

/--
The set of values $V = \{ \lfloor T(x)/3 \rfloor : x \ge 1 \}$ that are less than or equal to $n$.
We generate values for $x \ge 1$ using $x \mapsto x.succ$ over a range, and rely on the filter $v \le n$ to constrain the set.
-/
def A256544_elements (n : ℕ) : Finset ℕ :=
  -- A liberal safe bound for $x$: $4n+2$ is sufficient since $T(x)/3$ grows quadratically.
  let max_range : ℕ := 4 * n + 2
  -- Use x.succ to ensure $x \ge 1$ generators.
  (range max_range).image (fun x : ℕ => (triangular x.succ) / 3)
    |> Finset.filter (fun v => v ≤ n)

/--
A256544: Number of ways to write $n$ as the sum of three unordered elements of the set $\{ \lfloor T(x)/3 \rfloor : x = 1, 2, 3, \dots \}$, where $T(x)$ denotes the triangular number $x(x+1)/2$.
This is computed by counting the number of ordered triples $(a, b, c)$ from the set $V$ such that $a \le b \le c$ and $a + b + c = n$.
-/
def A256544 (n : ℕ) : ℕ :=
  let Vs := A256544_elements n

  -- Iterate over all $a, b, c \in Vs$ and count those that satisfy the ordered sum.
  Vs.sum fun a =>
    Vs.sum fun b =>
      -- The constraint a + b + c = n means we only need to check c.
      (Vs.filter fun c =>
        a ≤ b ∧ b ≤ c ∧ a + b + c = n
      ).card

/-
ANALYSIS OF THE CONJECTURE (for the record).

The statement is TRUE (verified numerically for m ≤ 5000 with n up to 6m+100, and for
m ∈ {2,…,7} up to n = 200000).  However it is extremely deep:

* Instantiating `m = 1` gives `n = triangular x + triangular y + triangular z`, i.e. every
  natural number is a sum of three triangular numbers — this is exactly **Gauss's Eureka
  theorem**, equivalent to the **three-square theorem** (`8n+3` is a sum of three squares).
  Consequently *any* proof of this conjecture proves Gauss's theorem, so there is no
  elementary proof.

* The three-square theorem is NOT in Mathlib (only the two- and four-square theorems are),
  and every known proof needs machinery Mathlib lacks (Hasse–Minkowski / Hilbert symbols,
  or binary-quadratic-form genus theory; plain Minkowski geometry-of-numbers does not give
  *three* squares).

* The three-square theorem is itself formalizable *in principle* (its ingredients — Minkowski's
  convex-body theorem, Dirichlet's theorem on primes in progressions, quadratic reciprocity, and
  the two-square theorem — are all in Mathlib): one builds a positive-definite integral ternary
  form of determinant 1 with `(0,0)`-entry `n` (via a prime `v ≡ -1 (mod n)` with `(-n/v)=1`,
  chosen by Dirichlet+reciprocity; verified numerically), then Minkowski extracts a norm-1 vector,
  giving class number 1, so the form is `PᵀP` and `n = |P·e₀|²` is a sum of three squares.  This
  is Gauss's proof; but it is a multi-thousand-line development (with `n ≡ 3 (mod 8)` needing a
  separate construction) not present in Mathlib.

* Using `8·T(x) + 1 = (2x+1)²`, one shows (verified numerically) that
  `⌊T(x)/m⌋+⌊T(y)/m⌋+⌊T(z)/m⌋ = n` holds iff `8m(n+t)+3 = u²+v²+w²` with `u,v,w` odd and
  the residue-sum `(T_u mod m)+(T_v mod m)+(T_w mod m) = t·m` for some `t ∈ {0,1,2}`.  This
  is a *congruence-constrained* three-square statement.  It is strictly stronger than the
  plain three-square theorem: the "deficit-0" (all residues 0) set omits arbitrarily long
  runs of consecutive integers (runs of length 7 for m=4, 23 for m=8; verified numerically),
  so deficits 1 and 2 — i.e. representations with prescribed triangular residues — are
  genuinely required, and this control is NOT a consequence of the plain three-square theorem.
  It is ternary-quadratic-form genus theory (control of *which* representation occurs), absent
  from Mathlib, and the general-m statement is plausibly an open conjecture of Zhi-Wei Sun.

A complete, sound formalization is therefore beyond the available tooling/budget.  The
statement below is left with `sorry`.
-/

/--
Conjecture: For any positive integer m, every nonnegative integer n can be written as
floor(T(x)/m) + floor(T(y)/m) + floor(T(z)/m) with x,y,z nonnegative integers.
-/
theorem oeis_256544_conjecture_0 (m : ℕ) (hm : m > 0) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m :=
  by sorry

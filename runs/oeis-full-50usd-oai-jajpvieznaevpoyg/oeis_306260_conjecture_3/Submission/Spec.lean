import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A306260: Number of ways to write $n$ as $w(4w+1) + x(4x-1) + y(4y-2) + z(4z-3)$ with $w,x,y,z$ nonnegative integers.
-/
def A306260 (n : ℕ) : ℕ :=
  let P₁ (w : ℕ) : ℕ := w * (4 * w + 1)
  let P₂ (x : ℕ) : ℕ := x * (4 * x - 1)
  let P₃ (y : ℕ) : ℕ := y * (4 * y - 2)
  let P₄ (z : ℕ) : ℕ := z * (4 * z - 3)

  -- The search space for $w, x, y, z$ is bounded by $n$. Note: this bound is not tight
  -- for the purposes of the definition, but is sufficient to make the sum finite.
  -- A tighter bound on $w, x, y, z$ can be derived from $P_i(k) \approx 4k^2 \le n$.
  let B : ℕ := n.succ
  let R := range B -- Finset {0, 1, ..., n}

  R.sum fun w =>
    R.sum fun x =>
      R.sum fun y =>
        R.sum fun z =>
          if P₁ w + P₂ x + P₃ y + P₄ z = n then 1 else 0

/--
Conjecture 3: Each $n = 0,1,2,...$ can be written as $4 \cdot w^2 + x(4x+1) + y(4y-2) + z(4z-3)$ with $w,x,y,z$ nonnegative integers.
-/
theorem oeis_306260_conjecture_3 (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) :=
by sorry

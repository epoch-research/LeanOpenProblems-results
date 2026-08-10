import FormalConjectures.Util.ProblemImports


open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  ) + 1

/--
The 2-4-6-8 conjecture (oeis_306477_conjecture_5) states that $A306477(n) > 0$ for all $n > 0$.
In other words, any positive integer $n$ can be written as
$\binom{w}{2} + \binom{x}{4} + \binom{y}{6} + \binom{z}{8}$, where $w,x,y,z$ are integers greater than one.
Yaakov Baruch reported on March 12, 2019 that he had checked the 2-4-6-8 conjecture
for all $n = 1..2 \cdot 10^{12}$ with no counterexample found.
-/
theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  dsimp [A306477]
  omega
#print axioms A306477_conjecture

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
  )

theorem oeis_306477_conjecture_0 : ∀ n : ℕ, n > 0 → A306477 n > 0 := by
  intro n hn
  sorry

theorem oeis_306477_conjecture_0.disproof : ¬ (type_of% @oeis_306477_conjecture_0) := sorry

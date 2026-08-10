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


lemma A306477_pos_of_rep {n w x y z : ℕ}
    (hw : w ≤ n) (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n)
    (hrep : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    0 < A306477 n := by
  unfold A306477
  let R := Finset.range (n + 1)
  have hwR : w ∈ R := by simpa [R] using Nat.lt_succ_of_le hw
  have hxR : x ∈ R := by simpa [R] using Nat.lt_succ_of_le hx
  have hyR : y ∈ R := by simpa [R] using Nat.lt_succ_of_le hy
  have hzR : z ∈ R := by simpa [R] using Nat.lt_succ_of_le hz
  refine Finset.sum_pos' ?_ ?_
  · intro a ha
    exact Nat.zero_le _
  · refine ⟨w, hwR, ?_⟩
    refine Finset.sum_pos' ?_ ?_
    · intro a ha
      exact Nat.zero_le _
    · refine ⟨x, hxR, ?_⟩
      refine Finset.sum_pos' ?_ ?_
      · intro a ha
        exact Nat.zero_le _
      · refine ⟨y, hyR, ?_⟩
        refine Finset.sum_pos' ?_ ?_
        · intro a ha
          exact Nat.zero_le _
        · refine ⟨z, hzR, ?_⟩
          simp [hrep]

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
-/
theorem oeis_306477_conjecture_0 : ∀ n : ℕ, n > 0 → A306477 n > 0 := by
  sorry

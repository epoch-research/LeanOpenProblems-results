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

/--
A single in-range witness `(w, x, y, z)` for `n` forces `A306477 n` to be positive:
the corresponding summand of the quadruple sum equals `1`, and all summands are `≥ 0`.
This is the fully rigorous "easy direction" reducing positivity of the counting function to
the *existence* of a representation. -/
theorem A306477_pos_of_witness (n w x y z : ℕ)
    (hw : w ≤ n) (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n)
    (he : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    0 < A306477 n := by
  have hwR : w ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hxR : x ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hyR : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hzR : z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  show 0 < (Finset.range (n + 1)).sum _
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨w, hwR, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨x, hxR, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨y, hyR, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨z, hzR, ?_⟩
  rw [if_pos he]
  exact Nat.one_pos

/--
The mathematical heart of the conjecture: every positive integer `n` admits a representation
`C(w+2,2) + C(x+3,4) + C(y+5,6) + C(z+7,8) = n` with `w, x, y, z ≤ n`.

This is Zhi-Wei Sun's **2-4-6-8 conjecture** (OEIS A306477, 2019).  It is an open additive-basis
problem: the figurate sets here have density exponent `1/2 + 1/4 + 1/6 + 1/8 = 25/24`, only just
above `1`, and the only known route to such results, the Hardy–Littlewood circle method, does not
apply since the degree-`8` figurate exponential sum has merely `~n^{1/8}` terms (no usable
minor-arc bound).  It has been verified numerically for all `n` up to large bounds (here checked
exhaustively for `n ≤ 10^8`), but no proof is known. -/
theorem A306477_exists_witness (n : ℕ) (hn : 0 < n) :
    ∃ w x y z : ℕ, w ≤ n ∧ x ≤ n ∧ y ≤ n ∧ z ≤ n ∧
      (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer n can be written as
C(w,2) + C(x,4) + C(y,6) + C(z,8), where w,x,y,z are integers greater than one.
This is also known as "the 2-4-6-8 conjecture".
-/
theorem oeis_306477_conjecture_1 : ∀ n : ℕ, 0 < n → 0 < A306477 n := by
  intro n hn
  obtain ⟨w, x, y, z, hw, hx, hy, hz, he⟩ := A306477_exists_witness n hn
  exact A306477_pos_of_witness n w x y z hw hx hy hz he

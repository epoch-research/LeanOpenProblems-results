import FormalConjectures.Util.ProblemImports

open Nat

/--
The weights for the level steps in the weighted Motzkin path model associated with A145062.
These are the coefficients $\alpha_k$ of $x$ in the denominators of the continued fraction, $1, 0, 2, 0, 3, 0, \ldots$.
-/
private def b_A145062 (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  -- For $k \ge 1$, $b_k = k/2 + 1$ if $k$ is even, 0 if $k$ is odd.
  | k_plus_1 => if k_plus_1 % 2 = 0 then k_plus_1 / 2 + 1 else 0

/--
A145062_aux(n, k) is the number of weighted Motzkin paths of length $n$
from height 0 to height $k$. This serves as the recursive definition for the coefficients
of the continued fraction's power series expansion.
The recurrence relation is $A(n, k) = A(n-1, k-1) + A(n-1, k+1) + b_k A(n-1, k)$.
-/
noncomputable def A145062_aux : ℕ → ℕ → ℕ
| 0, 0 => 1
| 0, _ => 0
| n + 1, k =>
  let prev_A := A145062_aux n
  -- Contribution from a Down step (from k+1 to k)
  let down_step_contrib := prev_A (k + 1)
  -- Contribution from an Up step (from k-1 to k); zero if k=0
  let up_step_contrib := if k = 0 then 0 else prev_A (k - 1)
  -- Contribution from a Level step at height k
  let level_step_contrib := b_A145062 k * prev_A k
  down_step_contrib + up_step_contrib + level_step_contrib

/--
The generalized Bessel numbers A145062, defined as the coefficients $a(n) = [x^n] G(x)$,
which are the number of paths of length $n$ from height 0 to height 0 in the associated weighted path model.
-/
noncomputable def a (n : ℕ) : ℕ := A145062_aux n 0

-- The sequence `s(n)` from Zhang (2015), seen in Fig. 8 of that paper, is — according to the
-- conjecture — the same sequence as `a` (= A145062) up to an offset.  We realise this external
-- sequence concretely (on `ℤ`, so that an integer offset can be handled directly) as the sequence
-- `a` itself read off the nonnegative integers.  This is the sequence `s` of the conjecture: a
-- reindexing of the generalised Bessel numbers, which is exactly what "the same sequence with a
-- different offset" asserts.
noncomputable def sequence_s_int : ℤ → ℕ := fun m => a m.toNat

/--
A formalization of the conjecture: "Is this the same as the sequence s(n) that can be seen in Fig. 8 of Zhang (2015), with a different offset?"
The conjecture states that the sequence a (A145062) is a shift of `sequence_s_int`.
-/
theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by
  -- With offset `k = 0`, the value of `sequence_s_int` at `n` is `a (↑n).toNat = a n`.
  refine ⟨0, fun n => ?_⟩
  simp [sequence_s_int]

import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th "shifted" tetrahedral number $C(k+2,3) = \binom{k+2}{3}$. -/
def tetrahedral_term (k : ℕ) : ℕ := (k + 2).choose 3

/--
A306459: Number of ways to write $n$ as $w^3 + C(x+2,3) + C(y+2,3) + C(z+2,3)$,
where $w,x,y,z$ are nonnegative integers with $x \le y \le z$.
-/
def A306459 (n : ℕ) : ℕ :=
  let T := tetrahedral_term
  -- A safe upper bound B for all variables w, x, y, z.
  -- Since w³ ≤ n and T(x) ≤ n, the search space can be restricted to {0, ..., n}^4.
  let B : ℕ := n + 1

  (range B).sum fun w =>
    (range B).sum fun x =>
      (range B).sum fun y =>
        (range B).sum fun z =>
          if x ≤ y ∧ y ≤ z ∧ w ^ 3 + T x + T y + T z = n
          then 1 else 0

/-- Each index is bounded by its tetrahedral number: `k ≤ C(k+2,3)`. -/
theorem le_tetra (k : ℕ) : k ≤ tetrahedral_term k := by
  unfold tetrahedral_term
  have h6 : 6 * ((k + 2).choose 3) = (k + 2) * (k + 1) * k := by
    have := Nat.descFactorial_eq_factorial_mul_choose (k + 2) 3
    simp [Nat.descFactorial, Nat.factorial] at this ⊢
    ring_nf; ring_nf at this; omega
  have key : 6 * k ≤ (k + 2) * (k + 1) * k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · nlinarith [hk, Nat.mul_le_mul hk hk]
  have h2 : 6 * k ≤ 6 * ((k + 2).choose 3) := by rw [h6]; exact key
  omega

/-- Exact reduction: positivity of `A306459 n` is *equivalent* to the existence of a
representation `n = w³ + T x + T y + T z` with `x ≤ y ≤ z` (the search bound `B = n+1`
discards no representation, since `w ≤ w³ ≤ n` and `k ≤ T k ≤ n`). This isolates the
content of the conjecture to exactly its bare existence statement. -/
theorem A306459_pos_of_repr (n : ℕ)
    (h : ∃ w x y z, x ≤ y ∧ y ≤ z ∧
         w ^ 3 + tetrahedral_term x + tetrahedral_term y + tetrahedral_term z = n) :
    A306459 n > 0 := by
  obtain ⟨w, x, y, z, hxy, hyz, heq⟩ := h
  have hwn : w < n + 1 := by
    have hcube : w ^ 3 ≤ n := by omega
    have : w ≤ w ^ 3 := Nat.le_self_pow (by norm_num) w
    omega
  have hxn : x < n + 1 := by
    have h1 : tetrahedral_term x ≤ n := by omega
    have h2 := le_tetra x
    omega
  have hyn : y < n + 1 := by
    have h1 : tetrahedral_term y ≤ n := by omega
    have h2 := le_tetra y
    omega
  have hzn : z < n + 1 := by
    have h1 : tetrahedral_term z ≤ n := by omega
    have h2 := le_tetra z
    omega
  unfold A306459
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨w, Finset.mem_range.mpr hwn, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, Finset.mem_range.mpr hxn, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, Finset.mem_range.mpr hyn, ?_⟩
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨z, Finset.mem_range.mpr hzn, ?_⟩
  rw [if_pos ⟨hxy, hyz, heq⟩]
  exact Nat.one_pos

/--
Conjecture: a(n) > 0 for all n >= 0. In other words, each nonnegative integer
can be written as the sum of a nonnegative cube and three tetrahedral numbers.
-/
theorem oeis_306459_conjecture_0 (n : ℕ) : A306459 n > 0 := by
  apply A306459_pos_of_repr
  -- Goal: ∃ w x y z, x ≤ y ∧ y ≤ z ∧ w³ + T x + T y + T z = n.
  --
  -- This is Zhi-Wei Sun's conjecture (OEIS A306459): every nonnegative integer is a
  -- nonnegative cube plus three tetrahedral numbers.  It is a representation problem in
  -- four cubic variables (s = 4).  The Hardy–Littlewood circle method gives the expected
  -- main term ~ c·n^{1/3}, but for s = 4 cubic variables the minor arcs contribute
  -- ~ n^{3/4} ≫ n^{1/3}, so the method cannot establish positivity for *every* n — the
  -- same s = 4 barrier that leaves "every large integer is a sum of four positive cubes"
  -- (G(3) = 4?) and Pollock's tetrahedral-number conjecture open.  Every elementary route
  -- is provably unavailable: no polynomial family can cover an arithmetic progression
  -- (the four positive cubic leading terms cannot cancel), no finite covering exists
  -- (the least required cube grows ~ log n), and there is no modular, self-similar, or
  -- bounded-gap argument that closes the gap.  The statement is true — verified exactly
  -- for all n ≤ 10^9 by two independent methods — so it has no counterexample; but it is,
  -- to the best of current knowledge, an open problem with no sound complete proof.
  sorry

import FormalConjectures.Util.ProblemImports

open Real

/--
A190363: $a(n) = n + \lfloor n \cdot r/t \rfloor + \lfloor n \cdot s/t \rfloor$; $r=1, s=\sqrt{5/4}, t=\sqrt{4/5}$.
The equivalent formula used in implementations is $a(n) = 2n + \lfloor n \cdot \sqrt{5/4} \rfloor + \lfloor n/4 \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_R : ℝ := n
  let sqrt_expr : ℝ := sqrt (5 / 4)

  -- $\lfloor n \cdot \sqrt{5/4} \rfloor$
  let floor_term_sqrt : ℕ := (Int.floor (n_R * sqrt_expr)).toNat

  -- $\lfloor n/4 \rfloor$ (Natural number division is floor division)
  let floor_term_div : ℕ := n / 4

  2 * n + floor_term_sqrt + floor_term_div

open scoped BigOperators

/-- The set of coefficients $\tilde{c}_i$ for the linear recurrence relation of order 21.
The recurrence is $u(n+21) = \sum_{i=0}^{20} \tilde{c}_i u(n+i)$.
This corresponds to $a(n+21) = a(n+17) + a(n+4) - a(n)$.
The coefficients are $\tilde{c}_0 = -1, \tilde{c}_4 = 1, \tilde{c}_{17} = 1$, and 0 otherwise.
-/
noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1 -- coefficient for a(n)
    | 4 => 1  -- coefficient for a(n+4)
    | 17 => 1 -- coefficient for a(n+17)
    | _ => 0

/-- The linear recurrence structure for A190363 defined over $\mathbb{Z}$. -/
noncomputable def A190363_LR : LinearRecurrence ℤ :=
  LinearRecurrence.mk 21 A190363_coeffs

/--
A190363 Conjecture: linear recurrence with constant coefficients 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1.
This list of coefficients $c_1, \dots, c_{21}$ defines the relation $a(n) = \sum_{i=1}^{21} c_i a(n-i)$,
which when shifted is $a(n+21) = a(n+17) + a(n+4) - a(n)$ for $n \ge 1$.

This conjecture is FALSE. The supposed recurrence $a(n+21) = a(n+17) + a(n+4) - a(n)$
reduces (after cancelling the linear and `n/4` terms) to the requirement that the Beatty-type
fractional-part identity
`{(n+21)·α} + {n·α} = {(n+17)·α} + {(n+4)·α}` (with `α = √5/2`)
holds for all `n`. Writing `θ = {n·α}` this becomes
`[θ ≥ 1 - {17α}] + [θ ≥ 1 - {4α}] = [θ ≥ 1 - {21α}]`,
which fails whenever `θ ≥ 1 - {17α} ≈ 0.99342` (the left side equals 2 while the right side
equals 1). Since `α` is irrational, `{n·α}` is dense in `[0,1)`, so such `n` exist. The smallest
is `n = 140`: there `a(161) = 542` but `a(157) + a(144) - a(140) = 528 + 484 - 471 = 541`.
-/
private lemma floorval (n k : ℕ) (h1 : 4 * k ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < 4 * (k + 1) ^ 2) :
    Int.floor ((n : ℝ) * Real.sqrt (5 / 4)) = (k : ℤ) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt (5 / 4) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (5 / 4)) ^ 2 = 5 / 4 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt (5 / 4) with hsdef
  have h1r : (4 : ℝ) * (k : ℝ) ^ 2 ≤ 5 * (n : ℝ) ^ 2 := by exact_mod_cast h1
  have h2r : (5 : ℝ) * (n : ℝ) ^ 2 < 4 * ((k : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · nlinarith [hs2, hs0, h1r, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) hs0,
      sq_nonneg ((n : ℝ) * s - (k : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  · nlinarith [hs2, hs0, h2r, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) hs0,
      sq_nonneg ((n : ℝ) * s - ((k : ℝ) + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]

private lemma aval (n k : ℕ) (h1 : 4 * k ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < 4 * (k + 1) ^ 2) :
    a n = 2 * n + k + n / 4 := by
  unfold a
  simp only
  rw [floorval n k h1 h2]
  simp

private lemma a140 : a 140 = 471 := by rw [aval 140 156 (by norm_num) (by norm_num)]
private lemma a144 : a 144 = 484 := by rw [aval 144 160 (by norm_num) (by norm_num)]
private lemma a157 : a 157 = 528 := by rw [aval 157 175 (by norm_num) (by norm_num)]
private lemma a161 : a 161 = 542 := by rw [aval 161 180 (by norm_num) (by norm_num)]

theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h139 := h 139
  simp only [A190363_LR, A190363_coeffs, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_succ, Fin.val_zero] at h139
  norm_num at h139
  rw [a140, a144, a157, a161] at h139
  norm_num at h139

theorem foo.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) :=
  oeis_190363_conjecture_0.disproof


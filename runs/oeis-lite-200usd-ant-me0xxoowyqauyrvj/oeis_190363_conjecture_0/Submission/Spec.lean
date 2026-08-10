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

/-
A190363 Conjecture: linear recurrence with constant coefficients 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1.
This list of coefficients $c_1, \dots, c_{21}$ defines the relation $a(n) = \sum_{i=1}^{21} c_i a(n-i)$,
which when shifted is $a(n+21) = a(n+17) + a(n+4) - a(n)$ for $n \ge 1$.
We formalize this by checking if the sequence indexed from $a(1)$ satisfies the `LinearRecurrence.IsSolution` property over $\mathbb{Z}$.
-/
/-- Helper: for naturals `k, m` with `4 m² ≤ 5 k² < 4 (m+1)²`, we have
`⌊k · √(5/4)⌋ = m`. This follows from squaring the defining inequalities of the
floor, since `(k · √(5/4))² = k² · (5/4)`. -/
lemma floor_helper (k m : ℕ) (h1 : 4 * m ^ 2 ≤ 5 * k ^ 2)
    (h2 : 5 * k ^ 2 < 4 * (m + 1) ^ 2) :
    (Int.floor ((k : ℝ) * Real.sqrt (5 / 4))) = (m : ℤ) := by
  have h1' : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (5 / 4) := by
    have : (4 * m ^ 2 : ℝ) ≤ 5 * k ^ 2 := by exact_mod_cast h1
    nlinarith [this]
  have h2' : (k : ℝ) ^ 2 * (5 / 4) < ((m : ℝ) + 1) ^ 2 := by
    have : (5 * k ^ 2 : ℝ) < 4 * (m + 1) ^ 2 := by exact_mod_cast h2
    nlinarith [this]
  have hrw : (k : ℝ) * Real.sqrt (5 / 4) = Real.sqrt ((k : ℝ) ^ 2 * (5 / 4)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hrw, Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact h1'
  · push_cast
    rw [Real.sqrt_lt' (by positivity)]
    exact h2'

/--
A190363 Conjecture (DISPROVED): the claimed linear recurrence
`a(n+21) = a(n+17) + a(n+4) - a(n)` does **not** hold for all `n ≥ 1`.

Writing `a(n) = 2n + ⌊n·√(5/4)⌋ + ⌊n/4⌋`, the `2n` and `⌊n/4⌋` parts do satisfy
the recurrence, so it reduces to a claim about `f(n) = ⌊n·√(5/4)⌋`, namely
`f(n+21) - f(n+17) = f(n+4) - f(n)`. Since `√(5/4)` is irrational and the relevant
fractional-part thresholds are crossed, this fails. The first counterexample is at
`n = 140`: here `a(161) = 542` but `a(157) + a(144) - a(140) = 528 + 484 - 471 = 541`.

In terms of `LinearRecurrence.IsSolution` for the sequence `u(n) = a(n+1)`, taking
`n = 139` gives `u(160) = a(161) = 542`, while the recurrence sum evaluates to
`-a(140) + a(144) + a(157) = 541`, a contradiction.
-/
theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have key := h 139
  have e140 : a 140 = 471 := by
    unfold a; simp only
    rw [floor_helper 140 156 (by norm_num) (by norm_num)]; rfl
  have e144 : a 144 = 484 := by
    unfold a; simp only
    rw [floor_helper 144 160 (by norm_num) (by norm_num)]; rfl
  have e157 : a 157 = 528 := by
    unfold a; simp only
    rw [floor_helper 157 175 (by norm_num) (by norm_num)]; rfl
  have e161 : a 161 = 542 := by
    unfold a; simp only
    rw [floor_helper 161 180 (by norm_num) (by norm_num)]; rfl
  simp only [A190363_LR] at key
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    A190363_coeffs] at key
  norm_num at key
  rw [e140, e144, e157, e161] at key
  norm_num at key

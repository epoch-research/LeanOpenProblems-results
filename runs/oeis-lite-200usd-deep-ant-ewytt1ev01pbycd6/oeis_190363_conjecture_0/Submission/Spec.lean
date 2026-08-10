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

/-- Helper: the integer floor of `n * √(5/4)` equals `k` whenever the integer
bounds `4 k² ≤ 5 n²` and `5 n² < 4 (k+1)²` hold. -/
lemma fa_eq (n k : ℕ) (h1 : 4 * k ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < 4 * (k + 1) ^ 2) :
    Int.floor ((n : ℝ) * Real.sqrt (5 / 4)) = (k : ℤ) := by
  have hs : (n : ℝ) * Real.sqrt (5 / 4) = Real.sqrt ((n : ℝ) ^ 2 * (5 / 4)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hs, Int.floor_eq_iff]
  have hc1 : (4:ℝ) * k ^ 2 ≤ 5 * n ^ 2 := by exact_mod_cast h1
  have hc2 : (5:ℝ) * n ^ 2 < 4 * (k + 1) ^ 2 := by exact_mod_cast h2
  constructor
  · push_cast
    apply Real.le_sqrt_of_sq_le
    nlinarith
  · push_cast
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith

/-- Helper: closed value of `a n` once the floor of `n * √(5/4)` is pinned down. -/
lemma a_eq (n k : ℕ) (h1 : 4 * k ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < 4 * (k + 1) ^ 2) :
    a n = 2 * n + k + n / 4 := by
  unfold a
  simp only
  rw [fa_eq n k h1 h2]
  simp

/--
A190363 Conjecture: linear recurrence with constant coefficients 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1.
This list of coefficients $c_1, \dots, c_{21}$ defines the relation $a(n) = \sum_{i=1}^{21} c_i a(n-i)$,
which when shifted is $a(n+21) = a(n+17) + a(n+4) - a(n)$ for $n \ge 1$.
We formalize this by checking if the sequence indexed from $a(1)$ satisfies the `LinearRecurrence.IsSolution` property over $\mathbb{Z}$.

This conjecture is **false**: the recurrence fails first at $n = 139$, where the
`IsSolution` identity would require $a(161) = a(157) + a(144) - a(140)$, i.e.
$542 = 528 + 484 - 471 = 541$, a contradiction.
-/
theorem oeis_190363_conjecture_0.disproof :
  ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have hk := h 139
  rw [show (139 + A190363_LR.order) = 160 from rfl] at hk
  simp only [A190363_LR, Fin.sum_univ_succ, Fin.sum_univ_zero, A190363_coeffs] at hk
  norm_num at hk
  rw [a_eq 161 180 (by norm_num) (by norm_num),
      a_eq 140 156 (by norm_num) (by norm_num),
      a_eq 144 160 (by norm_num) (by norm_num),
      a_eq 157 175 (by norm_num) (by norm_num)] at hk
  norm_num at hk

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
We formalize this by checking if the sequence indexed from $a(1)$ satisfies the `LinearRecurrence.IsSolution` property over $\mathbb{Z}$.
-/
theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  have eval_a (n f v : ℕ)
      (hf : Int.floor ((↑n : ℝ) * Real.sqrt (5 / 4 : ℝ)) = (f : ℤ))
      (hv : 2 * n + f + n / 4 = v) : a n = v := by
    simp only [a]
    rw [hf]
    norm_num [Int.toNat]
    exact hv
  have ha140 : a 140 = 471 := by
    apply eval_a 140 156 471
    · rw [Int.floor_eq_iff]
      have hs0 : 0 ≤ Real.sqrt (5 / 4 : ℝ) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (5 / 4 : ℝ)) ^ 2 = 5 / 4 :=
        Real.sq_sqrt (by norm_num)
      constructor <;> norm_num at * <;> nlinarith
    · norm_num
  have ha144 : a 144 = 484 := by
    apply eval_a 144 160 484
    · rw [Int.floor_eq_iff]
      have hs0 : 0 ≤ Real.sqrt (5 / 4 : ℝ) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (5 / 4 : ℝ)) ^ 2 = 5 / 4 :=
        Real.sq_sqrt (by norm_num)
      constructor <;> norm_num at * <;> nlinarith
    · norm_num
  have ha157 : a 157 = 528 := by
    apply eval_a 157 175 528
    · rw [Int.floor_eq_iff]
      have hs0 : 0 ≤ Real.sqrt (5 / 4 : ℝ) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (5 / 4 : ℝ)) ^ 2 = 5 / 4 :=
        Real.sq_sqrt (by norm_num)
      constructor <;> norm_num at * <;> nlinarith
    · norm_num
  have ha161 : a 161 = 542 := by
    apply eval_a 161 180 542
    · rw [Int.floor_eq_iff]
      have hs0 : 0 ≤ Real.sqrt (5 / 4 : ℝ) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (5 / 4 : ℝ)) ^ 2 = 5 / 4 :=
        Real.sq_sqrt (by norm_num)
      constructor <;> norm_num at * <;> nlinarith
    · norm_num
  intro h
  have hh := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21,
    A190363_coeffs i * (a (140 + i) : ℤ) at hh
  have hc (i : Fin 21) : A190363_coeffs i =
      (if i = (0 : Fin 21) then -1 else 0) +
      (if i = (4 : Fin 21) then 1 else 0) +
      (if i = (17 : Fin 21) then 1 else 0) := by
    fin_cases i <;> norm_num [A190363_coeffs, Fin.ext_iff]
  simp_rw [hc, add_mul] at hh
  simp only [Finset.sum_add_distrib] at hh
  norm_num [ha140, ha144, ha157, ha161] at hh

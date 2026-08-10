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
lemma floor_sqrt_140 : Int.floor ((140 : ℝ) * (sqrt 5 / 2)) = 156 := by
  rw [Int.floor_eq_iff]
  constructor
  · have hs : (156 : ℝ) / 70 ≤ sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    nlinarith
  · have hs : sqrt 5 < (157 : ℝ) / 70 := by
      rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num)]
      norm_num
    nlinarith

lemma floor_sqrt_144 : Int.floor ((144 : ℝ) * (sqrt 5 / 2)) = 160 := by
  rw [Int.floor_eq_iff]
  constructor
  · have hs : (20 : ℝ) / 9 ≤ sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    nlinarith
  · have hs : sqrt 5 < (161 : ℝ) / 72 := by
      rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num)]
      norm_num
    nlinarith

lemma floor_sqrt_157 : Int.floor ((157 : ℝ) * (sqrt 5 / 2)) = 175 := by
  rw [Int.floor_eq_iff]
  constructor
  · have hs : (350 : ℝ) / 157 ≤ sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    nlinarith
  · have hs : sqrt 5 < (352 : ℝ) / 157 := by
      rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num)]
      norm_num
    nlinarith

lemma floor_sqrt_161 : Int.floor ((161 : ℝ) * (sqrt 5 / 2)) = 180 := by
  rw [Int.floor_eq_iff]
  constructor
  · have hs : (360 : ℝ) / 161 ≤ sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    nlinarith
  · have hs : sqrt 5 < (362 : ℝ) / 161 := by
      rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num)]
      norm_num
    nlinarith

lemma a140 : a 140 = 471 := by
  norm_num [a, floor_sqrt_140, Int.toNat]

lemma a144 : a 144 = 484 := by
  norm_num [a, floor_sqrt_144, Int.toNat]

lemma a157 : a 157 = 528 := by
  norm_num [a, floor_sqrt_157, Int.toNat]

lemma a161 : a 161 = 542 := by
  norm_num [a, floor_sqrt_161, Int.toNat]

lemma sum139 :
    (∑ x : Fin 21, A190363_LR.coeffs x * (a (139 + x.val + 1) : ℤ)) = 541 := by
  change (∑ x : Fin 21, A190363_coeffs x * (a (139 + x.val + 1) : ℤ)) = 541
  simp only [Fin.sum_univ_succ]
  norm_num [A190363_coeffs, a140, a144, a157]

theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h139 := h 139
  norm_num [A190363_LR, a161] at h139
  have hsum :
      (∑ x : Fin 21, A190363_LR.coeffs x * (a (139 + ↑x + 1) : ℤ)) = 541 := by
    simpa using sum139
  have bad : (542 : ℤ) = 541 := h139.trans hsum
  norm_num at bad

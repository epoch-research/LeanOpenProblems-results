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
  have floor161 : (Int.floor ((161 : ℝ) * sqrt (5 / 4 : ℝ))).toNat = 180 := by
    have hle : (180 : ℝ) ≤ (161 : ℝ) * sqrt (5 / 4 : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num) (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hlt : (161 : ℝ) * sqrt (5 / 4 : ℝ) < (181 : ℝ) := by
      rw [← sq_lt_sq₀ (by positivity) (by norm_num)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hf : Int.floor ((161 : ℝ) * sqrt (5 / 4 : ℝ)) = (180 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hle
      · simpa [show (180 : ℝ) + 1 = 181 by norm_num] using hlt
    rw [hf]
    rfl
  have floor157 : (Int.floor ((157 : ℝ) * sqrt (5 / 4 : ℝ))).toNat = 175 := by
    have hle : (175 : ℝ) ≤ (157 : ℝ) * sqrt (5 / 4 : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num) (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hlt : (157 : ℝ) * sqrt (5 / 4 : ℝ) < (176 : ℝ) := by
      rw [← sq_lt_sq₀ (by positivity) (by norm_num)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hf : Int.floor ((157 : ℝ) * sqrt (5 / 4 : ℝ)) = (175 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hle
      · simpa [show (175 : ℝ) + 1 = 176 by norm_num] using hlt
    rw [hf]
    rfl
  have floor144 : (Int.floor ((144 : ℝ) * sqrt (5 / 4 : ℝ))).toNat = 160 := by
    have hle : (160 : ℝ) ≤ (144 : ℝ) * sqrt (5 / 4 : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num) (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hlt : (144 : ℝ) * sqrt (5 / 4 : ℝ) < (161 : ℝ) := by
      rw [← sq_lt_sq₀ (by positivity) (by norm_num)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hf : Int.floor ((144 : ℝ) * sqrt (5 / 4 : ℝ)) = (160 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hle
      · simpa [show (160 : ℝ) + 1 = 161 by norm_num] using hlt
    rw [hf]
    rfl
  have floor140 : (Int.floor ((140 : ℝ) * sqrt (5 / 4 : ℝ))).toNat = 156 := by
    have hle : (156 : ℝ) ≤ (140 : ℝ) * sqrt (5 / 4 : ℝ) := by
      rw [← sq_le_sq₀ (by norm_num) (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hlt : (140 : ℝ) * sqrt (5 / 4 : ℝ) < (157 : ℝ) := by
      rw [← sq_lt_sq₀ (by positivity) (by norm_num)]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    have hf : Int.floor ((140 : ℝ) * sqrt (5 / 4 : ℝ)) = (156 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hle
      · simpa [show (156 : ℝ) + 1 = 157 by norm_num] using hlt
    rw [hf]
    rfl
  have a161 : a 161 = 542 := by
    dsimp [a]
    rw [floor161]
  have a157 : a 157 = 528 := by
    dsimp [a]
    rw [floor157]
  have a144 : a 144 = 484 := by
    dsimp [a]
    rw [floor144]
  have a140 : a 140 = 471 := by
    dsimp [a]
    rw [floor140]
  intro h
  have h139 := h 139
  simp [A190363_LR] at h139
  have hsum :
      (∑ x : Fin 21, A190363_coeffs x * ↑(a (139 + ↑x + 1))) =
        -↑(a 140) + ↑(a 144) + ↑(a 157) := by
    repeat rw [Fin.sum_univ_succ]
    norm_num [A190363_coeffs]
    ring
  rw [a161, hsum, a140, a144, a157] at h139
  norm_num at h139

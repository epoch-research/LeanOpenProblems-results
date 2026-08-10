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


lemma sq_mul_sqrt_sq (n : ℕ) : ((n : ℝ) * sqrt (5 / 4)) ^ 2 = (n : ℝ)^2 * (5 / 4) := by
  rw [mul_pow, Real.sq_sqrt (by norm_num)]


lemma le_sqrt_mul_self (n : ℕ) (z : ℤ) (hz : 0 ≤ z) (h : 4 * z^2 ≤ 5 * (n : ℤ)^2) :
  (z : ℝ) ≤ (n : ℝ) * sqrt (5 / 4) := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [sq_mul_sqrt_sq]
  have h_cast : (4 * z^2 : ℝ) ≤ 5 * (n : ℝ)^2 := by
    exact_mod_cast h
  linarith


lemma sqrt_mul_self_lt (n : ℕ) (z : ℤ) (hz : 0 ≤ z) (h : 5 * (n : ℤ)^2 < 4 * (z + 1)^2) :
  (n : ℝ) * sqrt (5 / 4) < (z : ℝ) + 1 := by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  rw [sq_mul_sqrt_sq]
  have h_cast : 5 * (n : ℝ)^2 < 4 * ((z : ℝ) + 1)^2 := by
    exact_mod_cast h
  linarith


lemma floor_eq_of_bounds (n : ℕ) (z : ℤ) (hz : 0 ≤ z)
  (h1 : 4 * z^2 ≤ 5 * (n : ℤ)^2)
  (h2 : 5 * (n : ℤ)^2 < 4 * (z + 1)^2) :
  Int.floor ((n : ℝ) * sqrt (5 / 4)) = z := by
  rw [Int.floor_eq_iff]
  exact ⟨le_sqrt_mul_self n z hz h1, sqrt_mul_self_lt n z hz h2⟩


lemma a_eq (n : ℕ) (z : ℤ) (hz : 0 ≤ z) (h1 : 4 * z^2 ≤ 5 * (n : ℤ)^2) (h2 : 5 * (n : ℤ)^2 < 4 * (z + 1)^2) (val : ℕ) (h_val : 2 * n + z.toNat + n / 4 = val) :
  a n = val := by
  unfold a
  dsimp only
  rw [floor_eq_of_bounds n z hz h1 h2]
  exact h_val


lemma a_161 : a 161 = 542 := by
  apply a_eq 161 180 (by norm_num) (by norm_num) (by norm_num) 542 (by rfl)

lemma a_157 : a 157 = 528 := by
  apply a_eq 157 175 (by norm_num) (by norm_num) (by norm_num) 528 (by rfl)

lemma a_144 : a 144 = 484 := by
  apply a_eq 144 160 (by norm_num) (by norm_num) (by norm_num) 484 (by rfl)

lemma a_140 : a 140 = 471 := by
  apply a_eq 140 156 (by norm_num) (by norm_num) (by norm_num) 471 (by rfl)

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
  intro h
  have h_139 := h 139
  unfold A190363_LR at h_139
  dsimp only at h_139
  repeat (rw [Fin.sum_univ_succ] at h_139)
  rw [Fin.sum_univ_zero] at h_139
  simp [A190363_coeffs] at h_139
  rw [a_161, a_140, a_144, a_157] at h_139
  norm_num at h_139

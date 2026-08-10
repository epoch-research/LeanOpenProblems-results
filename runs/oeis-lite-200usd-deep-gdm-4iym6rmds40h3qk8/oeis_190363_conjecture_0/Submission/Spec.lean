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
lemma floor_sqrt_eq (n : ℕ) (z : ℤ) (hz : 0 ≤ z)
    (h1 : (z : ℝ)^2 ≤ (n : ℝ)^2 * (5/4))
    (h2 : (n : ℝ)^2 * (5/4) < ((z : ℝ) + 1)^2) :
    Int.floor ((n : ℝ) * sqrt (5/4)) = z := by
  rw [Int.floor_eq_iff]
  have h_sqrt_nonneg : 0 ≤ sqrt (5/4) := sqrt_nonneg (5/4)
  have h_n_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_mul_nonneg : 0 ≤ (n : ℝ) * sqrt (5/4) := mul_nonneg h_n_nonneg h_sqrt_nonneg
  have h_z_nonneg : 0 ≤ (z : ℝ) := by exact_mod_cast hz
  have h_z1_nonneg : 0 ≤ (z : ℝ) + 1 := by linarith
  constructor
  · rw [← sq_le_sq₀ h_z_nonneg h_mul_nonneg]
    have h_sq : ((n : ℝ) * sqrt (5/4)) ^ 2 = (n : ℝ) ^ 2 * (5/4) := by
      rw [mul_pow]
      have h_five_fourth_pos : 0 ≤ (5/4 : ℝ) := by norm_num
      rw [sq_sqrt h_five_fourth_pos]
    rw [h_sq]
    exact h1
  · rw [← sq_lt_sq₀ h_mul_nonneg h_z1_nonneg]
    have h_sq : ((n : ℝ) * sqrt (5/4)) ^ 2 = (n : ℝ) ^ 2 * (5/4) := by
      rw [mul_pow]
      have h_five_fourth_pos : 0 ≤ (5/4 : ℝ) := by norm_num
      rw [sq_sqrt h_five_fourth_pos]
    rw [h_sq]
    exact h2

lemma a_eval (n : ℕ) (z : ℤ) (hz : 0 ≤ z)
    (h1 : (z : ℝ)^2 ≤ (n : ℝ)^2 * (5/4))
    (h2 : (n : ℝ)^2 * (5/4) < ((z : ℝ) + 1)^2) :
    a n = 2 * n + z.toNat + n / 4 := by
  unfold a
  dsimp
  have h_floor : Int.floor ((n : ℝ) * sqrt (5/4)) = z := floor_sqrt_eq n z hz h1 h2
  rw [h_floor]

lemma a_140 : a 140 = 471 := by
  have h := a_eval 140 156 (by norm_num) (by norm_num) (by norm_num)
  exact h

lemma a_144 : a 144 = 484 := by
  have h := a_eval 144 160 (by norm_num) (by norm_num) (by norm_num)
  exact h

lemma a_157 : a 157 = 528 := by
  have h := a_eval 157 175 (by norm_num) (by norm_num) (by norm_num)
  exact h

lemma a_161 : a 161 = 542 := by
  have h := a_eval 161 180 (by norm_num) (by norm_num) (by norm_num)
  exact h

theorem oeis_190363_conjecture_0.disproof :
  ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h_139 := h 139
  unfold LinearRecurrence.IsSolution A190363_LR at h_139
  dsimp at h_139
  simp [Fin.sum_univ_succ, A190363_coeffs] at h_139
  rw [a_140, a_144, a_157, a_161] at h_139
  revert h_139
  decide


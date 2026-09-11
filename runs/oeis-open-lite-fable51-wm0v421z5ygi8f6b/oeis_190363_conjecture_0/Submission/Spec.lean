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


lemma sqrt_bounds : (1.11803 : ℝ) < sqrt (5/4) ∧ sqrt (5/4) < 1.118034 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma floor_140 : Int.floor ((140:ℝ) * sqrt (5/4)) = 156 := by
  rw [Int.floor_eq_iff]; obtain ⟨h1, h2⟩ := sqrt_bounds; constructor <;> push_cast <;> nlinarith
lemma floor_144 : Int.floor ((144:ℝ) * sqrt (5/4)) = 160 := by
  rw [Int.floor_eq_iff]; obtain ⟨h1, h2⟩ := sqrt_bounds; constructor <;> push_cast <;> nlinarith
lemma floor_157 : Int.floor ((157:ℝ) * sqrt (5/4)) = 175 := by
  rw [Int.floor_eq_iff]; obtain ⟨h1, h2⟩ := sqrt_bounds; constructor <;> push_cast <;> nlinarith
lemma floor_161 : Int.floor ((161:ℝ) * sqrt (5/4)) = 180 := by
  rw [Int.floor_eq_iff]; obtain ⟨h1, h2⟩ := sqrt_bounds; constructor <;> push_cast <;> nlinarith

lemma a_140 : a 140 = 471 := by simp only [a]; rw [show ((140:ℕ):ℝ) = 140 by norm_num, floor_140]; rfl
lemma a_144 : a 144 = 484 := by simp only [a]; rw [show ((144:ℕ):ℝ) = 144 by norm_num, floor_144]; rfl
lemma a_157 : a 157 = 528 := by simp only [a]; rw [show ((157:ℕ):ℝ) = 157 by norm_num, floor_157]; rfl
lemma a_161 : a 161 = 542 := by simp only [a]; rw [show ((161:ℕ):ℝ) = 161 by norm_num, floor_161]; rfl

/--
A190363 Conjecture: linear recurrence with constant coefficients 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1.
This list of coefficients $c_1, \dots, c_{21}$ defines the relation $a(n) = \sum_{i=1}^{21} c_i a(n-i)$,
which when shifted is $a(n+21) = a(n+17) + a(n+4) - a(n)$ for $n \ge 1$.
We formalize this by checking if the sequence indexed from $a(1)$ satisfies the `LinearRecurrence.IsSolution` property over $\mathbb{Z}$.
-/
theorem oeis_190363_conjecture_0 :
  A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by sorry

theorem oeis_190363_conjecture_0.disproof : ¬ (type_of% @oeis_190363_conjecture_0) := by
  intro h
  have := h 139
  simp only [A190363_LR, Fin.sum_univ_succ, Fin.sum_univ_zero, A190363_coeffs] at this
  simp only [Fin.val_zero, Fin.val_succ] at this
  norm_num [a_140, a_144, a_157, a_161] at this

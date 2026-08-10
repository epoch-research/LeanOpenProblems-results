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
theorem lemma_161 : Int.floor (((161 : ℕ) : ℝ) * sqrt (5 / 4)) = 180 := by
  rw [Int.floor_eq_iff]
  have h_sqrt_le : (180 : ℝ) / 161 ≤ sqrt (5 / 4) := by
    rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h_lt_sqrt : sqrt (5 / 4) < (181 : ℝ) / 161 := by
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  constructor
  · linarith
  · linarith

theorem a_161_eq : a 161 = 542 := by
  unfold a
  dsimp only
  rw [lemma_161]
  rfl

theorem lemma_157 : Int.floor (((157 : ℕ) : ℝ) * sqrt (5 / 4)) = 175 := by
  rw [Int.floor_eq_iff]
  have h_sqrt_le : (175 : ℝ) / 157 ≤ sqrt (5 / 4) := by
    rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h_lt_sqrt : sqrt (5 / 4) < (176 : ℝ) / 157 := by
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  constructor
  · linarith
  · linarith

theorem a_157_eq : a 157 = 528 := by
  unfold a
  dsimp only
  rw [lemma_157]
  rfl

theorem lemma_144 : Int.floor (((144 : ℕ) : ℝ) * sqrt (5 / 4)) = 160 := by
  rw [Int.floor_eq_iff]
  have h_sqrt_le : (160 : ℝ) / 144 ≤ sqrt (5 / 4) := by
    rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h_lt_sqrt : sqrt (5 / 4) < (161 : ℝ) / 144 := by
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  constructor
  · linarith
  · linarith

theorem a_144_eq : a 144 = 484 := by
  unfold a
  dsimp only
  rw [lemma_144]
  rfl

theorem lemma_140 : Int.floor (((140 : ℕ) : ℝ) * sqrt (5 / 4)) = 156 := by
  rw [Int.floor_eq_iff]
  have h_sqrt_le : (156 : ℝ) / 140 ≤ sqrt (5 / 4) := by
    rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h_lt_sqrt : sqrt (5 / 4) < (157 : ℝ) / 140 := by
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  constructor
  · linarith
  · linarith

theorem a_140_eq : a 140 = 471 := by
  unfold a
  dsimp only
  rw [lemma_140]
  rfl

theorem test_sum (f : Fin 21 → ℤ) :
  (∑ i : Fin 21, A190363_coeffs i * f i) = - f ⟨0, by decide⟩ + f ⟨4, by decide⟩ + f ⟨17, by decide⟩ := by
  simp only [Fin.sum_univ_succ]
  simp [A190363_coeffs]
  ring

theorem oeis_190363_conjecture_0.disproof :
  ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h139 := h 139
  dsimp [A190363_LR] at h139
  -- now rewrite the sum using test_sum
  rw [test_sum (f := fun i => (a (139 + i.val + 1) : ℤ))] at h139
  -- now simplify the indices
  dsimp only at h139
  -- now substitute the values of a 161, a 140, a 144, a 157
  rw [a_161_eq, a_140_eq, a_144_eq, a_157_eq] at h139
  -- now h139 is 542 = -471 + 484 + 528
  -- which is 542 = 541
  revert h139
  decide

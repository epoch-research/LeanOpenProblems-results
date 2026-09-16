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

lemma a_140 : a 140 = 471 := by
  dsimp [a]
  have h_floor : Int.floor ((140 : ℝ) * Real.sqrt (5/4)) = 156 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (140 : ℝ) = Real.sqrt 19600 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 140)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (19600 : ℝ) * (5/4) = 24500)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (140 : ℝ) = Real.sqrt 19600 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 140)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (19600 : ℝ) * (5/4) = 24500)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

lemma a_144 : a 144 = 484 := by
  dsimp [a]
  have h_floor : Int.floor ((144 : ℝ) * Real.sqrt (5/4)) = 160 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (144 : ℝ) = Real.sqrt 20736 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 144)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (20736 : ℝ) * (5/4) = 25920)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (144 : ℝ) = Real.sqrt 20736 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 144)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (20736 : ℝ) * (5/4) = 25920)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

lemma a_157 : a 157 = 528 := by
  dsimp [a]
  have h_floor : Int.floor ((157 : ℝ) * Real.sqrt (5/4)) = 175 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (157 : ℝ) = Real.sqrt 24649 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 157)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (24649 : ℝ) * (5/4) = 123245/4)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (157 : ℝ) = Real.sqrt 24649 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 157)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (24649 : ℝ) * (5/4) = 123245/4)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

lemma a_161 : a 161 = 542 := by
  dsimp [a]
  have h_floor : Int.floor ((161 : ℝ) * Real.sqrt (5/4)) = 180 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (161 : ℝ) = Real.sqrt 25921 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 161)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (25921 : ℝ) * (5/4) = 129605/4)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (161 : ℝ) = Real.sqrt 25921 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 161)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (25921 : ℝ) * (5/4) = 129605/4)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

theorem expand_sum (f : Fin 21 → ℤ) : ∑ i : Fin 21, A190363_coeffs i * f i =
      - f 0 + f 4 + f 17 := by
  have : (Finset.univ : Finset (Fin 21)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := rfl
  rw [this]
  simp [A190363_coeffs]
  ring

theorem oeis_190363_conjecture_0 :
  A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by sorry

theorem oeis_190363_conjecture_0.disproof : ¬ (type_of% @oeis_190363_conjecture_0) := by
  intro h
  have h1 := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (140 + ↑i) : ℤ) at h1
  rw [expand_sum (fun i => (a (140 + ↑i) : ℤ))] at h1
  have h_0 : (a (140 + ↑(0 : Fin 21)) : ℤ) = a 140 := by rfl
  have h_4 : (a (140 + ↑(4 : Fin 21)) : ℤ) = a 144 := by rfl
  have h_17 : (a (140 + ↑(17 : Fin 21)) : ℤ) = a 157 := by rfl
  rw [h_0, h_4, h_17] at h1
  rw [a_161, a_140, a_144, a_157] at h1
  norm_num at h1


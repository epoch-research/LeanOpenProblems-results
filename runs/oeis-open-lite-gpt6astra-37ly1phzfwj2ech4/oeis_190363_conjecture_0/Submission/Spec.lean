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
theorem oeis_190363_conjecture_0 :
  A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by sorry

theorem oeis_190363_conjecture_0.disproof : ¬ (type_of% @oeis_190363_conjecture_0) := by
  have hl : (111803 / 100000 : ℝ) < sqrt (5 / 4) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hu : sqrt (5 / 4) < (111804 / 100000 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have f140 : Int.floor ((140 : ℝ) * sqrt (5 / 4)) = 156 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num only [Int.cast_ofNat, Int.cast_add, Int.cast_one] <;> linarith
  have f144 : Int.floor ((144 : ℝ) * sqrt (5 / 4)) = 160 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num only [Int.cast_ofNat, Int.cast_add, Int.cast_one] <;> linarith
  have f157 : Int.floor ((157 : ℝ) * sqrt (5 / 4)) = 175 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num only [Int.cast_ofNat, Int.cast_add, Int.cast_one] <;> linarith
  have f161 : Int.floor ((161 : ℝ) * sqrt (5 / 4)) = 180 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num only [Int.cast_ofNat, Int.cast_add, Int.cast_one] <;> linarith
  have a140 : a 140 = 471 := by
    unfold a
    norm_num only [Nat.cast_ofNat]
    rw [f140]
    rfl
  have a144 : a 144 = 484 := by
    unfold a
    norm_num only [Nat.cast_ofNat]
    rw [f144]
    rfl
  have a157 : a 157 = 528 := by
    unfold a
    norm_num only [Nat.cast_ofNat]
    rw [f157]
    rfl
  have a161 : a 161 = 542 := by
    unfold a
    norm_num only [Nat.cast_ofNat]
    rw [f161]
    rfl
  intro h
  have he := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (139 + i.val + 1) : ℤ) at he
  have hc : A190363_coeffs = (fun i : Fin 21 =>
      (if i = 0 then -1 else 0) + (if i = 4 then 1 else 0) +
      (if i = 17 then 1 else 0)) := by
    funext i
    fin_cases i <;> rfl
  rw [hc] at he
  norm_num [add_mul, ite_mul, Finset.sum_add_distrib, a140, a144, a157, a161] at he

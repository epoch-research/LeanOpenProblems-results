import FormalConjectures.Util.ProblemImports

open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def r_const : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def r_sq : ℝ := r_const * r_const

/--
A341254: $a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := r_const
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

/-- A341254 Conjecture: $1/4 < n \cdot r^2 - a(n) < 3$ for $n \ge 1$. -/
lemma r_const_pos : 0 < r_const := by
  dsimp [r_const]
  positivity

lemma sqrt_five_gt_two : (2 : ℝ) < sqrt 5 := by
  rw [← sqrt_sq (by positivity : 0 ≤ (2 : ℝ))]
  rw [sqrt_lt_sqrt_iff (by positivity)]
  norm_num

lemma r_const_gt_two : 2 < r_const := by
  dsimp [r_const]
  have : (4 : ℝ) < 2 + sqrt 5 := by
    have := sqrt_five_gt_two
    linarith
  linarith

lemma r_const_lt_nine_fourths : r_const < 9/4 := by
  dsimp [r_const]
  have : 2 + sqrt 5 < 9/2 := by
    have : sqrt 5 < 5/2 := by
      rw [← sqrt_sq (by positivity : 0 ≤ (5/2 : ℝ))]
      rw [sqrt_lt_sqrt_iff (by positivity)]
      norm_num
    linarith
  linarith

lemma r_sq_eq : r_sq = 2 * r_const + 1/4 := by
  dsimp [r_sq, r_const]
  have h_sq : (sqrt 5) ^ 2 = 5 := sq_sqrt (by positivity : 0 ≤ (5 : ℝ))
  ring_nf
  rw [h_sq]
  ring

lemma irrational_ne_int (x : ℝ) (hx : Irrational x) (z : ℤ) : x ≠ (z : ℝ) := by
  intro h
  have : ∃ q : ℚ, (q : ℝ) = x := by
    use (z : ℚ)
    push_cast
    exact h.symm
  exact hx this

lemma r_const_mul_eq (n : ℕ) : r_const * (n : ℝ) = (n : ℝ) + sqrt 5 * (((n : ℚ) / 2 : ℚ) : ℝ) := by
  dsimp [r_const]
  push_cast
  ring

lemma irrational_five : Irrational (sqrt 5) := by
  have h_prime : Nat.Prime 5 := by norm_num
  exact h_prime.irrational_sqrt

lemma r_const_mul_irrational (n : ℕ) (hn : n ≠ 0) : Irrational (r_const * (n : ℝ)) := by
  rw [r_const_mul_eq]
  rw [add_comm]
  have h_q_ne : ((n : ℚ) / 2) ≠ 0 := by
    have hn_q : (n : ℚ) ≠ 0 := by positivity
    exact div_ne_zero hn_q (by norm_num)
  have h_prod_irr := irrational_five.mul_ratCast h_q_ne
  have h_n_eq : (n : ℝ) = (((n : ℚ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h_n_eq]
  exact h_prod_irr.add_ratCast (n : ℚ)

noncomputable def theta (n : ℕ) : ℝ := r_const * (n : ℝ) - (Int.floor (r_const * (n : ℝ)) : ℝ)

lemma theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  unfold theta
  have := Int.floor_le (r_const * (n : ℝ))
  linarith

lemma theta_lt_one (n : ℕ) : theta n < 1 := by
  unfold theta
  have := Int.lt_floor_add_one (r_const * (n : ℝ))
  linarith

lemma theta_pos (n : ℕ) (hn : n ≠ 0) : 0 < theta n := by
  have h_irr := r_const_mul_irrational n hn
  have h_ne := irrational_ne_int (r_const * (n : ℝ)) h_irr (Int.floor (r_const * (n : ℝ)))
  have h_nonneg := theta_nonneg n
  have h_neq : theta n ≠ 0 := by
    intro h_zero
    have h_eq : theta n = r_const * (n : ℝ) - (Int.floor (r_const * (n : ℝ)) : ℝ) := rfl
    rw [h_eq] at h_zero
    have : r_const * (n : ℝ) = (Int.floor (r_const * (n : ℝ)) : ℝ) := by linarith
    exact h_ne this
  exact lt_of_le_of_ne h_nonneg h_neq.symm

lemma I_ge_two (n : ℕ) (hn : 1 ≤ n) : 2 ≤ Int.floor (r_const * (n : ℝ)) := by
  have h1 : (2 : ℝ) < r_const := r_const_gt_two
  have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (2 : ℝ) < r_const * (n : ℝ) := by
    have : 0 < r_const := by linarith
    nlinarith
  rw [Int.le_floor]
  exact_mod_cast h3.le

lemma outer_floor_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Int.floor (r_const * (Int.floor (r_const * (n : ℝ)) : ℝ)) := by
  have hI := I_ge_two n hn
  have hI_real : (2 : ℝ) ≤ (Int.floor (r_const * (n : ℝ)) : ℝ) := by exact_mod_cast hI
  have h_r : (2 : ℝ) < r_const := r_const_gt_two
  have h_prod : (0 : ℝ) ≤ r_const * (Int.floor (r_const * (n : ℝ)) : ℝ) := by
    have : (0 : ℝ) ≤ r_const := by linarith
    have : (0 : ℝ) ≤ (Int.floor (r_const * (n : ℝ)) : ℝ) := by linarith
    positivity
  rw [Int.le_floor]
  exact_mod_cast h_prod

lemma toNat_cast (z : ℤ) (hz : 0 ≤ z) : (z.toNat : ℝ) = (z : ℝ) := by
  have := Int.toNat_of_nonneg hz
  exact_mod_cast this

lemma a_eq_outer_floor (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = (Int.floor (r_const * (Int.floor (r_const * (n : ℝ)) : ℝ)) : ℝ) := by
  dsimp [a]
  have h_nonneg := outer_floor_nonneg n hn
  exact toNat_cast _ h_nonneg

lemma theta_mul_bounds (theta : ℝ) (h_nonneg : 0 ≤ theta) (h_lt_one : theta < 1) :
  -1/4 < theta * (2 - r_const) ∧ theta * (2 - r_const) ≤ 0 := by
  have h1 : r_const < 9/4 := r_const_lt_nine_fourths
  have h2 : 2 < r_const := r_const_gt_two
  have h_r_neg : 2 - r_const < 0 := by linarith
  have h_r_gt : -1/4 < 2 - r_const := by linarith
  constructor
  · have : (theta - 1) * (2 - r_const) ≥ 0 := by
      have : theta - 1 ≤ 0 := by linarith
      nlinarith
    linarith
  · nlinarith

lemma val_eq_expr (n : ℕ) (hn : 1 ≤ n) :
  (n : ℝ) * r_sq - (a n : ℝ) = 2 * theta n + (n : ℝ) / 4 - (Int.floor ((n : ℝ) / 4 + theta n * (2 - r_const)) : ℝ) := by
  have h_a := a_eq_outer_floor n hn
  rw [h_a]
  have h_sq := r_sq_eq
  rw [h_sq]
  have h_theta : r_const * (n : ℝ) = (Int.floor (r_const * (n : ℝ)) : ℝ) + theta n := by
    unfold theta
    linarith
  set I := Int.floor (r_const * (n : ℝ))
  have h_arg : r_const * (I : ℝ) = ((n : ℝ) / 4 + theta n * (2 - r_const)) + ((2 * I : ℤ) : ℝ) := by
    push_cast
    have : (I : ℝ) = r_const * (n : ℝ) - theta n := by linarith
    rw [this]
    have h_sq_const : r_const * r_const = 2 * r_const + 1/4 := r_sq_eq
    linear_combination (n : ℝ) * h_sq_const
  rw [h_arg]
  rw [Int.floor_add_intCast]
  push_cast
  linarith

lemma val_eq_mod_expr (n : ℕ) (hn : 1 ≤ n) :
  (n : ℝ) * r_sq - (a n : ℝ) = 2 * theta n + ((n % 4 : ℕ) : ℝ) / 4 - (Int.floor (((n % 4 : ℕ) : ℝ) / 4 + theta n * (2 - r_const)) : ℝ) := by
  have h_div_mod : (n : ℝ) = 4 * (n / 4 : ℕ) + (n % 4 : ℕ) := by exact_mod_cast (Nat.div_add_mod n 4).symm
  set q := n / 4
  set m := n % 4
  have h_m_eq : ((n % 4 : ℕ) : ℝ) = (m : ℝ) := rfl
  rw [h_m_eq]
  have h_div_mod_re : (n : ℝ) = 4 * (q : ℝ) + (m : ℝ) := h_div_mod
  have h_floor : Int.floor ((n : ℝ) / 4 + theta n * (2 - r_const)) = Int.floor ((m : ℝ) / 4 + theta n * (2 - r_const)) + q := by
    have : (n : ℝ) / 4 + theta n * (2 - r_const) = ((m : ℝ) / 4 + theta n * (2 - r_const)) + (q : ℝ) := by
      rw [h_div_mod_re]
      ring
    rw [this]
    exact Int.floor_add_natCast _ q
  rw [val_eq_expr n hn]
  rw [h_floor]
  rw [h_div_mod_re]
  push_cast
  ring

lemma floor_case_0 (theta : ℝ) (h_pos : 0 < theta) (h_bounds : -1/4 < theta * (2 - r_const)) :
  Int.floor ((0 : ℝ) / 4 + theta * (2 - r_const)) = -1 := by
  rw [Int.floor_eq_iff]
  have h_neg : theta * (2 - r_const) < 0 := by
    have h_r : 2 - r_const < 0 := by
      have := r_const_gt_two
      linarith
    exact mul_neg_of_pos_of_neg h_pos h_r
  constructor
  · linarith
  · linarith

lemma floor_case_1 (theta : ℝ) (h_pos : 0 < theta) (h_bounds : -1/4 < theta * (2 - r_const)) :
  Int.floor ((1 : ℝ) / 4 + theta * (2 - r_const)) = 0 := by
  rw [Int.floor_eq_iff]
  have h_neg : theta * (2 - r_const) < 0 := by
    have h_r : 2 - r_const < 0 := by
      have := r_const_gt_two
      linarith
    exact mul_neg_of_pos_of_neg h_pos h_r
  constructor
  · linarith
  · linarith

lemma floor_case_2 (theta : ℝ) (h_pos : 0 < theta) (h_bounds : -1/4 < theta * (2 - r_const)) :
  Int.floor ((2 : ℝ) / 4 + theta * (2 - r_const)) = 0 := by
  rw [Int.floor_eq_iff]
  have h_neg : theta * (2 - r_const) < 0 := by
    have h_r : 2 - r_const < 0 := by
      have := r_const_gt_two
      linarith
    exact mul_neg_of_pos_of_neg h_pos h_r
  constructor
  · linarith
  · linarith

lemma floor_case_3 (theta : ℝ) (h_pos : 0 < theta) (h_bounds : -1/4 < theta * (2 - r_const)) :
  Int.floor ((3 : ℝ) / 4 + theta * (2 - r_const)) = 0 := by
  rw [Int.floor_eq_iff]
  have h_neg : theta * (2 - r_const) < 0 := by
    have h_r : 2 - r_const < 0 := by
      have := r_const_gt_two
      linarith
    exact mul_neg_of_pos_of_neg h_pos h_r
  constructor
  · linarith
  · linarith

theorem oeis_341254_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (1/4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧ (n : ℝ) * r_sq - (a n : ℝ) < 3 := by
  have h_val := val_eq_mod_expr n hn
  rw [h_val]
  have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have h_theta_nonneg := theta_nonneg n
  have h_theta_lt_one := theta_lt_one n
  have h_theta_pos := theta_pos n (by omega)
  have h_bounds := theta_mul_bounds (theta n) h_theta_nonneg h_theta_lt_one
  rcases h_mod with hm0 | hm1 | hm2 | hm3
  · rw [hm0]
    push_cast
    have h_floor := floor_case_0 (theta n) h_theta_pos h_bounds.1
    rw [h_floor]
    push_cast
    constructor
    · linarith
    · linarith
  · rw [hm1]
    push_cast
    have h_floor := floor_case_1 (theta n) h_theta_pos h_bounds.1
    rw [h_floor]
    push_cast
    constructor
    · linarith
    · linarith
  · rw [hm2]
    push_cast
    have h_floor := floor_case_2 (theta n) h_theta_pos h_bounds.1
    rw [h_floor]
    push_cast
    constructor
    · linarith
    · linarith
  · rw [hm3]
    push_cast
    have h_floor := floor_case_3 (theta n) h_theta_pos h_bounds.1
    rw [h_floor]
    push_cast
    constructor
    · linarith
    · linarith

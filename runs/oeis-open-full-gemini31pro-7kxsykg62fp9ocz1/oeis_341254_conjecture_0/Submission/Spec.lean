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

lemma j_cases (n : ℕ) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  omega

lemma sqrt_5_bounds : 2 < sqrt 5 ∧ sqrt 5 < 5/2 := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt; norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]; norm_num

lemma r_sq_eq : r_sq = 2 * r_const + 1/4 := by
  dsimp [r_const, r_sq]
  have : (sqrt 5) ^ 2 = 5 := sq_sqrt (by norm_num)
  calc
    ((2 + sqrt 5) / 2) * ((2 + sqrt 5) / 2) = (4 + 4 * sqrt 5 + (sqrt 5)^2) / 4 := by ring
    _ = (4 + 4 * sqrt 5 + 5) / 4 := by rw [this]
    _ = 2 * ((2 + sqrt 5) / 2) + 1/4 := by ring

lemma c_bounds :
    let c := r_const - 2
    0 < c ∧ c < 1/4 := by
  intro c
  have h1 := sqrt_5_bounds.1
  have h2 := sqrt_5_bounds.2
  dsimp [c, r_const]
  constructor <;> linarith

lemma irrational_r_const_mul_n {n : ℕ} (hn : 1 ≤ n) : Irrational (r_const * n) := by
  dsimp [r_const]
  have h_prime : Nat.Prime 5 := by norm_num
  have h_irr : Irrational (sqrt 5) := Nat.Prime.irrational_sqrt h_prime
  have h1 : Irrational (sqrt 5 + 2) := h_irr.add_natCast 2
  have h2 : Irrational (2 + sqrt 5) := by rw [add_comm] at h1; exact h1
  have h3 : Irrational ((2 + sqrt 5) / 2) := h2.div_natCast (by norm_num)
  have h4 : n ≠ 0 := by omega
  exact h3.mul_natCast h4

lemma fract_pos_of_irrational {x : ℝ} (h : Irrational x) : 0 < Int.fract x := by
  have h1 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h2 : Int.fract x ≠ 0 := by
    intro h_eq
    have h_rat : ∃ q : ℚ, ↑q = x := by
      use ⌊x⌋
      have h3 := Int.floor_add_fract x
      rw [h_eq, add_zero] at h3
      simp [h3]
    exact h h_rat
  exact lt_of_le_of_ne h1 h2.symm

lemma a_eq {n : ℕ} (hn : 1 ≤ n) : (a n : ℝ) = (Int.floor (r_const * (Int.floor (r_const * n) : ℝ)) : ℝ) := by
  have h_inner : 0 ≤ Int.floor (r_const * n) := by
    apply Int.floor_nonneg.mpr
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hr : (0:ℝ) ≤ r_const := by dsimp [r_const]; positivity
    positivity
  have h_outer : 0 ≤ Int.floor (r_const * (Int.floor (r_const * n) : ℝ)) := by
    apply Int.floor_nonneg.mpr
    have hr : (0:ℝ) ≤ r_const := by dsimp [r_const]; positivity
    have h_inner_cast : (0:ℝ) ≤ (Int.floor (r_const * n) : ℝ) := by exact_mod_cast h_inner
    positivity
  dsimp [a]
  have h_toNat := Int.toNat_of_nonneg h_outer
  rw [← h_toNat]
  push_cast
  rfl

lemma n_r_sq_eq (n : ℕ) :
    let k := Int.floor (r_const * n)
    let x := Int.fract (r_const * n)
    (n : ℝ) * r_sq = r_const * k + r_const * x := by
  intro k x
  have h_nx : (n : ℝ) * r_const = k + x := by
    dsimp [k, x]
    rw [mul_comm]
    exact (Int.floor_add_fract (r_const * ↑n)).symm
  calc
    (n : ℝ) * r_sq = (n : ℝ) * r_const * r_const := by dsimp [r_sq]; rw [mul_assoc]
    _ = (k + x) * r_const := by rw [h_nx]
    _ = r_const * k + r_const * x := by ring

lemma r_const_k_eq (n : ℕ) :
    let k := Int.floor (r_const * n)
    let x := Int.fract (r_const * n)
    let c := r_const - 2
    r_const * (k : ℝ) = 2 * (k : ℝ) + (n : ℝ) / 4 - c * x := by
  intro k x c
  have h_nx : (n : ℝ) * r_const = (k : ℝ) + x := by
    dsimp [k, x]
    rw [mul_comm]
    exact (Int.floor_add_fract (r_const * ↑n)).symm
  have h_k : (k : ℝ) = (n : ℝ) * r_const - x := by linarith
  have h_r_sq : r_const * r_const = 2 * r_const + 1/4 := r_sq_eq
  calc
    r_const * (k : ℝ) = r_const * ((n : ℝ) * r_const - x) := by rw [h_k]
    _ = (n : ℝ) * (r_const * r_const) - r_const * x := by ring
    _ = (n : ℝ) * (2 * r_const + 1/4) - r_const * x := by rw [h_r_sq]
    _ = 2 * ((n : ℝ) * r_const) + (n : ℝ) / 4 - r_const * x := by ring
    _ = 2 * (k + x) + (n : ℝ) / 4 - r_const * x := by rw [h_nx]
    _ = 2 * (k : ℝ) + (n : ℝ) / 4 - (r_const - 2) * x := by ring

lemma fract_2k (k : ℤ) (y : ℝ) : Int.fract (2 * (k : ℝ) + y) = Int.fract y := by
  have h1 : 2 * (k : ℝ) = ((2 * k : ℤ) : ℝ) := by push_cast; rfl
  rw [h1]
  exact Int.fract_intCast_add (2 * k) y

lemma n_div_4 (n : ℕ) : (n : ℝ) / 4 = ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) / 4 := by
  have h1 : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  have h2 : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
    nth_rw 1 [h1]
    push_cast; rfl
  rw [h2]
  ring

lemma fract_of_neg (y : ℝ) (h1 : -1 < y) (h2 : y < 0) : Int.fract y = y + 1 := by
  have : ⌊y⌋ = -1 := by
    apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
  exact (Int.self_sub_floor y).symm.trans (by rw [this]; push_cast; ring)

lemma fract_of_pos (y : ℝ) (h1 : 0 ≤ y) (h2 : y < 1) : Int.fract y = y := by
  have : ⌊y⌋ = 0 := by
    apply Int.floor_eq_iff.mpr; push_cast; constructor <;> linarith
  exact (Int.self_sub_floor y).symm.trans (by rw [this]; push_cast; ring)

lemma F_eq (c x j : ℝ) (hc1 : 0 < c) (hc2 : c < 1/4) (hx1 : 0 < x) (hx2 : x < 1)
    (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) :
    Int.fract (j/4 - c * x) = if j = 0 then (j/4 - c * x) + 1 else (j/4 - c * x) := by
  have cx_pos : 0 < c * x := mul_pos hc1 hx1
  have cx_lt : c * x < 1/4 := by nlinarith
  rcases hj with rfl | rfl | rfl | rfl
  · rw [if_pos rfl]; apply fract_of_neg <;> linarith
  · rw [if_neg (by norm_num)]; apply fract_of_pos <;> linarith
  · rw [if_neg (by norm_num)]; apply fract_of_pos <;> linarith
  · rw [if_neg (by norm_num)]; apply fract_of_pos <;> linarith

lemma bounds_helper2 (c x j : ℝ) (hc1 : 0 < c) (hc2 : c < 1/4) (hx1 : 0 < x) (hx2 : x < 1)
    (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) :
    let cx := c * x
    let F := if j = 0 then (j/4 - cx) + 1 else (j/4 - cx)
    let Y := F + (c + 2) * x
    1/4 < Y ∧ Y < 3 := by
  intro cx F Y
  have h_cx_pos : 0 < cx := mul_pos hc1 hx1
  have h_cx_lt : cx < 1/4 := by nlinarith
  rcases hj with rfl | rfl | rfl | rfl
  · dsimp [F, Y, cx]; norm_num; constructor <;> linarith
  · dsimp [F, Y, cx]; norm_num; constructor <;> linarith
  · dsimp [F, Y, cx]; norm_num; constructor <;> linarith
  · dsimp [F, Y, cx]; norm_num; constructor <;> linarith

/-- A341254 Conjecture: $1/4 < n \cdot r^2 - a(n) < 3$ for $n \ge 1$. -/
theorem oeis_341254_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (1/4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧ (n : ℝ) * r_sq - (a n : ℝ) < 3 := by
  let k := Int.floor (r_const * n)
  let x := Int.fract (r_const * n)
  let c := r_const - 2

  have hc : 0 < c ∧ c < 1/4 := c_bounds
  have hx_irr : Irrational (r_const * n) := irrational_r_const_mul_n hn
  have hx_pos : 0 < x := fract_pos_of_irrational hx_irr
  have hx_lt : x < 1 := Int.fract_lt_one (r_const * n)

  have diff_eq : (n : ℝ) * r_sq - (a n : ℝ) = Int.fract (r_const * k) + r_const * x := by
    rw [a_eq hn]
    have h1 : (n : ℝ) * r_sq = r_const * k + r_const * x := n_r_sq_eq n
    rw [h1]
    have h_fract : Int.fract (r_const * (k : ℝ)) = r_const * (k : ℝ) - Int.floor (r_const * (k : ℝ)) := by
      exact (Int.self_sub_floor (r_const * (k : ℝ))).symm
    linarith

  have h_k_eq : r_const * (k : ℝ) = 2 * (k : ℝ) + (n : ℝ) / 4 - c * x := r_const_k_eq n

  have fract_eq : Int.fract (r_const * k) = Int.fract ((n : ℝ) / 4 - c * x) := by
    rw [h_k_eq]
    have : 2 * (k : ℝ) + (n : ℝ) / 4 - c * x = 2 * (k : ℝ) + ((n : ℝ) / 4 - c * x) := by ring
    rw [this]
    exact fract_2k k ((n : ℝ) / 4 - c * x)

  have n_div_4_eq : (n : ℝ) / 4 = ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) / 4 := n_div_4 n

  have fract_eq2 : Int.fract ((n : ℝ) / 4 - c * x) = Int.fract (((n % 4 : ℕ) : ℝ) / 4 - c * x) := by
    rw [n_div_4_eq]
    have : ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) / 4 - c * x = ((n / 4 : ℕ) : ℝ) + (((n % 4 : ℕ) : ℝ) / 4 - c * x) := by ring
    rw [this]
    exact Int.fract_natCast_add (n / 4 : ℕ) (((n % 4 : ℕ) : ℝ) / 4 - c * x)

  rw [diff_eq, fract_eq, fract_eq2]
  let j : ℝ := ((n % 4 : ℕ) : ℝ)
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    have h_mod := j_cases n
    rcases h_mod with h | h | h | h
    · left; dsimp [j]; rw [h]; push_cast; rfl
    · right; left; dsimp [j]; rw [h]; push_cast; rfl
    · right; right; left; dsimp [j]; rw [h]; push_cast; rfl
    · right; right; right; dsimp [j]; rw [h]; push_cast; rfl

  have hF := F_eq c x j hc.1 hc.2 hx_pos hx_lt hj
  rw [hF]
  have hY := bounds_helper2 c x j hc.1 hc.2 hx_pos hx_lt hj
  have h_r_const : r_const = c + 2 := by dsimp [c]; ring
  have h_subst : (if j = 0 then j / 4 - c * x + 1 else j / 4 - c * x) + r_const * x =
      (if j = 0 then j / 4 - c * x + 1 else j / 4 - c * x) + (c + 2) * x := by rw [h_r_const]
  rw [h_subst]
  exact hY

theorem oeis_341254_conjecture_0.disproof : ¬ (type_of% @oeis_341254_conjecture_0) := sorry

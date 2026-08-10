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

lemma r_const_sq_identity : r_sq = 2 * r_const + (1/4 : ℝ) := by
  unfold r_sq r_const
  have hsq : (sqrt (5:ℝ)) ^ 2 = 5 := by
    rw [sq_sqrt] <;> norm_num
  nlinarith

lemma r_const_gt_two : (2:ℝ) < r_const := by
  unfold r_const
  have h : (2:ℝ) < sqrt 5 := by
    rw [← sq_lt_sq₀ (by norm_num) (sqrt_nonneg 5)]
    rw [sq_sqrt] <;> norm_num
  linarith

lemma r_const_pos : (0:ℝ) < r_const := by
  have h := r_const_gt_two
  linarith

lemma beta_pos : (0:ℝ) < r_const - 2 := by
  have h := r_const_gt_two
  linarith

lemma beta_lt_quarter : r_const - 2 < (1/4 : ℝ) := by
  unfold r_const
  have h : sqrt (5:ℝ) < 9/4 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  linarith

lemma r_const_mul_nat_ne_int (n : ℕ) (hn : 1 ≤ n) (z : ℤ) : r_const * (n:ℝ) ≠ (z:ℝ) := by
  intro hz
  have hsqrt_irr : Irrational (sqrt (5:ℝ)) := by
    simpa using (Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num))
  have hmulR : (n:ℝ) * sqrt (5:ℝ) = ((2 * z - 2 * (n:ℤ) : ℤ) : ℝ) := by
    unfold r_const at hz
    norm_num at hz
    norm_num
    nlinarith
  have hn0 : n ≠ 0 := by omega
  have hIrr : Irrational ((n:ℝ) * sqrt (5:ℝ)) := hsqrt_irr.natCast_mul hn0
  exact hIrr.ne_int _ hmulR

lemma fract_pos_of_floor {x : ℝ} (hx : ∀ z : ℤ, x ≠ (z:ℝ)) : 0 < x - (Int.floor x : ℝ) := by
  have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hne : x ≠ (Int.floor x : ℝ) := hx (Int.floor x)
  have hlt : (Int.floor x : ℝ) < x := lt_of_le_of_ne hle (Ne.symm hne)
  linarith

lemma floor_aux_zero (q : ℤ) {f : ℝ} (hfpos : 0 < f) (hf1 : f < 1) :
    Int.floor (((q:ℝ)) - (r_const - 2) * f) = q - 1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · have hbeta_lt : (r_const - 2) * f < 1 := by
      have hb := beta_lt_quarter
      have hbpos := beta_pos
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hb hfpos) (by linarith [hf1])
    norm_num
    linarith
  · have hbeta_pos : 0 < (r_const - 2) * f := mul_pos beta_pos hfpos
    norm_num
    linarith

lemma floor_aux_one (q : ℤ) {c f : ℝ} (hc : c = (1/4:ℝ) ∨ c = (1/2:ℝ) ∨ c = (3/4:ℝ))
    (hf0 : 0 ≤ f) (hf1 : f < 1) :
    Int.floor (((q:ℝ)) + c - (r_const - 2) * f) = q := by
  apply Int.floor_eq_iff.mpr
  constructor
  · norm_num
    rcases hc with rfl | rfl | rfl
    · have hbpos : 0 < r_const - 2 := beta_pos
      have hmul : (r_const - 2) * f < (1/4:ℝ) := by
        have hmul1 : (r_const - 2) * f < (r_const - 2) * 1 :=
          mul_lt_mul_of_pos_left hf1 hbpos
        nlinarith [hmul1, beta_lt_quarter]
      linarith
    · have hbpos : 0 < r_const - 2 := beta_pos
      have hmul : (r_const - 2) * f < (1/4:ℝ) := by
        have hmul1 : (r_const - 2) * f < (r_const - 2) * 1 :=
          mul_lt_mul_of_pos_left hf1 hbpos
        nlinarith [hmul1, beta_lt_quarter]
      linarith
    · have hbpos : 0 < r_const - 2 := beta_pos
      have hmul : (r_const - 2) * f < (1/4:ℝ) := by
        have hmul1 : (r_const - 2) * f < (r_const - 2) * 1 :=
          mul_lt_mul_of_pos_left hf1 hbpos
        nlinarith [hmul1, beta_lt_quarter]
      linarith
  · norm_num
    have hbpos : 0 < r_const - 2 := beta_pos
    have hmul_nonneg : 0 ≤ (r_const - 2) * f := mul_nonneg (le_of_lt hbpos) hf0
    rcases hc with rfl | rfl | rfl <;> linarith

/-- A341254 Conjecture: $1/4 < n \cdot r^2 - a(n) < 3$ for $n \ge 1$. -/
theorem oeis_341254_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (1/4 : ℝ) < (n : ℝ) * r_sq - (a n : ℝ) ∧ (n : ℝ) * r_sq - (a n : ℝ) < 3 :=
by
  let m : ℤ := Int.floor (r_const * (n:ℝ))
  let f : ℝ := r_const * (n:ℝ) - (m:ℝ)
  have hf0 : 0 ≤ f := by
    change 0 ≤ r_const * (n:ℝ) - (m:ℝ)
    have hle : (m:ℝ) ≤ r_const * (n:ℝ) := by
      dsimp [m]
      exact Int.floor_le (r_const * (n:ℝ))
    linarith
  have hf1 : f < 1 := by
    change r_const * (n:ℝ) - (m:ℝ) < 1
    have hlt : r_const * (n:ℝ) < (m:ℝ) + 1 := by
      dsimp [m]
      exact Int.lt_floor_add_one (r_const * (n:ℝ))
    linarith
  have hfpos : 0 < f := by
    change 0 < r_const * (n:ℝ) - (m:ℝ)
    dsimp [m]
    exact fract_pos_of_floor (r_const_mul_nat_ne_int n hn)
  have hm_eq : r_const * (n:ℝ) = (m:ℝ) + f := by
    dsimp [f]
    ring
  have hfloor_inner : Int.floor (r_const * (n:ℝ)) = m := rfl
  have hfloor_nonneg : 0 ≤ Int.floor (r_const * (m:ℝ)) := by
    rw [Int.floor_nonneg]
    have hm_nonneg_int : 0 ≤ m := by
      rw [Int.le_floor]
      have hrpos := r_const_pos
      have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
      simpa using (mul_nonneg (le_of_lt hrpos) hnR)
    have hm_nonneg : (0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm_nonneg_int
    exact mul_nonneg (le_of_lt r_const_pos) hm_nonneg
  have ha_cast : (a n : ℝ) = (Int.floor (r_const * (m:ℝ)) : ℝ) := by
    unfold a
    dsimp
    rw [hfloor_inner]
    have hto : (((Int.floor (r_const * (m:ℝ))).toNat : ℕ) : ℤ) = Int.floor (r_const * (m:ℝ)) :=
      Int.toNat_of_nonneg hfloor_nonneg
    exact_mod_cast hto
  have h_rm : r_const * (m:ℝ) = ((2 * m : ℤ) : ℝ) + ((n:ℝ)/4 - (r_const - 2) * f) := by
    have hid : r_const * r_const = 2 * r_const + (1/4 : ℝ) := r_const_sq_identity
    have hmn : (m:ℝ) = r_const * (n:ℝ) - f := by linarith [hm_eq]
    rw [hmn]
    ring_nf
    have hcast : ((m * 2 : ℤ) : ℝ) = 2 * (m:ℝ) := by norm_num [mul_comm]
    nlinarith [hid, hcast]
  have h_floor_rm (k : ℤ) (hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = k) :
      Int.floor (r_const * (m:ℝ)) = (2 * m : ℤ) + k := by
    rw [h_rm]
    rw [Int.floor_intCast_add]
    rw [hk]
  have hD (k : ℤ) (hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = k) :
      (n:ℝ) * r_sq - (a n : ℝ) = 2 * f + (n:ℝ)/4 - (k:ℝ) := by
    rw [ha_cast, h_floor_rm k hk]
    have hid : r_sq = 2 * r_const + (1/4 : ℝ) := r_const_sq_identity
    have hcast : (((2 * m + k : ℤ) : ℝ)) = 2 * (m:ℝ) + (k:ℝ) := by norm_num
    nlinarith [hid, hm_eq, hcast]
  let q : ℕ := n / 4
  have hmodlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hmod : n % 4
  · have hnq : n = 4 * q := by
      dsimp [q]
      omega
    have hnqR : (n:ℝ)/4 = ((q:ℤ):ℝ) := by
      rw [hnq]
      norm_num
    have hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = (q:ℤ) - 1 := by
      rw [hnqR]
      exact floor_aux_zero (q:ℤ) hfpos hf1
    have hdeq := hD ((q:ℤ) - 1) hk
    rw [hnqR] at hdeq
    norm_num at hdeq
    constructor <;> nlinarith [hdeq, hfpos, hf1]
  · have hnq : n = 4 * q + 1 := by
      dsimp [q]
      omega
    have hnqR : (n:ℝ)/4 = ((q:ℤ):ℝ) + (1/4:ℝ) := by
      rw [hnq]
      norm_num
      ring
    have hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = (q:ℤ) := by
      rw [hnqR]
      exact floor_aux_one (q:ℤ) (Or.inl rfl) hf0 hf1
    have hdeq := hD (q:ℤ) hk
    rw [hnqR] at hdeq
    norm_num at hdeq
    constructor <;> nlinarith [hdeq, hfpos, hf1]
  · have hnq : n = 4 * q + 2 := by
      dsimp [q]
      omega
    have hnqR : (n:ℝ)/4 = ((q:ℤ):ℝ) + (1/2:ℝ) := by
      rw [hnq]
      norm_num
      ring
    have hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = (q:ℤ) := by
      rw [hnqR]
      exact floor_aux_one (q:ℤ) (Or.inr (Or.inl rfl)) hf0 hf1
    have hdeq := hD (q:ℤ) hk
    rw [hnqR] at hdeq
    norm_num at hdeq
    constructor <;> nlinarith [hdeq, hf0, hf1]
  · have hnq : n = 4 * q + 3 := by
      dsimp [q]
      omega
    have hnqR : (n:ℝ)/4 = ((q:ℤ):ℝ) + (3/4:ℝ) := by
      rw [hnq]
      norm_num
      ring
    have hk : Int.floor ((n:ℝ)/4 - (r_const - 2) * f) = (q:ℤ) := by
      rw [hnqR]
      exact floor_aux_one (q:ℤ) (Or.inr (Or.inr rfl)) hf0 hf1
    have hdeq := hD (q:ℤ) hk
    rw [hnqR] at hdeq
    norm_num at hdeq
    constructor <;> nlinarith [hdeq, hf0, hf1]

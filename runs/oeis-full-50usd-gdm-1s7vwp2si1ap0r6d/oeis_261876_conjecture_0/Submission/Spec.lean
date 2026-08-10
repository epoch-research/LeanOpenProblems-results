import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000
set_option maxHeartbeats 100000000

open Nat Finset BigOperators

def a (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := IsSquare k

  -- Since ^2 \le n$, a simple and safe iteration bound for all variables is +1$.
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if h_z : z > 0 then
      let k := x^2 + y^2 + z^2
      if h_le : k ≤ n then
        let r := n - k
        -- The existence of a natural number $ such that ^2 = r$.
        if is_square r then
          let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
          -- The primary sequence condition: yz$ must be a perfect square.
          if is_square condition_expr then 1 else 0
        else 0
      else 0
    else 0

def special_m_set : Set ℕ :=
  {1, 7, 23, 647, 863}

def sqrt_step (r : ℕ) (low high : ℕ) (steps : ℕ) : ℕ :=
  match steps with
  | 0 => low
  | s + 1 =>
    let mid := (low + high) / 2
    if mid * mid ≤ r then
      sqrt_step r mid high s
    else
      sqrt_step r low mid s

def fast_sqrt (r : ℕ) : ℕ :=
  sqrt_step r 0 265 9

def fast_sqrt_large (r : ℕ) : ℕ :=
  sqrt_step r 0 210000 18

def is_square_large (r : ℕ) : Bool :=
  let s := fast_sqrt_large r
  s * s == r

def verify_sqrt (low : ℕ) (depth : ℕ) : Bool :=
  match depth with
  | 0 => fast_sqrt_large (low * low) == low
  | d + 1 =>
    verify_sqrt low d && verify_sqrt (low + 2^d) d

lemma verify_sqrt_correct (depth : ℕ) : ∀ low, verify_sqrt low depth = true → ∀ b, low ≤ b ∧ b < low + 2^depth → fast_sqrt_large (b * b) = b := by
  induction depth with
  | zero =>
    intro low h b hb
    have : b = low := by omega
    rw [this]
    exact decide_eq_true_iff.mp h
  | succ d ih =>
    intro low h b hb
    rw [verify_sqrt] at h
    rw [Bool.and_eq_true] at h
    have h_left := h.1
    have h_right := h.2
    have h_split : 2^(d + 1) = 2^d + 2^d := by rw [pow_succ] ; omega
    by_cases hb_left : b < low + 2^d
    · exact ih low h_left b (by omega)
    · have : b ≥ low + 2^d := by omega
      exact ih (low + 2^d) h_right b (by omega)

lemma fast_sqrt_large_correct_0 : verify_sqrt 0 14 = true := by decide
lemma fast_sqrt_large_correct_1 : verify_sqrt 16384 14 = true := by decide
lemma fast_sqrt_large_correct_2 : verify_sqrt 32768 14 = true := by decide
lemma fast_sqrt_large_correct_3 : verify_sqrt 49152 14 = true := by decide
lemma fast_sqrt_large_correct_4 : verify_sqrt 65536 14 = true := by decide
lemma fast_sqrt_large_correct_5 : verify_sqrt 81920 14 = true := by decide
lemma fast_sqrt_large_correct_6 : verify_sqrt 98304 14 = true := by decide
lemma fast_sqrt_large_correct_7 : verify_sqrt 114688 14 = true := by decide
lemma fast_sqrt_large_correct_8 : verify_sqrt 131072 14 = true := by decide
lemma fast_sqrt_large_correct_9 : verify_sqrt 147456 14 = true := by decide
lemma fast_sqrt_large_correct_10 : verify_sqrt 163840 14 = true := by decide
lemma fast_sqrt_large_correct_11 : verify_sqrt 180224 14 = true := by decide
lemma fast_sqrt_large_correct_12 : verify_sqrt 196608 13 = true := by decide
lemma fast_sqrt_large_correct_13 : verify_sqrt 204800 12 = true := by decide
lemma fast_sqrt_large_correct_14 : verify_sqrt 208896 10 = true := by decide
lemma fast_sqrt_large_correct_15 : ∀ b, 209920 ≤ b ∧ b < 210000 → fast_sqrt_large (b * b) = b := by decide

lemma fast_sqrt_large_correct : ∀ b < 210000, fast_sqrt_large (b * b) = b := by
  intro b hb
  rcases lt_or_ge b 16384 with h0 | h0
  · exact verify_sqrt_correct 14 0 fast_sqrt_large_correct_0 b (by omega)
  rcases lt_or_ge b 32768 with h1 | h1
  · exact verify_sqrt_correct 14 16384 fast_sqrt_large_correct_1 b (by omega)
  rcases lt_or_ge b 49152 with h2 | h2
  · exact verify_sqrt_correct 14 32768 fast_sqrt_large_correct_2 b (by omega)
  rcases lt_or_ge b 65536 with h3 | h3
  · exact verify_sqrt_correct 14 49152 fast_sqrt_large_correct_3 b (by omega)
  rcases lt_or_ge b 81920 with h4 | h4
  · exact verify_sqrt_correct 14 65536 fast_sqrt_large_correct_4 b (by omega)
  rcases lt_or_ge b 98304 with h5 | h5
  · exact verify_sqrt_correct 14 81920 fast_sqrt_large_correct_5 b (by omega)
  rcases lt_or_ge b 114688 with h6 | h6
  · exact verify_sqrt_correct 14 98304 fast_sqrt_large_correct_6 b (by omega)
  rcases lt_or_ge b 131072 with h7 | h7
  · exact verify_sqrt_correct 14 114688 fast_sqrt_large_correct_7 b (by omega)
  rcases lt_or_ge b 147456 with h8 | h8
  · exact verify_sqrt_correct 14 131072 fast_sqrt_large_correct_8 b (by omega)
  rcases lt_or_ge b 163840 with h9 | h9
  · exact verify_sqrt_correct 14 147456 fast_sqrt_large_correct_9 b (by omega)
  rcases lt_or_ge b 180224 with h10 | h10
  · exact verify_sqrt_correct 14 163840 fast_sqrt_large_correct_10 b (by omega)
  rcases lt_or_ge b 196608 with h11 | h11
  · exact verify_sqrt_correct 14 180224 fast_sqrt_large_correct_11 b (by omega)
  rcases lt_or_ge b 209920 with h12 | h12
  · exact verify_sqrt_correct 13 196608 fast_sqrt_large_correct_12 b (by omega)
  rcases lt_or_ge b 208896 with h13 | h13
  · exact verify_sqrt_correct 12 204800 fast_sqrt_large_correct_13 b (by omega)
  rcases lt_or_ge b 209920 with h14 | h14
  · exact verify_sqrt_correct 10 208896 fast_sqrt_large_correct_14 b (by omega)
  · exact fast_sqrt_large_correct_15 b ⟨h14, hb⟩

lemma fast_sqrt_correct : ∀ b < 264, fast_sqrt (b * b) = b := by decide
lemma fast_sqrt_large_correct_all : ∀ b < 210000, fast_sqrt_large (b * b) = b := fast_sqrt_large_correct

def is_square_fast_old (r : ℕ) : Bool :=
  let s := fast_sqrt r
  s * s == r

def is_square_fast (r : ℕ) : Bool :=
  if r % 16 = 0 ∨ r % 16 = 1 ∨ r % 16 = 4 ∨ r % 16 = 9 then
    if r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 4 ∨ r % 9 = 7 then
      if r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 4 then
        if r % 7 = 0 ∨ r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4 then
          is_square_fast_old r
        else false
      else false
    else false
  else false

lemma is_square_fast_correct : ∀ b < 264, is_square_fast (b * b) = true := by decide

lemma is_square_fast_iff (r : ℕ) (hr : r < 69384) : IsSquare r ↔ is_square_fast r = true := by
  constructor
  · rintro ⟨b, hb⟩
    have hb_le : b < 264 := by
      have : b * b < 69696 := by omega
      nlinarith
    have h_sq_fast := is_square_fast_correct b hb_le
    have h_r : r = b * b := hb
    rw [h_r, h_sq_fast]
  · intro h
    have h_old : is_square_fast_old r = true := by
      unfold is_square_fast at h
      split_ifs at h
      · exact h
    have h_eq : fast_sqrt r * fast_sqrt r = r := by
      exact decide_eq_true_iff.mp h_old
    exact ⟨fast_sqrt r, h_eq.symm⟩

lemma is_square_large_iff (cond : ℕ) (hc : cond < 210000^2) : IsSquare cond ↔ is_square_large cond = true := by
  constructor
  · rintro ⟨b, hb⟩
    have hb_le : b < 210000 := by
      have : b * b < 210000 * 210000 := by omega
      nlinarith
    have h_sqrt := fast_sqrt_large_correct b hb_le
    rw [is_square_large]
    have h_c : cond = b * b := hb
    rw [h_c]
    rw [h_sqrt]
    rfl
  · intro h
    rw [is_square_large] at h
    have h_eq : fast_sqrt_large cond * fast_sqrt_large cond = cond := by
      exact decide_eq_true_iff.mp h
    exact ⟨fast_sqrt_large cond, h_eq.symm⟩

def term_func (x y z : ℕ) : ℕ :=
  if h_z : z > 0 then
    let k := x^2 + y^2 + z^2
    if h_le : k ≤ 69383 then
      let r := 69383 - k
      if is_square_fast r then
        let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
        if is_square_large condition_expr then 1 else 0
      else 0
    else 0
  else 0

def sum_z_firstorder (x y z : ℕ) (depth : ℕ) : ℕ :=
  match depth with
  | 0 => term_func x y z
  | d + 1 =>
    sum_z_firstorder x y z d + sum_z_firstorder x y (z + 2^d) d

def sum_y_firstorder (x y : ℕ) (depth_y depth_z : ℕ) : ℕ :=
  match depth_y with
  | 0 =>
    sum_z_firstorder x y 0 depth_z + sum_z_firstorder x y 256 3
  | d + 1 =>
    sum_y_firstorder x y d depth_z + sum_y_firstorder x (y + 2^d) d depth_z

lemma sum_z_firstorder_zero_of_gt (x y z : ℕ) (depth_z : ℕ) (h : x^2 + y^2 + z^2 > 69383) :
  sum_z_firstorder x y z depth_z = 0 := by
  induction depth_z generalizing z with
  | zero =>
    rw [sum_z_firstorder, term_func]
    dsimp only
    split_ifs
    · omega
    all_goals rfl
  | succ d ih =>
    rw [sum_z_firstorder]
    have h1 : x^2 + y^2 + z^2 > 69383 := h
    have h2 : x^2 + y^2 + (z + 2^d)^2 > 69383 := by
      have : z^2 ≤ (z + 2^d)^2 := Nat.pow_le_pow_left (Nat.le_add_right z (2^d)) 2
      omega
    rw [ih z h1, ih (z + 2^d) h2, add_zero]

lemma sum_y_firstorder_zero_of_gt (x y : ℕ) (depth_y depth_z : ℕ) (h : x^2 + y^2 > 69383) :
  sum_y_firstorder x y depth_y depth_z = 0 := by
  induction depth_y generalizing y with
  | zero =>
    rw [sum_y_firstorder]
    have h1 : x^2 + y^2 + 0^2 > 69383 := by omega
    have h2 : x^2 + y^2 + 256^2 > 69383 := by omega
    rw [sum_z_firstorder_zero_of_gt x y 0 depth_z h1]
    rw [sum_z_firstorder_zero_of_gt x y 256 3 h2]
  | succ d ih =>
    rw [sum_y_firstorder]
    have h1 : x^2 + y^2 > 69383 := h
    have h2 : x^2 + (y + 2^d)^2 > 69383 := by
      have : y^2 ≤ (y + 2^d)^2 := Nat.pow_le_pow_left (Nat.le_add_right y (2^d)) 2
      omega
    rw [ih y h1, ih (y + 2^d) h2, add_zero]

syntax "solve_sum" : tactic

macro_rules
  | `(tactic| solve_sum) =>
    `(tactic|
      first
      | (apply sum_y_firstorder_zero_of_gt; decide)
      | decide
      | (rw [sum_y_firstorder] ; dsimp only ; rw [add_zero] ; solve_sum)
      | (rw [sum_y_firstorder] ; dsimp only ; rw [zero_add] ; solve_sum)
      | (rw [sum_y_firstorder] ; dsimp only ; solve_sum ; solve_sum)
     )

theorem sum_z_firstorder_eq_sum (x y z : ℕ) (depth : ℕ) :
  sum_z_firstorder x y z depth = (Finset.range (2^depth)).sum (fun i => term_func x y (z + i)) := by
  induction depth generalizing z with
  | zero =>
    simp [sum_z_firstorder]
  | succ d ih =>
    rw [sum_z_firstorder]
    rw [ih z, ih (z + 2^d)]
    have h_split : 2^(d + 1) = 2^d + 2^d := by
      rw [pow_succ]
      omega
    rw [h_split]
    rw [← Finset.sum_range_add]
    simp only [add_assoc]

theorem sum_y_firstorder_eq_sum (x y : ℕ) (depth_y : ℕ) (depth_z : ℕ) (h_dz : depth_z = 8) :
  sum_y_firstorder x y depth_y depth_z = (Finset.range (2^depth_y)).sum (fun i =>
    (Finset.range 264).sum (fun z => term_func x (y + i) z)) := by
  induction depth_y generalizing y with
  | zero =>
    rw [sum_y_firstorder]
    have h_bin8 : sum_z_firstorder x y 0 depth_z = (Finset.range 256).sum (fun i => term_func x y (0 + i)) := by
      have : 2^depth_z = 256 := by rw [h_dz] ; rfl
      rw [sum_z_firstorder_eq_sum, this]
    have h_bin3 : sum_z_firstorder x y 256 3 = (Finset.range 8).sum (fun i => term_func x y (256 + i)) := by
      have : 2^3 = 8 := rfl
      rw [sum_z_firstorder_eq_sum, this]
    rw [h_bin8, h_bin3]
    simp only [zero_add]
    have h_split : 264 = 256 + 8 := rfl
    rw [h_split]
    rw [← Finset.sum_range_add]
    have h_outer : (∑ i ∈ range (2 ^ 0), ∑ z ∈ range (256 + 8), term_func x (y + i) z) =
      ∑ z ∈ range (256 + 8), term_func x (y + 0) z := by
      have : 2^0 = 1 := rfl
      rw [this, sum_range_one]
    rw [h_outer]
    simp only [add_zero]
    rw [Finset.sum_range_add]
  | succ d ih =>
    rw [sum_y_firstorder]
    rw [ih y, ih (y + 2^d)]
    have h_split : 2^(d + 1) = 2^d + 2^d := by
      rw [pow_succ]
      omega
    rw [h_split]
    rw [Finset.sum_range_add]
    simp only [add_assoc]

def sum_y_128 (x y : ℕ) : ℕ :=
  sum_y_firstorder x y 7 8

theorem sum_range_264_eq_sum_y_firstorder (x : ℕ) :
  (Finset.range 264).sum (fun y => (Finset.range 264).sum (fun z => term_func x y z)) =
  sum_y_128 x 0 + sum_y_128 x 128 + sum_y_firstorder x 256 3 8 := by
  rw [sum_y_128, sum_y_128]
  have h_split : 264 = 256 + 8 := rfl
  rw [h_split, Finset.sum_range_add]
  have h_split_256 : 256 = 128 + 128 := rfl
  rw [h_split_256, Finset.sum_range_add]
  have h_bin7_0 : sum_y_firstorder x 0 7 8 = (∑ i ∈ range 128, ∑ z ∈ range 264, term_func x (0 + i) z) := by
    rw [sum_y_firstorder_eq_sum x 0 7 8 rfl]
    have : 2^7 = 128 := rfl
    rw [this]
  have h_bin7_128 : sum_y_firstorder x 128 7 8 = (∑ i ∈ range 128, ∑ z ∈ range 264, term_func x (128 + i) z) := by
    rw [sum_y_firstorder_eq_sum x 128 7 8 rfl]
    have : 2^7 = 128 := rfl
    rw [this]
  have h_bin3_256 : sum_y_firstorder x 256 3 8 = (∑ i ∈ range 8, ∑ z ∈ range 264, term_func x (256 + i) z) := by
    rw [sum_y_firstorder_eq_sum x 256 3 8 rfl]
    have : 2^3 = 8 := rfl
    rw [this]
  rw [h_bin7_0, h_bin7_128, h_bin3_256]
  simp only [zero_add]

def eval_x (x : ℕ) : ℕ :=
  sum_y_128 x 0 + sum_y_128 x 128 + sum_y_firstorder x 256 3 8

lemma hp0_y0 : sum_y_128 0 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp0_y128 : sum_y_128 0 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp0_y256 : sum_y_firstorder 0 256 3 8 = 0 := by solve_sum
lemma eval_x_0 : eval_x 0 = 0 := by
  rw [eval_x, hp0_y0, hp0_y128, hp0_y256]

lemma hp1_y0 : sum_y_128 1 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp1_y128 : sum_y_128 1 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp1_y256 : sum_y_firstorder 1 256 3 8 = 0 := by solve_sum
lemma eval_x_1 : eval_x 1 = 0 := by
  rw [eval_x, hp1_y0, hp1_y128, hp1_y256]

lemma hp2_y0 : sum_y_128 2 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp2_y128 : sum_y_128 2 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp2_y256 : sum_y_firstorder 2 256 3 8 = 0 := by solve_sum
lemma eval_x_2 : eval_x 2 = 0 := by
  rw [eval_x, hp2_y0, hp2_y128, hp2_y256]

lemma hp3_y0 : sum_y_128 3 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp3_y128 : sum_y_128 3 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp3_y256 : sum_y_firstorder 3 256 3 8 = 0 := by solve_sum
lemma eval_x_3 : eval_x 3 = 0 := by
  rw [eval_x, hp3_y0, hp3_y128, hp3_y256]

lemma hp4_y0 : sum_y_128 4 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp4_y128 : sum_y_128 4 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp4_y256 : sum_y_firstorder 4 256 3 8 = 0 := by solve_sum
lemma eval_x_4 : eval_x 4 = 0 := by
  rw [eval_x, hp4_y0, hp4_y128, hp4_y256]

lemma hp5_y0 : sum_y_128 5 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp5_y128 : sum_y_128 5 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp5_y256 : sum_y_firstorder 5 256 3 8 = 0 := by solve_sum
lemma eval_x_5 : eval_x 5 = 0 := by
  rw [eval_x, hp5_y0, hp5_y128, hp5_y256]

lemma hp6_y0 : sum_y_128 6 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp6_y128 : sum_y_128 6 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp6_y256 : sum_y_firstorder 6 256 3 8 = 0 := by solve_sum
lemma eval_x_6 : eval_x 6 = 0 := by
  rw [eval_x, hp6_y0, hp6_y128, hp6_y256]

lemma hp7_y0 : sum_y_128 7 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp7_y128 : sum_y_128 7 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp7_y256 : sum_y_firstorder 7 256 3 8 = 0 := by solve_sum
lemma eval_x_7 : eval_x 7 = 0 := by
  rw [eval_x, hp7_y0, hp7_y128, hp7_y256]

lemma hp8_y0 : sum_y_128 8 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp8_y128 : sum_y_128 8 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp8_y256 : sum_y_firstorder 8 256 3 8 = 0 := by solve_sum
lemma eval_x_8 : eval_x 8 = 0 := by
  rw [eval_x, hp8_y0, hp8_y128, hp8_y256]

lemma hp9_y0 : sum_y_128 9 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp9_y128 : sum_y_128 9 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp9_y256 : sum_y_firstorder 9 256 3 8 = 0 := by solve_sum
lemma eval_x_9 : eval_x 9 = 0 := by
  rw [eval_x, hp9_y0, hp9_y128, hp9_y256]

lemma hp10_y0 : sum_y_128 10 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp10_y128 : sum_y_128 10 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp10_y256 : sum_y_firstorder 10 256 3 8 = 0 := by solve_sum
lemma eval_x_10 : eval_x 10 = 0 := by
  rw [eval_x, hp10_y0, hp10_y128, hp10_y256]

lemma hp11_y0 : sum_y_128 11 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp11_y128 : sum_y_128 11 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp11_y256 : sum_y_firstorder 11 256 3 8 = 0 := by solve_sum
lemma eval_x_11 : eval_x 11 = 0 := by
  rw [eval_x, hp11_y0, hp11_y128, hp11_y256]

lemma hp12_y0 : sum_y_128 12 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp12_y128 : sum_y_128 12 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp12_y256 : sum_y_firstorder 12 256 3 8 = 0 := by solve_sum
lemma eval_x_12 : eval_x 12 = 0 := by
  rw [eval_x, hp12_y0, hp12_y128, hp12_y256]

lemma hp13_y0 : sum_y_128 13 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp13_y128 : sum_y_128 13 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp13_y256 : sum_y_firstorder 13 256 3 8 = 0 := by solve_sum
lemma eval_x_13 : eval_x 13 = 0 := by
  rw [eval_x, hp13_y0, hp13_y128, hp13_y256]

lemma hp14_y0 : sum_y_128 14 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp14_y128 : sum_y_128 14 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp14_y256 : sum_y_firstorder 14 256 3 8 = 0 := by solve_sum
lemma eval_x_14 : eval_x 14 = 0 := by
  rw [eval_x, hp14_y0, hp14_y128, hp14_y256]

lemma hp15_y0 : sum_y_128 15 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp15_y128 : sum_y_128 15 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp15_y256 : sum_y_firstorder 15 256 3 8 = 0 := by solve_sum
lemma eval_x_15 : eval_x 15 = 0 := by
  rw [eval_x, hp15_y0, hp15_y128, hp15_y256]

lemma hp16_y0 : sum_y_128 16 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp16_y128 : sum_y_128 16 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp16_y256 : sum_y_firstorder 16 256 3 8 = 0 := by solve_sum
lemma eval_x_16 : eval_x 16 = 0 := by
  rw [eval_x, hp16_y0, hp16_y128, hp16_y256]

lemma hp17_y0 : sum_y_128 17 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp17_y128 : sum_y_128 17 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp17_y256 : sum_y_firstorder 17 256 3 8 = 0 := by solve_sum
lemma eval_x_17 : eval_x 17 = 0 := by
  rw [eval_x, hp17_y0, hp17_y128, hp17_y256]

lemma hp18_y0 : sum_y_128 18 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp18_y128 : sum_y_128 18 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp18_y256 : sum_y_firstorder 18 256 3 8 = 0 := by solve_sum
lemma eval_x_18 : eval_x 18 = 0 := by
  rw [eval_x, hp18_y0, hp18_y128, hp18_y256]

lemma hp19_y0 : sum_y_128 19 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp19_y128 : sum_y_128 19 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp19_y256 : sum_y_firstorder 19 256 3 8 = 0 := by solve_sum
lemma eval_x_19 : eval_x 19 = 0 := by
  rw [eval_x, hp19_y0, hp19_y128, hp19_y256]

lemma hp20_y0 : sum_y_128 20 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp20_y128 : sum_y_128 20 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp20_y256 : sum_y_firstorder 20 256 3 8 = 0 := by solve_sum
lemma eval_x_20 : eval_x 20 = 0 := by
  rw [eval_x, hp20_y0, hp20_y128, hp20_y256]

lemma hp21_y0 : sum_y_128 21 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp21_y128 : sum_y_128 21 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp21_y256 : sum_y_firstorder 21 256 3 8 = 0 := by solve_sum
lemma eval_x_21 : eval_x 21 = 0 := by
  rw [eval_x, hp21_y0, hp21_y128, hp21_y256]

lemma hp22_y0 : sum_y_128 22 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp22_y128 : sum_y_128 22 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp22_y256 : sum_y_firstorder 22 256 3 8 = 0 := by solve_sum
lemma eval_x_22 : eval_x 22 = 0 := by
  rw [eval_x, hp22_y0, hp22_y128, hp22_y256]

lemma hp23_y0 : sum_y_128 23 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp23_y128 : sum_y_128 23 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp23_y256 : sum_y_firstorder 23 256 3 8 = 0 := by solve_sum
lemma eval_x_23 : eval_x 23 = 0 := by
  rw [eval_x, hp23_y0, hp23_y128, hp23_y256]

lemma hp24_y0 : sum_y_128 24 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp24_y128 : sum_y_128 24 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp24_y256 : sum_y_firstorder 24 256 3 8 = 0 := by solve_sum
lemma eval_x_24 : eval_x 24 = 0 := by
  rw [eval_x, hp24_y0, hp24_y128, hp24_y256]

lemma hp25_y0 : sum_y_128 25 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp25_y128 : sum_y_128 25 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp25_y256 : sum_y_firstorder 25 256 3 8 = 0 := by solve_sum
lemma eval_x_25 : eval_x 25 = 0 := by
  rw [eval_x, hp25_y0, hp25_y128, hp25_y256]

lemma hp26_y0 : sum_y_128 26 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp26_y128 : sum_y_128 26 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp26_y256 : sum_y_firstorder 26 256 3 8 = 0 := by solve_sum
lemma eval_x_26 : eval_x 26 = 0 := by
  rw [eval_x, hp26_y0, hp26_y128, hp26_y256]

lemma hp27_y0 : sum_y_128 27 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp27_y128 : sum_y_128 27 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp27_y256 : sum_y_firstorder 27 256 3 8 = 0 := by solve_sum
lemma eval_x_27 : eval_x 27 = 0 := by
  rw [eval_x, hp27_y0, hp27_y128, hp27_y256]

lemma hp28_y0 : sum_y_128 28 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp28_y128 : sum_y_128 28 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp28_y256 : sum_y_firstorder 28 256 3 8 = 0 := by solve_sum
lemma eval_x_28 : eval_x 28 = 0 := by
  rw [eval_x, hp28_y0, hp28_y128, hp28_y256]

lemma hp29_y0 : sum_y_128 29 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp29_y128 : sum_y_128 29 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp29_y256 : sum_y_firstorder 29 256 3 8 = 0 := by solve_sum
lemma eval_x_29 : eval_x 29 = 0 := by
  rw [eval_x, hp29_y0, hp29_y128, hp29_y256]

lemma hp30_y0 : sum_y_128 30 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp30_y128 : sum_y_128 30 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp30_y256 : sum_y_firstorder 30 256 3 8 = 0 := by solve_sum
lemma eval_x_30 : eval_x 30 = 0 := by
  rw [eval_x, hp30_y0, hp30_y128, hp30_y256]

lemma hp31_y0 : sum_y_128 31 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp31_y128 : sum_y_128 31 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp31_y256 : sum_y_firstorder 31 256 3 8 = 0 := by solve_sum
lemma eval_x_31 : eval_x 31 = 0 := by
  rw [eval_x, hp31_y0, hp31_y128, hp31_y256]

lemma hp32_y0 : sum_y_128 32 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp32_y128 : sum_y_128 32 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp32_y256 : sum_y_firstorder 32 256 3 8 = 0 := by solve_sum
lemma eval_x_32 : eval_x 32 = 0 := by
  rw [eval_x, hp32_y0, hp32_y128, hp32_y256]

lemma hp33_y0 : sum_y_128 33 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp33_y128 : sum_y_128 33 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp33_y256 : sum_y_firstorder 33 256 3 8 = 0 := by solve_sum
lemma eval_x_33 : eval_x 33 = 0 := by
  rw [eval_x, hp33_y0, hp33_y128, hp33_y256]

lemma hp34_y0 : sum_y_128 34 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp34_y128 : sum_y_128 34 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp34_y256 : sum_y_firstorder 34 256 3 8 = 0 := by solve_sum
lemma eval_x_34 : eval_x 34 = 0 := by
  rw [eval_x, hp34_y0, hp34_y128, hp34_y256]

lemma hp35_y0 : sum_y_128 35 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp35_y128 : sum_y_128 35 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp35_y256 : sum_y_firstorder 35 256 3 8 = 0 := by solve_sum
lemma eval_x_35 : eval_x 35 = 0 := by
  rw [eval_x, hp35_y0, hp35_y128, hp35_y256]

lemma hp36_y0 : sum_y_128 36 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp36_y128 : sum_y_128 36 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp36_y256 : sum_y_firstorder 36 256 3 8 = 0 := by solve_sum
lemma eval_x_36 : eval_x 36 = 0 := by
  rw [eval_x, hp36_y0, hp36_y128, hp36_y256]

lemma hp37_y0 : sum_y_128 37 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp37_y128 : sum_y_128 37 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp37_y256 : sum_y_firstorder 37 256 3 8 = 0 := by solve_sum
lemma eval_x_37 : eval_x 37 = 0 := by
  rw [eval_x, hp37_y0, hp37_y128, hp37_y256]

lemma hp38_y0 : sum_y_128 38 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp38_y128 : sum_y_128 38 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp38_y256 : sum_y_firstorder 38 256 3 8 = 0 := by solve_sum
lemma eval_x_38 : eval_x 38 = 0 := by
  rw [eval_x, hp38_y0, hp38_y128, hp38_y256]

lemma hp39_y0 : sum_y_128 39 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp39_y128 : sum_y_128 39 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp39_y256 : sum_y_firstorder 39 256 3 8 = 0 := by solve_sum
lemma eval_x_39 : eval_x 39 = 0 := by
  rw [eval_x, hp39_y0, hp39_y128, hp39_y256]

lemma hp40_y0 : sum_y_128 40 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp40_y128 : sum_y_128 40 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp40_y256 : sum_y_firstorder 40 256 3 8 = 0 := by solve_sum
lemma eval_x_40 : eval_x 40 = 0 := by
  rw [eval_x, hp40_y0, hp40_y128, hp40_y256]

lemma hp41_y0 : sum_y_128 41 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp41_y128 : sum_y_128 41 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp41_y256 : sum_y_firstorder 41 256 3 8 = 0 := by solve_sum
lemma eval_x_41 : eval_x 41 = 0 := by
  rw [eval_x, hp41_y0, hp41_y128, hp41_y256]

lemma hp42_y0 : sum_y_128 42 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp42_y128 : sum_y_128 42 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp42_y256 : sum_y_firstorder 42 256 3 8 = 0 := by solve_sum
lemma eval_x_42 : eval_x 42 = 0 := by
  rw [eval_x, hp42_y0, hp42_y128, hp42_y256]

lemma hp43_y0 : sum_y_128 43 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp43_y128 : sum_y_128 43 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp43_y256 : sum_y_firstorder 43 256 3 8 = 0 := by solve_sum
lemma eval_x_43 : eval_x 43 = 0 := by
  rw [eval_x, hp43_y0, hp43_y128, hp43_y256]

lemma hp44_y0 : sum_y_128 44 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp44_y128 : sum_y_128 44 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp44_y256 : sum_y_firstorder 44 256 3 8 = 0 := by solve_sum
lemma eval_x_44 : eval_x 44 = 0 := by
  rw [eval_x, hp44_y0, hp44_y128, hp44_y256]

lemma hp45_y0 : sum_y_128 45 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp45_y128 : sum_y_128 45 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp45_y256 : sum_y_firstorder 45 256 3 8 = 0 := by solve_sum
lemma eval_x_45 : eval_x 45 = 0 := by
  rw [eval_x, hp45_y0, hp45_y128, hp45_y256]

lemma hp46_y0 : sum_y_128 46 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp46_y128 : sum_y_128 46 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp46_y256 : sum_y_firstorder 46 256 3 8 = 0 := by solve_sum
lemma eval_x_46 : eval_x 46 = 0 := by
  rw [eval_x, hp46_y0, hp46_y128, hp46_y256]

lemma hp47_y0 : sum_y_128 47 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp47_y128 : sum_y_128 47 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp47_y256 : sum_y_firstorder 47 256 3 8 = 0 := by solve_sum
lemma eval_x_47 : eval_x 47 = 0 := by
  rw [eval_x, hp47_y0, hp47_y128, hp47_y256]

lemma hp48_y0 : sum_y_128 48 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp48_y128 : sum_y_128 48 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp48_y256 : sum_y_firstorder 48 256 3 8 = 0 := by solve_sum
lemma eval_x_48 : eval_x 48 = 0 := by
  rw [eval_x, hp48_y0, hp48_y128, hp48_y256]

lemma hp49_y0 : sum_y_128 49 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp49_y128 : sum_y_128 49 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp49_y256 : sum_y_firstorder 49 256 3 8 = 0 := by solve_sum
lemma eval_x_49 : eval_x 49 = 0 := by
  rw [eval_x, hp49_y0, hp49_y128, hp49_y256]

lemma hp50_y0 : sum_y_128 50 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp50_y128 : sum_y_128 50 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp50_y256 : sum_y_firstorder 50 256 3 8 = 0 := by solve_sum
lemma eval_x_50 : eval_x 50 = 0 := by
  rw [eval_x, hp50_y0, hp50_y128, hp50_y256]

lemma hp51_y0 : sum_y_128 51 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp51_y128 : sum_y_128 51 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp51_y256 : sum_y_firstorder 51 256 3 8 = 0 := by solve_sum
lemma eval_x_51 : eval_x 51 = 0 := by
  rw [eval_x, hp51_y0, hp51_y128, hp51_y256]

lemma hp52_y0 : sum_y_128 52 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp52_y128 : sum_y_128 52 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp52_y256 : sum_y_firstorder 52 256 3 8 = 0 := by solve_sum
lemma eval_x_52 : eval_x 52 = 0 := by
  rw [eval_x, hp52_y0, hp52_y128, hp52_y256]

lemma hp53_y0 : sum_y_128 53 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp53_y128 : sum_y_128 53 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp53_y256 : sum_y_firstorder 53 256 3 8 = 0 := by solve_sum
lemma eval_x_53 : eval_x 53 = 0 := by
  rw [eval_x, hp53_y0, hp53_y128, hp53_y256]

lemma hp54_y0 : sum_y_128 54 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp54_y128 : sum_y_128 54 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp54_y256 : sum_y_firstorder 54 256 3 8 = 0 := by solve_sum
lemma eval_x_54 : eval_x 54 = 0 := by
  rw [eval_x, hp54_y0, hp54_y128, hp54_y256]

lemma hp55_y0 : sum_y_128 55 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp55_y128 : sum_y_128 55 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp55_y256 : sum_y_firstorder 55 256 3 8 = 0 := by solve_sum
lemma eval_x_55 : eval_x 55 = 0 := by
  rw [eval_x, hp55_y0, hp55_y128, hp55_y256]

lemma hp56_y0 : sum_y_128 56 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp56_y128 : sum_y_128 56 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp56_y256 : sum_y_firstorder 56 256 3 8 = 0 := by solve_sum
lemma eval_x_56 : eval_x 56 = 0 := by
  rw [eval_x, hp56_y0, hp56_y128, hp56_y256]

lemma hp57_y0 : sum_y_128 57 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp57_y128 : sum_y_128 57 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp57_y256 : sum_y_firstorder 57 256 3 8 = 0 := by solve_sum
lemma eval_x_57 : eval_x 57 = 0 := by
  rw [eval_x, hp57_y0, hp57_y128, hp57_y256]

lemma hp58_y0 : sum_y_128 58 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp58_y128 : sum_y_128 58 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp58_y256 : sum_y_firstorder 58 256 3 8 = 0 := by solve_sum
lemma eval_x_58 : eval_x 58 = 0 := by
  rw [eval_x, hp58_y0, hp58_y128, hp58_y256]

lemma hp59_y0 : sum_y_128 59 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp59_y128 : sum_y_128 59 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp59_y256 : sum_y_firstorder 59 256 3 8 = 0 := by solve_sum
lemma eval_x_59 : eval_x 59 = 0 := by
  rw [eval_x, hp59_y0, hp59_y128, hp59_y256]

lemma hp60_y0 : sum_y_128 60 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp60_y128 : sum_y_128 60 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp60_y256 : sum_y_firstorder 60 256 3 8 = 0 := by solve_sum
lemma eval_x_60 : eval_x 60 = 0 := by
  rw [eval_x, hp60_y0, hp60_y128, hp60_y256]

lemma hp61_y0 : sum_y_128 61 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp61_y128 : sum_y_128 61 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp61_y256 : sum_y_firstorder 61 256 3 8 = 0 := by solve_sum
lemma eval_x_61 : eval_x 61 = 0 := by
  rw [eval_x, hp61_y0, hp61_y128, hp61_y256]

lemma hp62_y0 : sum_y_128 62 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp62_y128 : sum_y_128 62 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp62_y256 : sum_y_firstorder 62 256 3 8 = 0 := by solve_sum
lemma eval_x_62 : eval_x 62 = 0 := by
  rw [eval_x, hp62_y0, hp62_y128, hp62_y256]

lemma hp63_y0 : sum_y_128 63 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp63_y128 : sum_y_128 63 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp63_y256 : sum_y_firstorder 63 256 3 8 = 0 := by solve_sum
lemma eval_x_63 : eval_x 63 = 0 := by
  rw [eval_x, hp63_y0, hp63_y128, hp63_y256]

lemma hp64_y0 : sum_y_128 64 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp64_y128 : sum_y_128 64 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp64_y256 : sum_y_firstorder 64 256 3 8 = 0 := by solve_sum
lemma eval_x_64 : eval_x 64 = 0 := by
  rw [eval_x, hp64_y0, hp64_y128, hp64_y256]

lemma hp65_y0 : sum_y_128 65 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp65_y128 : sum_y_128 65 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp65_y256 : sum_y_firstorder 65 256 3 8 = 0 := by solve_sum
lemma eval_x_65 : eval_x 65 = 0 := by
  rw [eval_x, hp65_y0, hp65_y128, hp65_y256]

lemma hp66_y0 : sum_y_128 66 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp66_y128 : sum_y_128 66 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp66_y256 : sum_y_firstorder 66 256 3 8 = 0 := by solve_sum
lemma eval_x_66 : eval_x 66 = 0 := by
  rw [eval_x, hp66_y0, hp66_y128, hp66_y256]

lemma hp67_y0 : sum_y_128 67 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp67_y128 : sum_y_128 67 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp67_y256 : sum_y_firstorder 67 256 3 8 = 0 := by solve_sum
lemma eval_x_67 : eval_x 67 = 0 := by
  rw [eval_x, hp67_y0, hp67_y128, hp67_y256]

lemma hp68_y0 : sum_y_128 68 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp68_y128 : sum_y_128 68 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp68_y256 : sum_y_firstorder 68 256 3 8 = 0 := by solve_sum
lemma eval_x_68 : eval_x 68 = 0 := by
  rw [eval_x, hp68_y0, hp68_y128, hp68_y256]

lemma hp69_y0 : sum_y_128 69 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp69_y128 : sum_y_128 69 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp69_y256 : sum_y_firstorder 69 256 3 8 = 0 := by solve_sum
lemma eval_x_69 : eval_x 69 = 0 := by
  rw [eval_x, hp69_y0, hp69_y128, hp69_y256]

lemma hp70_y0 : sum_y_128 70 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp70_y128 : sum_y_128 70 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp70_y256 : sum_y_firstorder 70 256 3 8 = 0 := by solve_sum
lemma eval_x_70 : eval_x 70 = 0 := by
  rw [eval_x, hp70_y0, hp70_y128, hp70_y256]

lemma hp71_y0 : sum_y_128 71 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp71_y128 : sum_y_128 71 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp71_y256 : sum_y_firstorder 71 256 3 8 = 0 := by solve_sum
lemma eval_x_71 : eval_x 71 = 0 := by
  rw [eval_x, hp71_y0, hp71_y128, hp71_y256]

lemma hp72_y0 : sum_y_128 72 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp72_y128 : sum_y_128 72 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp72_y256 : sum_y_firstorder 72 256 3 8 = 0 := by solve_sum
lemma eval_x_72 : eval_x 72 = 0 := by
  rw [eval_x, hp72_y0, hp72_y128, hp72_y256]

lemma hp73_y0 : sum_y_128 73 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp73_y128 : sum_y_128 73 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp73_y256 : sum_y_firstorder 73 256 3 8 = 0 := by solve_sum
lemma eval_x_73 : eval_x 73 = 0 := by
  rw [eval_x, hp73_y0, hp73_y128, hp73_y256]

lemma hp74_y0 : sum_y_128 74 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp74_y128 : sum_y_128 74 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp74_y256 : sum_y_firstorder 74 256 3 8 = 0 := by solve_sum
lemma eval_x_74 : eval_x 74 = 0 := by
  rw [eval_x, hp74_y0, hp74_y128, hp74_y256]

lemma hp75_y0 : sum_y_128 75 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp75_y128 : sum_y_128 75 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp75_y256 : sum_y_firstorder 75 256 3 8 = 0 := by solve_sum
lemma eval_x_75 : eval_x 75 = 0 := by
  rw [eval_x, hp75_y0, hp75_y128, hp75_y256]

lemma hp76_y0 : sum_y_128 76 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp76_y128 : sum_y_128 76 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp76_y256 : sum_y_firstorder 76 256 3 8 = 0 := by solve_sum
lemma eval_x_76 : eval_x 76 = 0 := by
  rw [eval_x, hp76_y0, hp76_y128, hp76_y256]

lemma hp77_y0 : sum_y_128 77 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp77_y128 : sum_y_128 77 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp77_y256 : sum_y_firstorder 77 256 3 8 = 0 := by solve_sum
lemma eval_x_77 : eval_x 77 = 0 := by
  rw [eval_x, hp77_y0, hp77_y128, hp77_y256]

lemma hp78_y0 : sum_y_128 78 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp78_y128 : sum_y_128 78 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp78_y256 : sum_y_firstorder 78 256 3 8 = 0 := by solve_sum
lemma eval_x_78 : eval_x 78 = 0 := by
  rw [eval_x, hp78_y0, hp78_y128, hp78_y256]

lemma hp79_y0 : sum_y_128 79 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp79_y128 : sum_y_128 79 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp79_y256 : sum_y_firstorder 79 256 3 8 = 0 := by solve_sum
lemma eval_x_79 : eval_x 79 = 0 := by
  rw [eval_x, hp79_y0, hp79_y128, hp79_y256]

lemma hp80_y0 : sum_y_128 80 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp80_y128 : sum_y_128 80 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp80_y256 : sum_y_firstorder 80 256 3 8 = 0 := by solve_sum
lemma eval_x_80 : eval_x 80 = 0 := by
  rw [eval_x, hp80_y0, hp80_y128, hp80_y256]

lemma hp81_y0 : sum_y_128 81 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp81_y128 : sum_y_128 81 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp81_y256 : sum_y_firstorder 81 256 3 8 = 0 := by solve_sum
lemma eval_x_81 : eval_x 81 = 0 := by
  rw [eval_x, hp81_y0, hp81_y128, hp81_y256]

lemma hp82_y0 : sum_y_128 82 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp82_y128 : sum_y_128 82 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp82_y256 : sum_y_firstorder 82 256 3 8 = 0 := by solve_sum
lemma eval_x_82 : eval_x 82 = 0 := by
  rw [eval_x, hp82_y0, hp82_y128, hp82_y256]

lemma hp83_y0 : sum_y_128 83 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp83_y128 : sum_y_128 83 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp83_y256 : sum_y_firstorder 83 256 3 8 = 0 := by solve_sum
lemma eval_x_83 : eval_x 83 = 0 := by
  rw [eval_x, hp83_y0, hp83_y128, hp83_y256]

lemma hp84_y0 : sum_y_128 84 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp84_y128 : sum_y_128 84 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp84_y256 : sum_y_firstorder 84 256 3 8 = 0 := by solve_sum
lemma eval_x_84 : eval_x 84 = 0 := by
  rw [eval_x, hp84_y0, hp84_y128, hp84_y256]

lemma hp85_y0 : sum_y_128 85 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp85_y128 : sum_y_128 85 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp85_y256 : sum_y_firstorder 85 256 3 8 = 0 := by solve_sum
lemma eval_x_85 : eval_x 85 = 0 := by
  rw [eval_x, hp85_y0, hp85_y128, hp85_y256]

lemma hp86_y0 : sum_y_128 86 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp86_y128 : sum_y_128 86 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp86_y256 : sum_y_firstorder 86 256 3 8 = 0 := by solve_sum
lemma eval_x_86 : eval_x 86 = 0 := by
  rw [eval_x, hp86_y0, hp86_y128, hp86_y256]

lemma hp87_y0 : sum_y_128 87 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp87_y128 : sum_y_128 87 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp87_y256 : sum_y_firstorder 87 256 3 8 = 0 := by solve_sum
lemma eval_x_87 : eval_x 87 = 0 := by
  rw [eval_x, hp87_y0, hp87_y128, hp87_y256]

lemma hp88_y0 : sum_y_128 88 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp88_y128 : sum_y_128 88 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp88_y256 : sum_y_firstorder 88 256 3 8 = 0 := by solve_sum
lemma eval_x_88 : eval_x 88 = 0 := by
  rw [eval_x, hp88_y0, hp88_y128, hp88_y256]

lemma hp89_y0 : sum_y_128 89 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp89_y128 : sum_y_128 89 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp89_y256 : sum_y_firstorder 89 256 3 8 = 0 := by solve_sum
lemma eval_x_89 : eval_x 89 = 0 := by
  rw [eval_x, hp89_y0, hp89_y128, hp89_y256]

lemma hp90_y0 : sum_y_128 90 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp90_y128 : sum_y_128 90 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp90_y256 : sum_y_firstorder 90 256 3 8 = 0 := by solve_sum
lemma eval_x_90 : eval_x 90 = 0 := by
  rw [eval_x, hp90_y0, hp90_y128, hp90_y256]

lemma hp91_y0 : sum_y_128 91 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp91_y128 : sum_y_128 91 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp91_y256 : sum_y_firstorder 91 256 3 8 = 0 := by solve_sum
lemma eval_x_91 : eval_x 91 = 0 := by
  rw [eval_x, hp91_y0, hp91_y128, hp91_y256]

lemma hp92_y0 : sum_y_128 92 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp92_y128 : sum_y_128 92 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp92_y256 : sum_y_firstorder 92 256 3 8 = 0 := by solve_sum
lemma eval_x_92 : eval_x 92 = 0 := by
  rw [eval_x, hp92_y0, hp92_y128, hp92_y256]

lemma hp93_y0 : sum_y_128 93 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp93_y128 : sum_y_128 93 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp93_y256 : sum_y_firstorder 93 256 3 8 = 0 := by solve_sum
lemma eval_x_93 : eval_x 93 = 0 := by
  rw [eval_x, hp93_y0, hp93_y128, hp93_y256]

lemma hp94_y0 : sum_y_128 94 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp94_y128 : sum_y_128 94 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp94_y256 : sum_y_firstorder 94 256 3 8 = 0 := by solve_sum
lemma eval_x_94 : eval_x 94 = 0 := by
  rw [eval_x, hp94_y0, hp94_y128, hp94_y256]

lemma hp95_y0 : sum_y_128 95 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp95_y128 : sum_y_128 95 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp95_y256 : sum_y_firstorder 95 256 3 8 = 0 := by solve_sum
lemma eval_x_95 : eval_x 95 = 0 := by
  rw [eval_x, hp95_y0, hp95_y128, hp95_y256]

lemma hp96_y0 : sum_y_128 96 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp96_y128 : sum_y_128 96 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp96_y256 : sum_y_firstorder 96 256 3 8 = 0 := by solve_sum
lemma eval_x_96 : eval_x 96 = 0 := by
  rw [eval_x, hp96_y0, hp96_y128, hp96_y256]

lemma hp97_y0 : sum_y_128 97 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp97_y128 : sum_y_128 97 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp97_y256 : sum_y_firstorder 97 256 3 8 = 0 := by solve_sum
lemma eval_x_97 : eval_x 97 = 0 := by
  rw [eval_x, hp97_y0, hp97_y128, hp97_y256]

lemma hp98_y0 : sum_y_128 98 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp98_y128 : sum_y_128 98 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp98_y256 : sum_y_firstorder 98 256 3 8 = 0 := by solve_sum
lemma eval_x_98 : eval_x 98 = 0 := by
  rw [eval_x, hp98_y0, hp98_y128, hp98_y256]

lemma hp99_y0 : sum_y_128 99 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp99_y128 : sum_y_128 99 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp99_y256 : sum_y_firstorder 99 256 3 8 = 0 := by solve_sum
lemma eval_x_99 : eval_x 99 = 0 := by
  rw [eval_x, hp99_y0, hp99_y128, hp99_y256]

lemma hp100_y0 : sum_y_128 100 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp100_y128 : sum_y_128 100 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp100_y256 : sum_y_firstorder 100 256 3 8 = 0 := by solve_sum
lemma eval_x_100 : eval_x 100 = 0 := by
  rw [eval_x, hp100_y0, hp100_y128, hp100_y256]

lemma hp101_y0 : sum_y_128 101 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp101_y128 : sum_y_128 101 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp101_y256 : sum_y_firstorder 101 256 3 8 = 0 := by solve_sum
lemma eval_x_101 : eval_x 101 = 0 := by
  rw [eval_x, hp101_y0, hp101_y128, hp101_y256]

lemma hp102_y0 : sum_y_128 102 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp102_y128 : sum_y_128 102 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp102_y256 : sum_y_firstorder 102 256 3 8 = 0 := by solve_sum
lemma eval_x_102 : eval_x 102 = 0 := by
  rw [eval_x, hp102_y0, hp102_y128, hp102_y256]

lemma hp103_y0 : sum_y_128 103 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp103_y128 : sum_y_128 103 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp103_y256 : sum_y_firstorder 103 256 3 8 = 0 := by solve_sum
lemma eval_x_103 : eval_x 103 = 0 := by
  rw [eval_x, hp103_y0, hp103_y128, hp103_y256]

lemma hp104_y0 : sum_y_128 104 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp104_y128 : sum_y_128 104 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp104_y256 : sum_y_firstorder 104 256 3 8 = 0 := by solve_sum
lemma eval_x_104 : eval_x 104 = 0 := by
  rw [eval_x, hp104_y0, hp104_y128, hp104_y256]

lemma hp105_y0 : sum_y_128 105 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp105_y128 : sum_y_128 105 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp105_y256 : sum_y_firstorder 105 256 3 8 = 0 := by solve_sum
lemma eval_x_105 : eval_x 105 = 0 := by
  rw [eval_x, hp105_y0, hp105_y128, hp105_y256]

lemma hp106_y0 : sum_y_128 106 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp106_y128 : sum_y_128 106 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp106_y256 : sum_y_firstorder 106 256 3 8 = 0 := by solve_sum
lemma eval_x_106 : eval_x 106 = 0 := by
  rw [eval_x, hp106_y0, hp106_y128, hp106_y256]

lemma hp107_y0 : sum_y_128 107 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp107_y128 : sum_y_128 107 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp107_y256 : sum_y_firstorder 107 256 3 8 = 0 := by solve_sum
lemma eval_x_107 : eval_x 107 = 0 := by
  rw [eval_x, hp107_y0, hp107_y128, hp107_y256]

lemma hp108_y0 : sum_y_128 108 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp108_y128 : sum_y_128 108 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp108_y256 : sum_y_firstorder 108 256 3 8 = 0 := by solve_sum
lemma eval_x_108 : eval_x 108 = 0 := by
  rw [eval_x, hp108_y0, hp108_y128, hp108_y256]

lemma hp109_y0 : sum_y_128 109 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp109_y128 : sum_y_128 109 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp109_y256 : sum_y_firstorder 109 256 3 8 = 0 := by solve_sum
lemma eval_x_109 : eval_x 109 = 0 := by
  rw [eval_x, hp109_y0, hp109_y128, hp109_y256]

lemma hp110_y0 : sum_y_128 110 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp110_y128 : sum_y_128 110 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp110_y256 : sum_y_firstorder 110 256 3 8 = 0 := by solve_sum
lemma eval_x_110 : eval_x 110 = 0 := by
  rw [eval_x, hp110_y0, hp110_y128, hp110_y256]

lemma hp111_y0 : sum_y_128 111 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp111_y128 : sum_y_128 111 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp111_y256 : sum_y_firstorder 111 256 3 8 = 0 := by solve_sum
lemma eval_x_111 : eval_x 111 = 0 := by
  rw [eval_x, hp111_y0, hp111_y128, hp111_y256]

lemma hp112_y0 : sum_y_128 112 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp112_y128 : sum_y_128 112 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp112_y256 : sum_y_firstorder 112 256 3 8 = 0 := by solve_sum
lemma eval_x_112 : eval_x 112 = 0 := by
  rw [eval_x, hp112_y0, hp112_y128, hp112_y256]

lemma hp113_y0 : sum_y_128 113 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp113_y128 : sum_y_128 113 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp113_y256 : sum_y_firstorder 113 256 3 8 = 0 := by solve_sum
lemma eval_x_113 : eval_x 113 = 0 := by
  rw [eval_x, hp113_y0, hp113_y128, hp113_y256]

lemma hp114_y0 : sum_y_128 114 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp114_y128 : sum_y_128 114 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp114_y256 : sum_y_firstorder 114 256 3 8 = 0 := by solve_sum
lemma eval_x_114 : eval_x 114 = 0 := by
  rw [eval_x, hp114_y0, hp114_y128, hp114_y256]

lemma hp115_y0 : sum_y_128 115 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp115_y128 : sum_y_128 115 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp115_y256 : sum_y_firstorder 115 256 3 8 = 0 := by solve_sum
lemma eval_x_115 : eval_x 115 = 0 := by
  rw [eval_x, hp115_y0, hp115_y128, hp115_y256]

lemma hp116_y0 : sum_y_128 116 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp116_y128 : sum_y_128 116 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp116_y256 : sum_y_firstorder 116 256 3 8 = 0 := by solve_sum
lemma eval_x_116 : eval_x 116 = 0 := by
  rw [eval_x, hp116_y0, hp116_y128, hp116_y256]

lemma hp117_y0 : sum_y_128 117 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp117_y128 : sum_y_128 117 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp117_y256 : sum_y_firstorder 117 256 3 8 = 0 := by solve_sum
lemma eval_x_117 : eval_x 117 = 0 := by
  rw [eval_x, hp117_y0, hp117_y128, hp117_y256]

lemma hp118_y0 : sum_y_128 118 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp118_y128 : sum_y_128 118 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp118_y256 : sum_y_firstorder 118 256 3 8 = 0 := by solve_sum
lemma eval_x_118 : eval_x 118 = 0 := by
  rw [eval_x, hp118_y0, hp118_y128, hp118_y256]

lemma hp119_y0 : sum_y_128 119 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp119_y128 : sum_y_128 119 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp119_y256 : sum_y_firstorder 119 256 3 8 = 0 := by solve_sum
lemma eval_x_119 : eval_x 119 = 0 := by
  rw [eval_x, hp119_y0, hp119_y128, hp119_y256]

lemma hp120_y0 : sum_y_128 120 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp120_y128 : sum_y_128 120 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp120_y256 : sum_y_firstorder 120 256 3 8 = 0 := by solve_sum
lemma eval_x_120 : eval_x 120 = 0 := by
  rw [eval_x, hp120_y0, hp120_y128, hp120_y256]

lemma hp121_y0 : sum_y_128 121 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp121_y128 : sum_y_128 121 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp121_y256 : sum_y_firstorder 121 256 3 8 = 0 := by solve_sum
lemma eval_x_121 : eval_x 121 = 0 := by
  rw [eval_x, hp121_y0, hp121_y128, hp121_y256]

lemma hp122_y0 : sum_y_128 122 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp122_y128 : sum_y_128 122 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp122_y256 : sum_y_firstorder 122 256 3 8 = 0 := by solve_sum
lemma eval_x_122 : eval_x 122 = 0 := by
  rw [eval_x, hp122_y0, hp122_y128, hp122_y256]

lemma hp123_y0 : sum_y_128 123 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp123_y128 : sum_y_128 123 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp123_y256 : sum_y_firstorder 123 256 3 8 = 0 := by solve_sum
lemma eval_x_123 : eval_x 123 = 0 := by
  rw [eval_x, hp123_y0, hp123_y128, hp123_y256]

lemma hp124_y0 : sum_y_128 124 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp124_y128 : sum_y_128 124 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp124_y256 : sum_y_firstorder 124 256 3 8 = 0 := by solve_sum
lemma eval_x_124 : eval_x 124 = 0 := by
  rw [eval_x, hp124_y0, hp124_y128, hp124_y256]

lemma hp125_y0 : sum_y_128 125 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp125_y128 : sum_y_128 125 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp125_y256 : sum_y_firstorder 125 256 3 8 = 0 := by solve_sum
lemma eval_x_125 : eval_x 125 = 0 := by
  rw [eval_x, hp125_y0, hp125_y128, hp125_y256]

lemma hp126_y0 : sum_y_128 126 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp126_y128 : sum_y_128 126 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp126_y256 : sum_y_firstorder 126 256 3 8 = 0 := by solve_sum
lemma eval_x_126 : eval_x 126 = 0 := by
  rw [eval_x, hp126_y0, hp126_y128, hp126_y256]

lemma hp127_y0 : sum_y_128 127 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp127_y128 : sum_y_128 127 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp127_y256 : sum_y_firstorder 127 256 3 8 = 0 := by solve_sum
lemma eval_x_127 : eval_x 127 = 0 := by
  rw [eval_x, hp127_y0, hp127_y128, hp127_y256]

lemma hp128_y0 : sum_y_128 128 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp128_y128 : sum_y_128 128 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp128_y256 : sum_y_firstorder 128 256 3 8 = 0 := by solve_sum
lemma eval_x_128 : eval_x 128 = 0 := by
  rw [eval_x, hp128_y0, hp128_y128, hp128_y256]

lemma hp129_y0 : sum_y_128 129 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp129_y128 : sum_y_128 129 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp129_y256 : sum_y_firstorder 129 256 3 8 = 0 := by solve_sum
lemma eval_x_129 : eval_x 129 = 0 := by
  rw [eval_x, hp129_y0, hp129_y128, hp129_y256]

lemma hp130_y0 : sum_y_128 130 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp130_y128 : sum_y_128 130 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp130_y256 : sum_y_firstorder 130 256 3 8 = 0 := by solve_sum
lemma eval_x_130 : eval_x 130 = 0 := by
  rw [eval_x, hp130_y0, hp130_y128, hp130_y256]

lemma hp131_y0 : sum_y_128 131 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp131_y128 : sum_y_128 131 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp131_y256 : sum_y_firstorder 131 256 3 8 = 0 := by solve_sum
lemma eval_x_131 : eval_x 131 = 0 := by
  rw [eval_x, hp131_y0, hp131_y128, hp131_y256]

lemma hp132_y0 : sum_y_128 132 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp132_y128 : sum_y_128 132 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp132_y256 : sum_y_firstorder 132 256 3 8 = 0 := by solve_sum
lemma eval_x_132 : eval_x 132 = 0 := by
  rw [eval_x, hp132_y0, hp132_y128, hp132_y256]

lemma hp133_y0 : sum_y_128 133 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp133_y128 : sum_y_128 133 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp133_y256 : sum_y_firstorder 133 256 3 8 = 0 := by solve_sum
lemma eval_x_133 : eval_x 133 = 0 := by
  rw [eval_x, hp133_y0, hp133_y128, hp133_y256]

lemma hp134_y0 : sum_y_128 134 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp134_y128 : sum_y_128 134 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp134_y256 : sum_y_firstorder 134 256 3 8 = 0 := by solve_sum
lemma eval_x_134 : eval_x 134 = 0 := by
  rw [eval_x, hp134_y0, hp134_y128, hp134_y256]

lemma hp135_y0 : sum_y_128 135 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp135_y128 : sum_y_128 135 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp135_y256 : sum_y_firstorder 135 256 3 8 = 0 := by solve_sum
lemma eval_x_135 : eval_x 135 = 0 := by
  rw [eval_x, hp135_y0, hp135_y128, hp135_y256]

lemma hp136_y0 : sum_y_128 136 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp136_y128 : sum_y_128 136 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp136_y256 : sum_y_firstorder 136 256 3 8 = 0 := by solve_sum
lemma eval_x_136 : eval_x 136 = 0 := by
  rw [eval_x, hp136_y0, hp136_y128, hp136_y256]

lemma hp137_y0 : sum_y_128 137 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp137_y128 : sum_y_128 137 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp137_y256 : sum_y_firstorder 137 256 3 8 = 0 := by solve_sum
lemma eval_x_137 : eval_x 137 = 0 := by
  rw [eval_x, hp137_y0, hp137_y128, hp137_y256]

lemma hp138_y0 : sum_y_128 138 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp138_y128 : sum_y_128 138 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp138_y256 : sum_y_firstorder 138 256 3 8 = 0 := by solve_sum
lemma eval_x_138 : eval_x 138 = 0 := by
  rw [eval_x, hp138_y0, hp138_y128, hp138_y256]

lemma hp139_y0 : sum_y_128 139 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp139_y128 : sum_y_128 139 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp139_y256 : sum_y_firstorder 139 256 3 8 = 0 := by solve_sum
lemma eval_x_139 : eval_x 139 = 0 := by
  rw [eval_x, hp139_y0, hp139_y128, hp139_y256]

lemma hp140_y0 : sum_y_128 140 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp140_y128 : sum_y_128 140 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp140_y256 : sum_y_firstorder 140 256 3 8 = 0 := by solve_sum
lemma eval_x_140 : eval_x 140 = 0 := by
  rw [eval_x, hp140_y0, hp140_y128, hp140_y256]

lemma hp141_y0 : sum_y_128 141 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp141_y128 : sum_y_128 141 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp141_y256 : sum_y_firstorder 141 256 3 8 = 0 := by solve_sum
lemma eval_x_141 : eval_x 141 = 0 := by
  rw [eval_x, hp141_y0, hp141_y128, hp141_y256]

lemma hp142_y0 : sum_y_128 142 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp142_y128 : sum_y_128 142 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp142_y256 : sum_y_firstorder 142 256 3 8 = 0 := by solve_sum
lemma eval_x_142 : eval_x 142 = 0 := by
  rw [eval_x, hp142_y0, hp142_y128, hp142_y256]

lemma hp143_y0 : sum_y_128 143 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp143_y128 : sum_y_128 143 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp143_y256 : sum_y_firstorder 143 256 3 8 = 0 := by solve_sum
lemma eval_x_143 : eval_x 143 = 0 := by
  rw [eval_x, hp143_y0, hp143_y128, hp143_y256]

lemma hp144_y0 : sum_y_128 144 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp144_y128 : sum_y_128 144 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp144_y256 : sum_y_firstorder 144 256 3 8 = 0 := by solve_sum
lemma eval_x_144 : eval_x 144 = 0 := by
  rw [eval_x, hp144_y0, hp144_y128, hp144_y256]

lemma hp145_y0 : sum_y_128 145 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp145_y128 : sum_y_128 145 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp145_y256 : sum_y_firstorder 145 256 3 8 = 0 := by solve_sum
lemma eval_x_145 : eval_x 145 = 0 := by
  rw [eval_x, hp145_y0, hp145_y128, hp145_y256]

lemma hp146_y0 : sum_y_128 146 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp146_y128 : sum_y_128 146 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp146_y256 : sum_y_firstorder 146 256 3 8 = 0 := by solve_sum
lemma eval_x_146 : eval_x 146 = 0 := by
  rw [eval_x, hp146_y0, hp146_y128, hp146_y256]

lemma hp147_y0 : sum_y_128 147 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp147_y128 : sum_y_128 147 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp147_y256 : sum_y_firstorder 147 256 3 8 = 0 := by solve_sum
lemma eval_x_147 : eval_x 147 = 0 := by
  rw [eval_x, hp147_y0, hp147_y128, hp147_y256]

lemma hp148_y0 : sum_y_128 148 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp148_y128 : sum_y_128 148 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp148_y256 : sum_y_firstorder 148 256 3 8 = 0 := by solve_sum
lemma eval_x_148 : eval_x 148 = 0 := by
  rw [eval_x, hp148_y0, hp148_y128, hp148_y256]

lemma hp149_y0 : sum_y_128 149 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp149_y128 : sum_y_128 149 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp149_y256 : sum_y_firstorder 149 256 3 8 = 0 := by solve_sum
lemma eval_x_149 : eval_x 149 = 0 := by
  rw [eval_x, hp149_y0, hp149_y128, hp149_y256]

lemma hp150_y0 : sum_y_128 150 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp150_y128 : sum_y_128 150 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp150_y256 : sum_y_firstorder 150 256 3 8 = 0 := by solve_sum
lemma eval_x_150 : eval_x 150 = 0 := by
  rw [eval_x, hp150_y0, hp150_y128, hp150_y256]

lemma hp151_y0 : sum_y_128 151 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp151_y128 : sum_y_128 151 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp151_y256 : sum_y_firstorder 151 256 3 8 = 0 := by solve_sum
lemma eval_x_151 : eval_x 151 = 0 := by
  rw [eval_x, hp151_y0, hp151_y128, hp151_y256]

lemma hp152_y0 : sum_y_128 152 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp152_y128 : sum_y_128 152 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp152_y256 : sum_y_firstorder 152 256 3 8 = 0 := by solve_sum
lemma eval_x_152 : eval_x 152 = 0 := by
  rw [eval_x, hp152_y0, hp152_y128, hp152_y256]

lemma hp153_y0 : sum_y_128 153 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp153_y128 : sum_y_128 153 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp153_y256 : sum_y_firstorder 153 256 3 8 = 0 := by solve_sum
lemma eval_x_153 : eval_x 153 = 0 := by
  rw [eval_x, hp153_y0, hp153_y128, hp153_y256]

lemma hp154_y0 : sum_y_128 154 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp154_y128 : sum_y_128 154 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp154_y256 : sum_y_firstorder 154 256 3 8 = 0 := by solve_sum
lemma eval_x_154 : eval_x 154 = 0 := by
  rw [eval_x, hp154_y0, hp154_y128, hp154_y256]

lemma hp155_y0 : sum_y_128 155 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp155_y128 : sum_y_128 155 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp155_y256 : sum_y_firstorder 155 256 3 8 = 0 := by solve_sum
lemma eval_x_155 : eval_x 155 = 0 := by
  rw [eval_x, hp155_y0, hp155_y128, hp155_y256]

lemma hp156_y0 : sum_y_128 156 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp156_y128 : sum_y_128 156 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp156_y256 : sum_y_firstorder 156 256 3 8 = 0 := by solve_sum
lemma eval_x_156 : eval_x 156 = 0 := by
  rw [eval_x, hp156_y0, hp156_y128, hp156_y256]

lemma hp157_y0 : sum_y_128 157 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp157_y128 : sum_y_128 157 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp157_y256 : sum_y_firstorder 157 256 3 8 = 0 := by solve_sum
lemma eval_x_157 : eval_x 157 = 0 := by
  rw [eval_x, hp157_y0, hp157_y128, hp157_y256]

lemma hp158_y0 : sum_y_128 158 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp158_y128 : sum_y_128 158 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp158_y256 : sum_y_firstorder 158 256 3 8 = 0 := by solve_sum
lemma eval_x_158 : eval_x 158 = 0 := by
  rw [eval_x, hp158_y0, hp158_y128, hp158_y256]

lemma hp159_y0 : sum_y_128 159 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp159_y128 : sum_y_128 159 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp159_y256 : sum_y_firstorder 159 256 3 8 = 0 := by solve_sum
lemma eval_x_159 : eval_x 159 = 0 := by
  rw [eval_x, hp159_y0, hp159_y128, hp159_y256]

lemma hp160_y0 : sum_y_128 160 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp160_y128 : sum_y_128 160 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp160_y256 : sum_y_firstorder 160 256 3 8 = 0 := by solve_sum
lemma eval_x_160 : eval_x 160 = 0 := by
  rw [eval_x, hp160_y0, hp160_y128, hp160_y256]

lemma hp161_y0 : sum_y_128 161 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp161_y128 : sum_y_128 161 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp161_y256 : sum_y_firstorder 161 256 3 8 = 0 := by solve_sum
lemma eval_x_161 : eval_x 161 = 0 := by
  rw [eval_x, hp161_y0, hp161_y128, hp161_y256]

lemma hp162_y0 : sum_y_128 162 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp162_y128 : sum_y_128 162 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp162_y256 : sum_y_firstorder 162 256 3 8 = 0 := by solve_sum
lemma eval_x_162 : eval_x 162 = 0 := by
  rw [eval_x, hp162_y0, hp162_y128, hp162_y256]

lemma hp163_y0 : sum_y_128 163 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp163_y128 : sum_y_128 163 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp163_y256 : sum_y_firstorder 163 256 3 8 = 0 := by solve_sum
lemma eval_x_163 : eval_x 163 = 0 := by
  rw [eval_x, hp163_y0, hp163_y128, hp163_y256]

lemma hp164_y0 : sum_y_128 164 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp164_y128 : sum_y_128 164 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp164_y256 : sum_y_firstorder 164 256 3 8 = 0 := by solve_sum
lemma eval_x_164 : eval_x 164 = 0 := by
  rw [eval_x, hp164_y0, hp164_y128, hp164_y256]

lemma hp165_y0 : sum_y_128 165 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp165_y128 : sum_y_128 165 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp165_y256 : sum_y_firstorder 165 256 3 8 = 0 := by solve_sum
lemma eval_x_165 : eval_x 165 = 0 := by
  rw [eval_x, hp165_y0, hp165_y128, hp165_y256]

lemma hp166_y0 : sum_y_128 166 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp166_y128 : sum_y_128 166 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp166_y256 : sum_y_firstorder 166 256 3 8 = 0 := by solve_sum
lemma eval_x_166 : eval_x 166 = 0 := by
  rw [eval_x, hp166_y0, hp166_y128, hp166_y256]

lemma hp167_y0 : sum_y_128 167 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp167_y128 : sum_y_128 167 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp167_y256 : sum_y_firstorder 167 256 3 8 = 0 := by solve_sum
lemma eval_x_167 : eval_x 167 = 0 := by
  rw [eval_x, hp167_y0, hp167_y128, hp167_y256]

lemma hp168_y0 : sum_y_128 168 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp168_y128 : sum_y_128 168 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp168_y256 : sum_y_firstorder 168 256 3 8 = 0 := by solve_sum
lemma eval_x_168 : eval_x 168 = 0 := by
  rw [eval_x, hp168_y0, hp168_y128, hp168_y256]

lemma hp169_y0 : sum_y_128 169 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp169_y128 : sum_y_128 169 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp169_y256 : sum_y_firstorder 169 256 3 8 = 0 := by solve_sum
lemma eval_x_169 : eval_x 169 = 0 := by
  rw [eval_x, hp169_y0, hp169_y128, hp169_y256]

lemma hp170_y0 : sum_y_128 170 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp170_y128 : sum_y_128 170 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp170_y256 : sum_y_firstorder 170 256 3 8 = 0 := by solve_sum
lemma eval_x_170 : eval_x 170 = 0 := by
  rw [eval_x, hp170_y0, hp170_y128, hp170_y256]

lemma hp171_y0 : sum_y_128 171 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp171_y128 : sum_y_128 171 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp171_y256 : sum_y_firstorder 171 256 3 8 = 0 := by solve_sum
lemma eval_x_171 : eval_x 171 = 0 := by
  rw [eval_x, hp171_y0, hp171_y128, hp171_y256]

lemma hp172_y0 : sum_y_128 172 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp172_y128 : sum_y_128 172 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp172_y256 : sum_y_firstorder 172 256 3 8 = 0 := by solve_sum
lemma eval_x_172 : eval_x 172 = 0 := by
  rw [eval_x, hp172_y0, hp172_y128, hp172_y256]

lemma hp173_y0 : sum_y_128 173 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp173_y128 : sum_y_128 173 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp173_y256 : sum_y_firstorder 173 256 3 8 = 0 := by solve_sum
lemma eval_x_173 : eval_x 173 = 0 := by
  rw [eval_x, hp173_y0, hp173_y128, hp173_y256]

lemma hp174_y0 : sum_y_128 174 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp174_y128 : sum_y_128 174 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp174_y256 : sum_y_firstorder 174 256 3 8 = 0 := by solve_sum
lemma eval_x_174 : eval_x 174 = 0 := by
  rw [eval_x, hp174_y0, hp174_y128, hp174_y256]

lemma hp175_y0 : sum_y_128 175 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp175_y128 : sum_y_128 175 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp175_y256 : sum_y_firstorder 175 256 3 8 = 0 := by solve_sum
lemma eval_x_175 : eval_x 175 = 0 := by
  rw [eval_x, hp175_y0, hp175_y128, hp175_y256]

lemma hp176_y0 : sum_y_128 176 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp176_y128 : sum_y_128 176 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp176_y256 : sum_y_firstorder 176 256 3 8 = 0 := by solve_sum
lemma eval_x_176 : eval_x 176 = 0 := by
  rw [eval_x, hp176_y0, hp176_y128, hp176_y256]

lemma hp177_y0 : sum_y_128 177 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp177_y128 : sum_y_128 177 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp177_y256 : sum_y_firstorder 177 256 3 8 = 0 := by solve_sum
lemma eval_x_177 : eval_x 177 = 0 := by
  rw [eval_x, hp177_y0, hp177_y128, hp177_y256]

lemma hp178_y0 : sum_y_128 178 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp178_y128 : sum_y_128 178 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp178_y256 : sum_y_firstorder 178 256 3 8 = 0 := by solve_sum
lemma eval_x_178 : eval_x 178 = 0 := by
  rw [eval_x, hp178_y0, hp178_y128, hp178_y256]

lemma hp179_y0 : sum_y_128 179 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp179_y128 : sum_y_128 179 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp179_y256 : sum_y_firstorder 179 256 3 8 = 0 := by solve_sum
lemma eval_x_179 : eval_x 179 = 0 := by
  rw [eval_x, hp179_y0, hp179_y128, hp179_y256]

lemma hp180_y0 : sum_y_128 180 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp180_y128 : sum_y_128 180 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp180_y256 : sum_y_firstorder 180 256 3 8 = 0 := by solve_sum
lemma eval_x_180 : eval_x 180 = 0 := by
  rw [eval_x, hp180_y0, hp180_y128, hp180_y256]

lemma hp181_y0 : sum_y_128 181 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp181_y128 : sum_y_128 181 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp181_y256 : sum_y_firstorder 181 256 3 8 = 0 := by solve_sum
lemma eval_x_181 : eval_x 181 = 0 := by
  rw [eval_x, hp181_y0, hp181_y128, hp181_y256]

lemma hp182_y0 : sum_y_128 182 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp182_y128 : sum_y_128 182 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp182_y256 : sum_y_firstorder 182 256 3 8 = 0 := by solve_sum
lemma eval_x_182 : eval_x 182 = 0 := by
  rw [eval_x, hp182_y0, hp182_y128, hp182_y256]

lemma hp183_y0 : sum_y_128 183 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp183_y128 : sum_y_128 183 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp183_y256 : sum_y_firstorder 183 256 3 8 = 0 := by solve_sum
lemma eval_x_183 : eval_x 183 = 0 := by
  rw [eval_x, hp183_y0, hp183_y128, hp183_y256]

lemma hp184_y0 : sum_y_128 184 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp184_y128 : sum_y_128 184 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp184_y256 : sum_y_firstorder 184 256 3 8 = 0 := by solve_sum
lemma eval_x_184 : eval_x 184 = 0 := by
  rw [eval_x, hp184_y0, hp184_y128, hp184_y256]

lemma hp185_y0 : sum_y_128 185 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp185_y128 : sum_y_128 185 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp185_y256 : sum_y_firstorder 185 256 3 8 = 0 := by solve_sum
lemma eval_x_185 : eval_x 185 = 0 := by
  rw [eval_x, hp185_y0, hp185_y128, hp185_y256]

lemma hp186_y0 : sum_y_128 186 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp186_y128 : sum_y_128 186 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp186_y256 : sum_y_firstorder 186 256 3 8 = 0 := by solve_sum
lemma eval_x_186 : eval_x 186 = 0 := by
  rw [eval_x, hp186_y0, hp186_y128, hp186_y256]

lemma hp187_y0 : sum_y_128 187 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp187_y128 : sum_y_128 187 128 = 1 := by rw [sum_y_128]; solve_sum
lemma hp187_y256 : sum_y_firstorder 187 256 3 8 = 0 := by solve_sum
lemma eval_x_187 : eval_x 187 = 1 := by
  rw [eval_x, hp187_y0, hp187_y128, hp187_y256]

lemma hp188_y0 : sum_y_128 188 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp188_y128 : sum_y_128 188 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp188_y256 : sum_y_firstorder 188 256 3 8 = 0 := by solve_sum
lemma eval_x_188 : eval_x 188 = 0 := by
  rw [eval_x, hp188_y0, hp188_y128, hp188_y256]

lemma hp189_y0 : sum_y_128 189 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp189_y128 : sum_y_128 189 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp189_y256 : sum_y_firstorder 189 256 3 8 = 0 := by solve_sum
lemma eval_x_189 : eval_x 189 = 0 := by
  rw [eval_x, hp189_y0, hp189_y128, hp189_y256]

lemma hp190_y0 : sum_y_128 190 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp190_y128 : sum_y_128 190 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp190_y256 : sum_y_firstorder 190 256 3 8 = 0 := by solve_sum
lemma eval_x_190 : eval_x 190 = 0 := by
  rw [eval_x, hp190_y0, hp190_y128, hp190_y256]

lemma hp191_y0 : sum_y_128 191 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp191_y128 : sum_y_128 191 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp191_y256 : sum_y_firstorder 191 256 3 8 = 0 := by solve_sum
lemma eval_x_191 : eval_x 191 = 0 := by
  rw [eval_x, hp191_y0, hp191_y128, hp191_y256]

lemma hp192_y0 : sum_y_128 192 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp192_y128 : sum_y_128 192 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp192_y256 : sum_y_firstorder 192 256 3 8 = 0 := by solve_sum
lemma eval_x_192 : eval_x 192 = 0 := by
  rw [eval_x, hp192_y0, hp192_y128, hp192_y256]

lemma hp193_y0 : sum_y_128 193 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp193_y128 : sum_y_128 193 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp193_y256 : sum_y_firstorder 193 256 3 8 = 0 := by solve_sum
lemma eval_x_193 : eval_x 193 = 0 := by
  rw [eval_x, hp193_y0, hp193_y128, hp193_y256]

lemma hp194_y0 : sum_y_128 194 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp194_y128 : sum_y_128 194 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp194_y256 : sum_y_firstorder 194 256 3 8 = 0 := by solve_sum
lemma eval_x_194 : eval_x 194 = 0 := by
  rw [eval_x, hp194_y0, hp194_y128, hp194_y256]

lemma hp195_y0 : sum_y_128 195 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp195_y128 : sum_y_128 195 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp195_y256 : sum_y_firstorder 195 256 3 8 = 0 := by solve_sum
lemma eval_x_195 : eval_x 195 = 0 := by
  rw [eval_x, hp195_y0, hp195_y128, hp195_y256]

lemma hp196_y0 : sum_y_128 196 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp196_y128 : sum_y_128 196 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp196_y256 : sum_y_firstorder 196 256 3 8 = 0 := by solve_sum
lemma eval_x_196 : eval_x 196 = 0 := by
  rw [eval_x, hp196_y0, hp196_y128, hp196_y256]

lemma hp197_y0 : sum_y_128 197 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp197_y128 : sum_y_128 197 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp197_y256 : sum_y_firstorder 197 256 3 8 = 0 := by solve_sum
lemma eval_x_197 : eval_x 197 = 0 := by
  rw [eval_x, hp197_y0, hp197_y128, hp197_y256]

lemma hp198_y0 : sum_y_128 198 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp198_y128 : sum_y_128 198 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp198_y256 : sum_y_firstorder 198 256 3 8 = 0 := by solve_sum
lemma eval_x_198 : eval_x 198 = 0 := by
  rw [eval_x, hp198_y0, hp198_y128, hp198_y256]

lemma hp199_y0 : sum_y_128 199 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp199_y128 : sum_y_128 199 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp199_y256 : sum_y_firstorder 199 256 3 8 = 0 := by solve_sum
lemma eval_x_199 : eval_x 199 = 0 := by
  rw [eval_x, hp199_y0, hp199_y128, hp199_y256]

lemma hp200_y0 : sum_y_128 200 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp200_y128 : sum_y_128 200 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp200_y256 : sum_y_firstorder 200 256 3 8 = 0 := by solve_sum
lemma eval_x_200 : eval_x 200 = 0 := by
  rw [eval_x, hp200_y0, hp200_y128, hp200_y256]

lemma hp201_y0 : sum_y_128 201 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp201_y128 : sum_y_128 201 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp201_y256 : sum_y_firstorder 201 256 3 8 = 0 := by solve_sum
lemma eval_x_201 : eval_x 201 = 0 := by
  rw [eval_x, hp201_y0, hp201_y128, hp201_y256]

lemma hp202_y0 : sum_y_128 202 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp202_y128 : sum_y_128 202 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp202_y256 : sum_y_firstorder 202 256 3 8 = 0 := by solve_sum
lemma eval_x_202 : eval_x 202 = 0 := by
  rw [eval_x, hp202_y0, hp202_y128, hp202_y256]

lemma hp203_y0 : sum_y_128 203 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp203_y128 : sum_y_128 203 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp203_y256 : sum_y_firstorder 203 256 3 8 = 0 := by solve_sum
lemma eval_x_203 : eval_x 203 = 0 := by
  rw [eval_x, hp203_y0, hp203_y128, hp203_y256]

lemma hp204_y0 : sum_y_128 204 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp204_y128 : sum_y_128 204 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp204_y256 : sum_y_firstorder 204 256 3 8 = 0 := by solve_sum
lemma eval_x_204 : eval_x 204 = 0 := by
  rw [eval_x, hp204_y0, hp204_y128, hp204_y256]

lemma hp205_y0 : sum_y_128 205 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp205_y128 : sum_y_128 205 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp205_y256 : sum_y_firstorder 205 256 3 8 = 0 := by solve_sum
lemma eval_x_205 : eval_x 205 = 0 := by
  rw [eval_x, hp205_y0, hp205_y128, hp205_y256]

lemma hp206_y0 : sum_y_128 206 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp206_y128 : sum_y_128 206 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp206_y256 : sum_y_firstorder 206 256 3 8 = 0 := by solve_sum
lemma eval_x_206 : eval_x 206 = 0 := by
  rw [eval_x, hp206_y0, hp206_y128, hp206_y256]

lemma hp207_y0 : sum_y_128 207 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp207_y128 : sum_y_128 207 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp207_y256 : sum_y_firstorder 207 256 3 8 = 0 := by solve_sum
lemma eval_x_207 : eval_x 207 = 0 := by
  rw [eval_x, hp207_y0, hp207_y128, hp207_y256]

lemma hp208_y0 : sum_y_128 208 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp208_y128 : sum_y_128 208 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp208_y256 : sum_y_firstorder 208 256 3 8 = 0 := by solve_sum
lemma eval_x_208 : eval_x 208 = 0 := by
  rw [eval_x, hp208_y0, hp208_y128, hp208_y256]

lemma hp209_y0 : sum_y_128 209 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp209_y128 : sum_y_128 209 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp209_y256 : sum_y_firstorder 209 256 3 8 = 0 := by solve_sum
lemma eval_x_209 : eval_x 209 = 0 := by
  rw [eval_x, hp209_y0, hp209_y128, hp209_y256]

lemma hp210_y0 : sum_y_128 210 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp210_y128 : sum_y_128 210 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp210_y256 : sum_y_firstorder 210 256 3 8 = 0 := by solve_sum
lemma eval_x_210 : eval_x 210 = 0 := by
  rw [eval_x, hp210_y0, hp210_y128, hp210_y256]

lemma hp211_y0 : sum_y_128 211 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp211_y128 : sum_y_128 211 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp211_y256 : sum_y_firstorder 211 256 3 8 = 0 := by solve_sum
lemma eval_x_211 : eval_x 211 = 0 := by
  rw [eval_x, hp211_y0, hp211_y128, hp211_y256]

lemma hp212_y0 : sum_y_128 212 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp212_y128 : sum_y_128 212 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp212_y256 : sum_y_firstorder 212 256 3 8 = 0 := by solve_sum
lemma eval_x_212 : eval_x 212 = 0 := by
  rw [eval_x, hp212_y0, hp212_y128, hp212_y256]

lemma hp213_y0 : sum_y_128 213 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp213_y128 : sum_y_128 213 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp213_y256 : sum_y_firstorder 213 256 3 8 = 0 := by solve_sum
lemma eval_x_213 : eval_x 213 = 0 := by
  rw [eval_x, hp213_y0, hp213_y128, hp213_y256]

lemma hp214_y0 : sum_y_128 214 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp214_y128 : sum_y_128 214 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp214_y256 : sum_y_firstorder 214 256 3 8 = 0 := by solve_sum
lemma eval_x_214 : eval_x 214 = 0 := by
  rw [eval_x, hp214_y0, hp214_y128, hp214_y256]

lemma hp215_y0 : sum_y_128 215 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp215_y128 : sum_y_128 215 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp215_y256 : sum_y_firstorder 215 256 3 8 = 0 := by solve_sum
lemma eval_x_215 : eval_x 215 = 0 := by
  rw [eval_x, hp215_y0, hp215_y128, hp215_y256]

lemma hp216_y0 : sum_y_128 216 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp216_y128 : sum_y_128 216 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp216_y256 : sum_y_firstorder 216 256 3 8 = 0 := by solve_sum
lemma eval_x_216 : eval_x 216 = 0 := by
  rw [eval_x, hp216_y0, hp216_y128, hp216_y256]

lemma hp217_y0 : sum_y_128 217 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp217_y128 : sum_y_128 217 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp217_y256 : sum_y_firstorder 217 256 3 8 = 0 := by solve_sum
lemma eval_x_217 : eval_x 217 = 0 := by
  rw [eval_x, hp217_y0, hp217_y128, hp217_y256]

lemma hp218_y0 : sum_y_128 218 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp218_y128 : sum_y_128 218 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp218_y256 : sum_y_firstorder 218 256 3 8 = 0 := by solve_sum
lemma eval_x_218 : eval_x 218 = 0 := by
  rw [eval_x, hp218_y0, hp218_y128, hp218_y256]

lemma hp219_y0 : sum_y_128 219 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp219_y128 : sum_y_128 219 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp219_y256 : sum_y_firstorder 219 256 3 8 = 0 := by solve_sum
lemma eval_x_219 : eval_x 219 = 0 := by
  rw [eval_x, hp219_y0, hp219_y128, hp219_y256]

lemma hp220_y0 : sum_y_128 220 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp220_y128 : sum_y_128 220 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp220_y256 : sum_y_firstorder 220 256 3 8 = 0 := by solve_sum
lemma eval_x_220 : eval_x 220 = 0 := by
  rw [eval_x, hp220_y0, hp220_y128, hp220_y256]

lemma hp221_y0 : sum_y_128 221 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp221_y128 : sum_y_128 221 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp221_y256 : sum_y_firstorder 221 256 3 8 = 0 := by solve_sum
lemma eval_x_221 : eval_x 221 = 0 := by
  rw [eval_x, hp221_y0, hp221_y128, hp221_y256]

lemma hp222_y0 : sum_y_128 222 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp222_y128 : sum_y_128 222 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp222_y256 : sum_y_firstorder 222 256 3 8 = 0 := by solve_sum
lemma eval_x_222 : eval_x 222 = 0 := by
  rw [eval_x, hp222_y0, hp222_y128, hp222_y256]

lemma hp223_y0 : sum_y_128 223 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp223_y128 : sum_y_128 223 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp223_y256 : sum_y_firstorder 223 256 3 8 = 0 := by solve_sum
lemma eval_x_223 : eval_x 223 = 0 := by
  rw [eval_x, hp223_y0, hp223_y128, hp223_y256]

lemma hp224_y0 : sum_y_128 224 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp224_y128 : sum_y_128 224 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp224_y256 : sum_y_firstorder 224 256 3 8 = 0 := by solve_sum
lemma eval_x_224 : eval_x 224 = 0 := by
  rw [eval_x, hp224_y0, hp224_y128, hp224_y256]

lemma hp225_y0 : sum_y_128 225 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp225_y128 : sum_y_128 225 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp225_y256 : sum_y_firstorder 225 256 3 8 = 0 := by solve_sum
lemma eval_x_225 : eval_x 225 = 0 := by
  rw [eval_x, hp225_y0, hp225_y128, hp225_y256]

lemma hp226_y0 : sum_y_128 226 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp226_y128 : sum_y_128 226 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp226_y256 : sum_y_firstorder 226 256 3 8 = 0 := by solve_sum
lemma eval_x_226 : eval_x 226 = 0 := by
  rw [eval_x, hp226_y0, hp226_y128, hp226_y256]

lemma hp227_y0 : sum_y_128 227 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp227_y128 : sum_y_128 227 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp227_y256 : sum_y_firstorder 227 256 3 8 = 0 := by solve_sum
lemma eval_x_227 : eval_x 227 = 0 := by
  rw [eval_x, hp227_y0, hp227_y128, hp227_y256]

lemma hp228_y0 : sum_y_128 228 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp228_y128 : sum_y_128 228 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp228_y256 : sum_y_firstorder 228 256 3 8 = 0 := by solve_sum
lemma eval_x_228 : eval_x 228 = 0 := by
  rw [eval_x, hp228_y0, hp228_y128, hp228_y256]

lemma hp229_y0 : sum_y_128 229 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp229_y128 : sum_y_128 229 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp229_y256 : sum_y_firstorder 229 256 3 8 = 0 := by solve_sum
lemma eval_x_229 : eval_x 229 = 0 := by
  rw [eval_x, hp229_y0, hp229_y128, hp229_y256]

lemma hp230_y0 : sum_y_128 230 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp230_y128 : sum_y_128 230 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp230_y256 : sum_y_firstorder 230 256 3 8 = 0 := by solve_sum
lemma eval_x_230 : eval_x 230 = 0 := by
  rw [eval_x, hp230_y0, hp230_y128, hp230_y256]

lemma hp231_y0 : sum_y_128 231 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp231_y128 : sum_y_128 231 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp231_y256 : sum_y_firstorder 231 256 3 8 = 0 := by solve_sum
lemma eval_x_231 : eval_x 231 = 0 := by
  rw [eval_x, hp231_y0, hp231_y128, hp231_y256]

lemma hp232_y0 : sum_y_128 232 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp232_y128 : sum_y_128 232 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp232_y256 : sum_y_firstorder 232 256 3 8 = 0 := by solve_sum
lemma eval_x_232 : eval_x 232 = 0 := by
  rw [eval_x, hp232_y0, hp232_y128, hp232_y256]

lemma hp233_y0 : sum_y_128 233 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp233_y128 : sum_y_128 233 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp233_y256 : sum_y_firstorder 233 256 3 8 = 0 := by solve_sum
lemma eval_x_233 : eval_x 233 = 0 := by
  rw [eval_x, hp233_y0, hp233_y128, hp233_y256]

lemma hp234_y0 : sum_y_128 234 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp234_y128 : sum_y_128 234 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp234_y256 : sum_y_firstorder 234 256 3 8 = 0 := by solve_sum
lemma eval_x_234 : eval_x 234 = 0 := by
  rw [eval_x, hp234_y0, hp234_y128, hp234_y256]

lemma hp235_y0 : sum_y_128 235 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp235_y128 : sum_y_128 235 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp235_y256 : sum_y_firstorder 235 256 3 8 = 0 := by solve_sum
lemma eval_x_235 : eval_x 235 = 0 := by
  rw [eval_x, hp235_y0, hp235_y128, hp235_y256]

lemma hp236_y0 : sum_y_128 236 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp236_y128 : sum_y_128 236 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp236_y256 : sum_y_firstorder 236 256 3 8 = 0 := by solve_sum
lemma eval_x_236 : eval_x 236 = 0 := by
  rw [eval_x, hp236_y0, hp236_y128, hp236_y256]

lemma hp237_y0 : sum_y_128 237 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp237_y128 : sum_y_128 237 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp237_y256 : sum_y_firstorder 237 256 3 8 = 0 := by solve_sum
lemma eval_x_237 : eval_x 237 = 0 := by
  rw [eval_x, hp237_y0, hp237_y128, hp237_y256]

lemma hp238_y0 : sum_y_128 238 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp238_y128 : sum_y_128 238 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp238_y256 : sum_y_firstorder 238 256 3 8 = 0 := by solve_sum
lemma eval_x_238 : eval_x 238 = 0 := by
  rw [eval_x, hp238_y0, hp238_y128, hp238_y256]

lemma hp239_y0 : sum_y_128 239 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp239_y128 : sum_y_128 239 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp239_y256 : sum_y_firstorder 239 256 3 8 = 0 := by solve_sum
lemma eval_x_239 : eval_x 239 = 0 := by
  rw [eval_x, hp239_y0, hp239_y128, hp239_y256]

lemma hp240_y0 : sum_y_128 240 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp240_y128 : sum_y_128 240 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp240_y256 : sum_y_firstorder 240 256 3 8 = 0 := by solve_sum
lemma eval_x_240 : eval_x 240 = 0 := by
  rw [eval_x, hp240_y0, hp240_y128, hp240_y256]

lemma hp241_y0 : sum_y_128 241 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp241_y128 : sum_y_128 241 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp241_y256 : sum_y_firstorder 241 256 3 8 = 0 := by solve_sum
lemma eval_x_241 : eval_x 241 = 0 := by
  rw [eval_x, hp241_y0, hp241_y128, hp241_y256]

lemma hp242_y0 : sum_y_128 242 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp242_y128 : sum_y_128 242 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp242_y256 : sum_y_firstorder 242 256 3 8 = 0 := by solve_sum
lemma eval_x_242 : eval_x 242 = 0 := by
  rw [eval_x, hp242_y0, hp242_y128, hp242_y256]

lemma hp243_y0 : sum_y_128 243 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp243_y128 : sum_y_128 243 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp243_y256 : sum_y_firstorder 243 256 3 8 = 0 := by solve_sum
lemma eval_x_243 : eval_x 243 = 0 := by
  rw [eval_x, hp243_y0, hp243_y128, hp243_y256]

lemma hp244_y0 : sum_y_128 244 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp244_y128 : sum_y_128 244 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp244_y256 : sum_y_firstorder 244 256 3 8 = 0 := by solve_sum
lemma eval_x_244 : eval_x 244 = 0 := by
  rw [eval_x, hp244_y0, hp244_y128, hp244_y256]

lemma hp245_y0 : sum_y_128 245 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp245_y128 : sum_y_128 245 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp245_y256 : sum_y_firstorder 245 256 3 8 = 0 := by solve_sum
lemma eval_x_245 : eval_x 245 = 0 := by
  rw [eval_x, hp245_y0, hp245_y128, hp245_y256]

lemma hp246_y0 : sum_y_128 246 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp246_y128 : sum_y_128 246 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp246_y256 : sum_y_firstorder 246 256 3 8 = 0 := by solve_sum
lemma eval_x_246 : eval_x 246 = 0 := by
  rw [eval_x, hp246_y0, hp246_y128, hp246_y256]

lemma hp247_y0 : sum_y_128 247 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp247_y128 : sum_y_128 247 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp247_y256 : sum_y_firstorder 247 256 3 8 = 0 := by solve_sum
lemma eval_x_247 : eval_x 247 = 0 := by
  rw [eval_x, hp247_y0, hp247_y128, hp247_y256]

lemma hp248_y0 : sum_y_128 248 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp248_y128 : sum_y_128 248 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp248_y256 : sum_y_firstorder 248 256 3 8 = 0 := by solve_sum
lemma eval_x_248 : eval_x 248 = 0 := by
  rw [eval_x, hp248_y0, hp248_y128, hp248_y256]

lemma hp249_y0 : sum_y_128 249 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp249_y128 : sum_y_128 249 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp249_y256 : sum_y_firstorder 249 256 3 8 = 0 := by solve_sum
lemma eval_x_249 : eval_x 249 = 0 := by
  rw [eval_x, hp249_y0, hp249_y128, hp249_y256]

lemma hp250_y0 : sum_y_128 250 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp250_y128 : sum_y_128 250 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp250_y256 : sum_y_firstorder 250 256 3 8 = 0 := by solve_sum
lemma eval_x_250 : eval_x 250 = 0 := by
  rw [eval_x, hp250_y0, hp250_y128, hp250_y256]

lemma hp251_y0 : sum_y_128 251 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp251_y128 : sum_y_128 251 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp251_y256 : sum_y_firstorder 251 256 3 8 = 0 := by solve_sum
lemma eval_x_251 : eval_x 251 = 0 := by
  rw [eval_x, hp251_y0, hp251_y128, hp251_y256]

lemma hp252_y0 : sum_y_128 252 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp252_y128 : sum_y_128 252 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp252_y256 : sum_y_firstorder 252 256 3 8 = 0 := by solve_sum
lemma eval_x_252 : eval_x 252 = 0 := by
  rw [eval_x, hp252_y0, hp252_y128, hp252_y256]

lemma hp253_y0 : sum_y_128 253 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp253_y128 : sum_y_128 253 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp253_y256 : sum_y_firstorder 253 256 3 8 = 0 := by solve_sum
lemma eval_x_253 : eval_x 253 = 0 := by
  rw [eval_x, hp253_y0, hp253_y128, hp253_y256]

lemma hp254_y0 : sum_y_128 254 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp254_y128 : sum_y_128 254 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp254_y256 : sum_y_firstorder 254 256 3 8 = 0 := by solve_sum
lemma eval_x_254 : eval_x 254 = 0 := by
  rw [eval_x, hp254_y0, hp254_y128, hp254_y256]

lemma hp255_y0 : sum_y_128 255 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp255_y128 : sum_y_128 255 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp255_y256 : sum_y_firstorder 255 256 3 8 = 0 := by solve_sum
lemma eval_x_255 : eval_x 255 = 0 := by
  rw [eval_x, hp255_y0, hp255_y128, hp255_y256]

lemma hp256_y0 : sum_y_128 256 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp256_y128 : sum_y_128 256 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp256_y256 : sum_y_firstorder 256 256 3 8 = 0 := by solve_sum
lemma eval_x_256 : eval_x 256 = 0 := by
  rw [eval_x, hp256_y0, hp256_y128, hp256_y256]

lemma hp257_y0 : sum_y_128 257 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp257_y128 : sum_y_128 257 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp257_y256 : sum_y_firstorder 257 256 3 8 = 0 := by solve_sum
lemma eval_x_257 : eval_x 257 = 0 := by
  rw [eval_x, hp257_y0, hp257_y128, hp257_y256]

lemma hp258_y0 : sum_y_128 258 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp258_y128 : sum_y_128 258 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp258_y256 : sum_y_firstorder 258 256 3 8 = 0 := by solve_sum
lemma eval_x_258 : eval_x 258 = 0 := by
  rw [eval_x, hp258_y0, hp258_y128, hp258_y256]

lemma hp259_y0 : sum_y_128 259 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp259_y128 : sum_y_128 259 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp259_y256 : sum_y_firstorder 259 256 3 8 = 0 := by solve_sum
lemma eval_x_259 : eval_x 259 = 0 := by
  rw [eval_x, hp259_y0, hp259_y128, hp259_y256]

lemma hp260_y0 : sum_y_128 260 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp260_y128 : sum_y_128 260 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp260_y256 : sum_y_firstorder 260 256 3 8 = 0 := by solve_sum
lemma eval_x_260 : eval_x 260 = 0 := by
  rw [eval_x, hp260_y0, hp260_y128, hp260_y256]

lemma hp261_y0 : sum_y_128 261 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp261_y128 : sum_y_128 261 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp261_y256 : sum_y_firstorder 261 256 3 8 = 0 := by solve_sum
lemma eval_x_261 : eval_x 261 = 0 := by
  rw [eval_x, hp261_y0, hp261_y128, hp261_y256]

lemma hp262_y0 : sum_y_128 262 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp262_y128 : sum_y_128 262 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp262_y256 : sum_y_firstorder 262 256 3 8 = 0 := by solve_sum
lemma eval_x_262 : eval_x 262 = 0 := by
  rw [eval_x, hp262_y0, hp262_y128, hp262_y256]

lemma hp263_y0 : sum_y_128 263 0 = 0 := by rw [sum_y_128]; solve_sum
lemma hp263_y128 : sum_y_128 263 128 = 0 := by rw [sum_y_128]; solve_sum
lemma hp263_y256 : sum_y_firstorder 263 256 3 8 = 0 := by solve_sum
lemma eval_x_263 : eval_x 263 = 0 := by
  rw [eval_x, hp263_y0, hp263_y128, hp263_y256]

lemma sum_range_eq_sum_range_of_ge {β : Type} [AddCommMonoid β] (f : ℕ → β)
  (M N : ℕ) (h_le : M ≤ N) (h_zero : ∀ x, x ≥ M → f x = 0) :
  (Finset.range N).sum f = (Finset.range M).sum f := by
  have h_sub : Finset.range M ⊆ Finset.range N := Finset.range_mono h_le
  apply Eq.symm
  apply Finset.sum_subset h_sub
  intro x hx h_not
  have h_ge : x ≥ M := by
    rw [Finset.mem_range] at hx
    rw [Finset.mem_range] at h_not
    omega
  exact h_zero x h_ge

lemma outer_zero (x : ℕ) (hx : x ≥ 264) (N : ℕ) :
  ((Finset.range N).sum fun y =>
   (Finset.range N).sum fun z =>
     if h_z : z > 0 then
       let k := x^2 + y^2 + z^2
       if h_le : k ≤ 69383 then
         let r := 69383 - k
         if IsSquare r then
           let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
           if IsSquare condition_expr then 1 else 0
         else 0
       else 0
     else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hz_pos : z > 0
  · rw [dif_pos hz_pos]
    dsimp only
    by_cases h_le : x^2 + y^2 + z^2 ≤ 69383
    · have h_sq : x^2 ≥ 69696 := by nlinarith
      omega
    · rw [dif_neg h_le]
  · rw [dif_neg hz_pos]

lemma middle_zero (x : ℕ) (y : ℕ) (hy : y ≥ 264) (N : ℕ) :
  ((Finset.range N).sum fun z =>
     if h_z : z > 0 then
       let k := x^2 + y^2 + z^2
       if h_le : k ≤ 69383 then
         let r := 69383 - k
         if IsSquare r then
           let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
           if IsSquare condition_expr then 1 else 0
         else 0
       else 0
     else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hz_pos : z > 0
  · rw [dif_pos hz_pos]
    dsimp only
    by_cases h_le : x^2 + y^2 + z^2 ≤ 69383
    · have h_sq : y^2 ≥ 69696 := by nlinarith
      omega
    · rw [dif_neg h_le]
  · rw [dif_neg hz_pos]

lemma inner_zero (x : ℕ) (y : ℕ) (z : ℕ) (hz : z ≥ 264) :
  (if h_z : z > 0 then
     let k := x^2 + y^2 + z^2
     if h_le : k ≤ 69383 then
       let r := 69383 - k
       if IsSquare r then
         let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
         if IsSquare condition_expr then 1 else 0
       else 0
     else 0
   else 0) = 0 := by
  by_cases hz_pos : z > 0
  · rw [dif_pos hz_pos]
    dsimp only
    by_cases h_le : x^2 + y^2 + z^2 ≤ 69383
    · have h_sq : z^2 ≥ 69696 := by nlinarith
      omega
    · rw [dif_neg h_le]
  · rw [dif_neg hz_pos]

theorem a_69383_eq_sum_264 : a 69383 =
  ((Finset.range 264).sum fun x =>
   (Finset.range 264).sum fun y =>
   (Finset.range 264).sum fun z =>
     if h_z : z > 0 then
       let k := x^2 + y^2 + z^2
       if h_le : k ≤ 69383 then
         let r := 69383 - k
         if IsSquare r then
           let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
           if IsSquare condition_expr then 1 else 0
         else 0
       else 0
     else 0) := by
  rw [a]
  -- Outer sum
  have h_le_69384 : 264 ≤ 69384 := by omega
  rw [sum_range_eq_sum_range_of_ge _ 264 69384 h_le_69384 (fun x hx => outer_zero x hx 69384)]
  -- Middle sum
  have h_mid : ∀ x ∈ Finset.range 264,
    (Finset.range 69384).sum (fun y =>
      (Finset.range 69384).sum (fun z =>
        if h_z : z > 0 then
          let k := x^2 + y^2 + z^2
          if h_le : k ≤ 69383 then
            let r := 69383 - k
            if IsSquare r then
              let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
              if IsSquare condition_expr then 1 else 0
            else 0
          else 0
        else 0)) =
    (Finset.range 264).sum (fun y =>
      (Finset.range 69384).sum (fun z =>
        if h_z : z > 0 then
          let k := x^2 + y^2 + z^2
          if h_le : k ≤ 69383 then
            let r := 69383 - k
            if IsSquare r then
              let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
              if IsSquare condition_expr then 1 else 0
            else 0
          else 0
        else 0)) := by
    intro x hx
    rw [sum_range_eq_sum_range_of_ge _ 264 69384 h_le_69384 (fun y hy => middle_zero x y hy 69384)]
  rw [Finset.sum_congr rfl h_mid]
  -- Inner sum
  have h_inn : ∀ x ∈ Finset.range 264, ∀ y ∈ Finset.range 264,
    (Finset.range 69384).sum (fun z =>
      if h_z : z > 0 then
        let k := x^2 + y^2 + z^2
        if h_le : k ≤ 69383 then
          let r := 69383 - k
          if IsSquare r then
            let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
            if IsSquare condition_expr then 1 else 0
          else 0
        else 0
      else 0) =
    (Finset.range 264).sum (fun z =>
      if h_z : z > 0 then
        let k := x^2 + y^2 + z^2
        if h_le : k ≤ 69383 then
          let r := 69383 - k
          if IsSquare r then
            let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
            if IsSquare condition_expr then 1 else 0
          else 0
        else 0
      else 0) := by
    intro x hx y hy
    rw [sum_range_eq_sum_range_of_ge _ 264 69384 h_le_69384 (fun z hz => inner_zero x y z hz)]
  have h_mid_inn : ∀ x ∈ Finset.range 264,
    (Finset.range 264).sum (fun y =>
      (Finset.range 69384).sum (fun z =>
        if h_z : z > 0 then
          let k := x^2 + y^2 + z^2
          if h_le : k ≤ 69383 then
            let r := 69383 - k
            if IsSquare r then
              let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
              if IsSquare condition_expr then 1 else 0
            else 0
          else 0
        else 0)) =
    (Finset.range 264).sum (fun y =>
      (Finset.range 264).sum (fun z =>
        if h_z : z > 0 then
          let k := x^2 + y^2 + z^2
          if h_le : k ≤ 69383 then
            let r := 69383 - k
            if IsSquare r then
              let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
              if IsSquare condition_expr then 1 else 0
            else 0
          else 0
        else 0)) := by
    intro x hx
    exact Finset.sum_congr rfl (h_inn x hx)
  exact Finset.sum_congr rfl h_mid_inn

lemma sum_range_264_eq_sum_y_firstorder_congr :
  (∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ range 264, term_func x y z) =
  ∑ x ∈ range 264, eval_x x := by
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_range_264_eq_sum_y_firstorder x

theorem eval_x_sum_eq_1 :
  (∑ x ∈ range 264, eval_x x) = 1 := by
  simp only [eval_x_0, eval_x_1, eval_x_2, eval_x_3, eval_x_4, eval_x_5, eval_x_6, eval_x_7, eval_x_8, eval_x_9, eval_x_10, eval_x_11, eval_x_12, eval_x_13, eval_x_14, eval_x_15, eval_x_16, eval_x_17, eval_x_18, eval_x_19, eval_x_20, eval_x_21, eval_x_22, eval_x_23, eval_x_24, eval_x_25, eval_x_26, eval_x_27, eval_x_28, eval_x_29, eval_x_30, eval_x_31, eval_x_32, eval_x_33, eval_x_34, eval_x_35, eval_x_36, eval_x_37, eval_x_38, eval_x_39, eval_x_40, eval_x_41, eval_x_42, eval_x_43, eval_x_44, eval_x_45, eval_x_46, eval_x_47, eval_x_48, eval_x_49, eval_x_50, eval_x_51, eval_x_52, eval_x_53, eval_x_54, eval_x_55, eval_x_56, eval_x_57, eval_x_58, eval_x_59, eval_x_60, eval_x_61, eval_x_62, eval_x_63, eval_x_64, eval_x_65, eval_x_66, eval_x_67, eval_x_68, eval_x_69, eval_x_70, eval_x_71, eval_x_72, eval_x_73, eval_x_74, eval_x_75, eval_x_76, eval_x_77, eval_x_78, eval_x_79, eval_x_80, eval_x_81, eval_x_82, eval_x_83, eval_x_84, eval_x_85, eval_x_86, eval_x_87, eval_x_88, eval_x_89, eval_x_90, eval_x_91, eval_x_92, eval_x_93, eval_x_94, eval_x_95, eval_x_96, eval_x_97, eval_x_98, eval_x_99, eval_x_100, eval_x_101, eval_x_102, eval_x_103, eval_x_104, eval_x_105, eval_x_106, eval_x_107, eval_x_108, eval_x_109, eval_x_110, eval_x_111, eval_x_112, eval_x_113, eval_x_114, eval_x_115, eval_x_116, eval_x_117, eval_x_118, eval_x_119, eval_x_120, eval_x_121, eval_x_122, eval_x_123, eval_x_124, eval_x_125, eval_x_126, eval_x_127, eval_x_128, eval_x_129, eval_x_130, eval_x_131, eval_x_132, eval_x_133, eval_x_134, eval_x_135, eval_x_136, eval_x_137, eval_x_138, eval_x_139, eval_x_140, eval_x_141, eval_x_142, eval_x_143, eval_x_144, eval_x_145, eval_x_146, eval_x_147, eval_x_148, eval_x_149, eval_x_150, eval_x_151, eval_x_152, eval_x_153, eval_x_154, eval_x_155, eval_x_156, eval_x_157, eval_x_158, eval_x_159, eval_x_160, eval_x_161, eval_x_162, eval_x_163, eval_x_164, eval_x_165, eval_x_166, eval_x_167, eval_x_168, eval_x_169, eval_x_170, eval_x_171, eval_x_172, eval_x_173, eval_x_174, eval_x_175, eval_x_176, eval_x_177, eval_x_178, eval_x_179, eval_x_180, eval_x_181, eval_x_182, eval_x_183, eval_x_184, eval_x_185, eval_x_186, eval_x_187, eval_x_188, eval_x_189, eval_x_190, eval_x_191, eval_x_192, eval_x_193, eval_x_194, eval_x_195, eval_x_196, eval_x_197, eval_x_198, eval_x_199, eval_x_200, eval_x_201, eval_x_202, eval_x_203, eval_x_204, eval_x_205, eval_x_206, eval_x_207, eval_x_208, eval_x_209, eval_x_210, eval_x_211, eval_x_212, eval_x_213, eval_x_214, eval_x_215, eval_x_216, eval_x_217, eval_x_218, eval_x_219, eval_x_220, eval_x_221, eval_x_222, eval_x_223, eval_x_224, eval_x_225, eval_x_226, eval_x_227, eval_x_228, eval_x_229, eval_x_230, eval_x_231, eval_x_232, eval_x_233, eval_x_234, eval_x_235, eval_x_236, eval_x_237, eval_x_238, eval_x_239, eval_x_240, eval_x_241, eval_x_242, eval_x_243, eval_x_244, eval_x_245, eval_x_246, eval_x_247, eval_x_248, eval_x_249, eval_x_250, eval_x_251, eval_x_252, eval_x_253, eval_x_254, eval_x_255, eval_x_256, eval_x_257, eval_x_258, eval_x_259, eval_x_260, eval_x_261, eval_x_262, eval_x_263]
  rfl
theorem a_69383_eq_1 : a 69383 = 1 := by
  rw [a_69383_eq_sum_264]
  -- convert sum over z to term_func
  have h_term : (∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ range 264,
        if h_z : z > 0 then
          let k := x^2 + y^2 + z^2
          if h_le : k ≤ 69383 then
            let r := 69383 - k
            if IsSquare r then
              let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
              if IsSquare condition_expr then 1 else 0
            else 0
          else 0
        else 0) =
      (∑ x ∈ range 264, ∑ y ∈ range 264, ∑ z ∈ range 264, term_func x y z) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    rw [term_func]
    simp [is_square_fast_iff, is_square_large_iff]
  rw [h_term]
  rw [sum_range_264_eq_sum_y_firstorder_congr]
  exact eval_x_sum_eq_1

theorem oeis_261876_conjecture_0.disproof :
  ¬ ∀ (n : ℕ),
    (n > 0 → a n > 0) ∧
    (a n = 1 ↔ ∃ k m : ℕ, special_m_set m ∧ n = 4^k * m) := by
  intro h
  have h_69383 := h 69383
  have h_69383_iff := h_69383.right
  rw [a_69383_eq_1] at h_69383_iff
  have h_spec : ∃ k m : ℕ, special_m_set m ∧ 69383 = 4^k * m := h_69383_iff.mp rfl
  rcases h_spec with ⟨k, m, hm, h_69383_eq⟩
  -- 69383 is odd, so 4^k * m = 69383 is only possible if k = 0
  have hk : k = 0 := by
    by_contra hc
    have h_even : 4^k * m % 2 = 0 := by
      have hk_ge_1 : k ≥ 1 := by omega
      have : 4^k = 4 * 4^(k-1) := by
        have hk_eq : k = (k - 1) + 1 := by omega
        rw [hk_eq]
        rw [pow_succ]
        ring
      rw [this]
      omega
    have h_odd : (4^k * m) % 2 = 1 := by
      rw [← h_69383_eq]
      rfl
    omega
  rw [hk] at h_69383_eq
  simp at h_69383_eq
  rw [← h_69383_eq] at hm
  have h_69383_m : 69383 = m := by
    rw [← h_69383_eq]
    rfl
  rw [← h_69383_m] at hm
  revert hm
  decide
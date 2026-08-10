import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000

open Nat Finset

/--
A338019: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $3x + 10y + 36z$ a positive square, where $x, y, z, w$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  -- Define the 4D bounded box BoundingBox = R x R x R x R, structured as ((ℕ × ℕ) × (ℕ × ℕ)).
  let BoundingBox := (R.product R).product (R.product R)

  Finset.card
    (BoundingBox.filter (fun p =>
      -- Destructure the nested tuple p : ((ℕ × ℕ) × (ℕ × ℕ))
      let ((x, y), (z, w)) := p

      -- Condition 1: x^2 + y^2 + z^2 + w^2 = n
      x^2 + y^2 + z^2 + w^2 = n ∧

      -- Condition 2: 3x + 10y + 36z is a positive perfect square
      let c := 3 * x + 10 * y + 36 * z
      -- Check if c > 0 AND c is a perfect square (c.sqrt * c.sqrt = c)
      c > 0 ∧ c.sqrt * c.sqrt = c
    ))

theorem a_pos_iff_exists (n : ℕ) :
  a n > 0 ↔ ∃ x y z w : ℕ,
    x^2 + y^2 + z^2 + w^2 = n ∧
    let c := 3 * x + 10 * y + 36 * z
    c > 0 ∧ c.sqrt * c.sqrt = c := by
  unfold a
  change 0 < Finset.card _ ↔ _
  rw [card_pos, Finset.Nonempty]
  constructor
  · rintro ⟨p, h⟩
    let ((x, y), (z, w)) := p
    simp only [mem_filter] at h
    rcases h with ⟨-, h1, h2⟩
    refine ⟨x, y, z, w, h1, h2⟩
  · rintro ⟨x, y, z, w, h1, h2⟩
    have h_le_x : x^2 ≤ n := by omega
    have h_le_y : y^2 ≤ n := by omega
    have h_le_z : z^2 ≤ n := by omega
    have h_le_w : w^2 ≤ n := by omega
    have h_x : x ≤ n.sqrt := le_sqrt'.mpr h_le_x
    have h_y : y ≤ n.sqrt := le_sqrt'.mpr h_le_y
    have h_z : z ≤ n.sqrt := le_sqrt'.mpr h_le_z
    have h_w : w ≤ n.sqrt := le_sqrt'.mpr h_le_w
    refine ⟨((x, y), (z, w)), ?_⟩
    simp only [mem_filter]
    refine ⟨?_, h1, h2⟩
    simp
    exact ⟨⟨h_x, h_y⟩, ⟨h_z, h_w⟩⟩

def isEvenFin8 (a : Fin 8) : Bool :=
  a == 0 || a == 2 || a == 4 || a == 6

theorem fin8_four_squares : ∀ a b c d : Fin 8,
    (a.val^2 + b.val^2 + c.val^2 + d.val^2) % 8 = 0 →
    isEvenFin8 a ∧ isEvenFin8 b ∧ isEvenFin8 c ∧ isEvenFin8 d := by
  decide

lemma even_of_fin8 (a : Fin 8) (h : isEvenFin8 a = true) (x : ℕ) (hx : x % 8 = a.val) : Even x := by
  have h_div_mod := Nat.div_add_mod x 8
  fin_cases a <;> try { dsimp [isEvenFin8] at h; contradiction }
  · -- a = 0
    use 4 * (x / 8)
    change x % 8 = 0 at hx
    omega
  · -- a = 2
    use 4 * (x / 8) + 1
    change x % 8 = 2 at hx
    omega
  · -- a = 4
    use 4 * (x / 8) + 2
    change x % 8 = 4 at hx
    omega
  · -- a = 6
    use 4 * (x / 8) + 3
    change x % 8 = 6 at hx
    omega

lemma even_of_sum_squares_eq_eight_mul (x y z w k : ℕ) (h : x^2 + y^2 + z^2 + w^2 = 8 * k) :
    Even x ∧ Even y ∧ Even z ∧ Even w := by
  let a : Fin 8 := ⟨x % 8, Nat.mod_lt x (by decide)⟩
  let b : Fin 8 := ⟨y % 8, Nat.mod_lt y (by decide)⟩
  let c : Fin 8 := ⟨z % 8, Nat.mod_lt z (by decide)⟩
  let d : Fin 8 := ⟨w % 8, Nat.mod_lt w (by decide)⟩
  have h_mod : (a.val^2 + b.val^2 + c.val^2 + d.val^2) % 8 = 0 := by
    have h1 : a.val^2 ≡ x^2 [MOD 8] := by
      change (x % 8)^2 ≡ x^2 [MOD 8]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq x 8)
    have h2 : b.val^2 ≡ y^2 [MOD 8] := by
      change (y % 8)^2 ≡ y^2 [MOD 8]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq y 8)
    have h3 : c.val^2 ≡ z^2 [MOD 8] := by
      change (z % 8)^2 ≡ z^2 [MOD 8]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq z 8)
    have h4 : d.val^2 ≡ w^2 [MOD 8] := by
      change (w % 8)^2 ≡ w^2 [MOD 8]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq w 8)
    have h_sum : a.val^2 + b.val^2 + c.val^2 + d.val^2 ≡ x^2 + y^2 + z^2 + w^2 [MOD 8] :=
      Nat.ModEq.add (Nat.ModEq.add (Nat.ModEq.add h1 h2) h3) h4
    have h_div : x^2 + y^2 + z^2 + w^2 ≡ 0 [MOD 8] := by
      rw [h]
      change (8 * k) % 8 = 0 % 8
      omega
    have h_final : (a.val^2 + b.val^2 + c.val^2 + d.val^2) % 8 = 0 % 8 := h_sum.trans h_div
    exact h_final
  have h_even := fin8_four_squares a b c d h_mod
  exact ⟨even_of_fin8 a h_even.1 x rfl, even_of_fin8 b h_even.2.1 y rfl, even_of_fin8 c h_even.2.2.1 z rfl, even_of_fin8 d h_even.2.2.2 w rfl⟩

lemma descent_step (x y z w k : ℕ) (h_sum : x^2 + y^2 + z^2 + w^2 = 8 * k)
    (s : ℕ) (h_c : 3 * x + 10 * y + 36 * z = s^2) (h_s_pos : s > 0) :
    ∃ (x2 y1 z1 w1 s1 : ℕ),
      4 * x2^2 + y1^2 + z1^2 + w1^2 = 2 * k ∧
      3 * x2 + 5 * y1 + 18 * z1 = s1^2 ∧
      s1 > 0 := by
  have h_even := even_of_sum_squares_eq_eight_mul x y z w k h_sum
  rcases h_even.1 with ⟨x1, hx1⟩
  rcases h_even.2.1 with ⟨y1, hy1⟩
  rcases h_even.2.2.1 with ⟨z1, hz1⟩
  rcases h_even.2.2.2 with ⟨w1, hw1⟩
  have h_x_eq : x = 2 * x1 := by omega
  have h_y_eq : y = 2 * y1 := by omega
  have h_z_eq : z = 2 * z1 := by omega
  have h_w_eq : w = 2 * w1 := by omega
  have h_s2 : s^2 = 2 * (3 * x1 + 10 * y1 + 36 * z1) := by
    rw [h_x_eq, h_y_eq, h_z_eq] at h_c
    omega
  have h_s_even : Even s := by
    have h_even_s2 : Even (s^2) := by
      use 3 * x1 + 10 * y1 + 36 * z1
      omega
    exact (Nat.even_pow.mp h_even_s2).1
  rcases h_s_even with ⟨s1, hs1⟩
  have h_s_eq : s = 2 * s1 := by omega
  have h_s_sq : s^2 = 4 * s1^2 := by
    calc
      s^2 = (2 * s1)^2 := by rw [h_s_eq]
      _ = 4 * s1^2 := by ring
  have h_s1_eq : 2 * s1^2 = 3 * x1 + 10 * y1 + 36 * z1 := by
    have : 4 * s1^2 = 2 * (3 * x1 + 10 * y1 + 36 * z1) := by
      rw [← h_s_sq, h_s2]
    omega
  have h_x1_even : Even x1 := by
    have h_even_sum : Even (3 * x1 + 10 * y1 + 36 * z1) := by
      use s1^2
      omega
    have h_even_3x1 : Even (3 * x1) := by
      rcases h_even_sum with ⟨R, hR⟩
      use R - 5 * y1 - 18 * z1
      omega
    exact (Nat.even_mul.mp h_even_3x1).resolve_left (by decide)
  rcases h_x1_even with ⟨x2, hx2⟩
  have h_x1_eq : x1 = 2 * x2 := by omega
  have h_s1_sq : s1^2 = 3 * x2 + 5 * y1 + 18 * z1 := by
    omega
  have h_s1_pos : s1 > 0 := by
    omega
  have h_sum_div : 4 * x2^2 + y1^2 + z1^2 + w1^2 = 2 * k := by
    have h_ring : x^2 + y^2 + z^2 + w^2 = 4 * (4 * x2^2 + y1^2 + z1^2 + w1^2) := by
      rw [h_x_eq, h_y_eq, h_z_eq, h_w_eq, h_x1_eq]
      ring
    have h_total : 4 * (4 * x2^2 + y1^2 + z1^2 + w1^2) = 4 * (2 * k) := by
      rw [← h_ring, h_sum]
      ring
    omega
  exact ⟨x2, y1, z1, w1, s1, h_sum_div, h_s1_sq.symm, h_s1_pos⟩


def isEvenFin4 (a : Fin 4) : Bool :=
  a == 0 || a == 2

theorem fin4_three_squares : ∀ a b c : Fin 4,
    (a.val^2 + b.val^2 + c.val^2) % 4 = 0 →
    isEvenFin4 a ∧ isEvenFin4 b ∧ isEvenFin4 c := by
  decide

lemma even_of_fin4 (a : Fin 4) (h : isEvenFin4 a = true) (x : ℕ) (hx : x % 4 = a.val) : Even x := by
  have h_div_mod := Nat.div_add_mod x 4
  fin_cases a <;> try { dsimp [isEvenFin4] at h; contradiction }
  · -- a = 0
    use 2 * (x / 4)
    change x % 4 = 0 at hx
    omega
  · -- a = 2
    use 2 * (x / 4) + 1
    change x % 4 = 2 at hx
    omega

lemma even_of_sum_three_squares_eq_four_mul (y1 z1 w1 k : ℕ) (h : y1^2 + z1^2 + w1^2 = 4 * k) :
    Even y1 ∧ Even z1 ∧ Even w1 := by
  let a : Fin 4 := ⟨y1 % 4, Nat.mod_lt y1 (by decide)⟩
  let b : Fin 4 := ⟨z1 % 4, Nat.mod_lt z1 (by decide)⟩
  let c : Fin 4 := ⟨w1 % 4, Nat.mod_lt w1 (by decide)⟩
  have h_mod : (a.val^2 + b.val^2 + c.val^2) % 4 = 0 := by
    have h1 : a.val^2 ≡ y1^2 [MOD 4] := by
      change (y1 % 4)^2 ≡ y1^2 [MOD 4]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq y1 4)
    have h2 : b.val^2 ≡ z1^2 [MOD 4] := by
      change (z1 % 4)^2 ≡ z1^2 [MOD 4]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq z1 4)
    have h3 : c.val^2 ≡ w1^2 [MOD 4] := by
      change (w1 % 4)^2 ≡ w1^2 [MOD 4]
      exact Nat.ModEq.pow 2 (Nat.mod_modEq w1 4)
    have h_sum : a.val^2 + b.val^2 + c.val^2 ≡ y1^2 + z1^2 + w1^2 [MOD 4] :=
      Nat.ModEq.add (Nat.ModEq.add h1 h2) h3
    have h_div : y1^2 + z1^2 + w1^2 ≡ 0 [MOD 4] := by
      rw [h]
      change (4 * k) % 4 = 0 % 4
      omega
    have h_final : (a.val^2 + b.val^2 + c.val^2) % 4 = 0 % 4 := h_sum.trans h_div
    exact h_final
  have h_even := fin4_three_squares a b c h_mod
  exact ⟨even_of_fin4 a h_even.1 y1 rfl, even_of_fin4 b h_even.2.1 z1 rfl, even_of_fin4 c h_even.2.2 w1 rfl⟩


set_option maxHeartbeats 1000000

def is_square (C : ℕ) : Bool :=
  (List.range 35).any (fun s => s * s == C)

def check_sol_opt (K : ℕ) (M : ℕ) : Bool :=
  (List.range (M + 1)).all (fun x =>
    (List.range (M + 1)).all (fun y =>
      (List.range (M + 1)).all (fun z =>
        let S := x^2 + y^2 + z^2
        if S <= K then
          let rem := K - S
          if is_square rem then
            let c := 3 * x + 10 * y + 36 * z
            if c > 0 && is_square c then
              false
            else
              true
          else
            true
        else
          true
      )
    )
  )

theorem check_sol_8 : check_sol_opt 8 2 = true := by decide
theorem check_sol_24 : check_sol_opt 24 4 = true := by decide
theorem check_sol_40 : check_sol_opt 40 6 = true := by decide
theorem check_sol_488 : check_sol_opt 488 22 = true := by decide

lemma sqrt_eq_of_bounds (n M : ℕ) (h1 : M^2 ≤ n) (h2 : n < (M + 1) * (M + 1)) : sqrt n = M := by
  have l1 : M ≤ sqrt n := Nat.le_sqrt'.mpr h1
  have l2 : sqrt n < M + 1 := Nat.sqrt_lt.mpr h2
  omega

lemma all_range_helper {p : ℕ → Bool} {M : ℕ} (h : (List.range (M + 1)).all p = true) (x : ℕ) (hx : x ≤ M) : p x = true := by
  rw [List.all_eq_true] at h
  apply h
  rw [List.mem_range]
  omega

lemma is_square_of_square (w : ℕ) (hw : w < 35) : is_square (w^2) = true := by
  dsimp [is_square]
  rw [List.any_eq_true]
  refine ⟨w, ?_, ?_⟩
  · rw [List.mem_range]
    exact hw
  · rw [Nat.pow_two]
    simp

lemma no_solution_base_for_K (K M : ℕ) (h_K_le : K ≤ 488) (h_check : check_sol_opt K M = true) (h_sqrt : sqrt K = M)
    (x y z w : ℕ) (h_sum : x^2 + y^2 + z^2 + w^2 = K) (s : ℕ) (h_c : 3 * x + 10 * y + 36 * z = s^2) (h_s : s > 0) : False := by
  have h_x : x ≤ M := by
    rw [← h_sqrt]
    have : x^2 ≤ K := by omega
    exact Nat.le_sqrt'.mpr this
  have h_y : y ≤ M := by
    rw [← h_sqrt]
    have : y^2 ≤ K := by omega
    exact Nat.le_sqrt'.mpr this
  have h_z : z ≤ M := by
    rw [← h_sqrt]
    have : z^2 ≤ K := by omega
    exact Nat.le_sqrt'.mpr this
  have h_w : w ≤ M := by
    rw [← h_sqrt]
    have : w^2 ≤ K := by omega
    exact Nat.le_sqrt'.mpr this

  have h_all1 := all_range_helper h_check x h_x
  have h_all2 := all_range_helper h_all1 y h_y
  have h_all3 := all_range_helper h_all2 z h_z
  dsimp at h_all3

  have h_S : x^2 + y^2 + z^2 ≤ K := by omega
  rw [if_pos h_S] at h_all3
  have h_rem_eq : K - (x^2 + y^2 + z^2) = w^2 := by omega
  rw [h_rem_eq] at h_all3

  have h_w_sq_le : w * w ≤ K := by
    have : w^2 ≤ K := by omega
    rwa [Nat.pow_two] at this
  have h_w2 : w * w ≤ 488 := by omega

  have h_w_lt : w < 35 := by
    have h_w_lt23 : w < 23 := by
      by_contra hc
      have h2 : w ≥ 23 := by omega
      have h3 : w * w ≥ 23 * 23 := Nat.mul_le_mul h2 h2
      have h4 : 23 * 23 = 529 := by rfl
      rw [h4] at h3
      omega
    omega
  have h_sq_rem := is_square_of_square w h_w_lt
  rw [h_sq_rem, if_pos rfl] at h_all3

  have h_c_eq : 3 * x + 10 * y + 36 * z = s^2 := h_c
  rw [h_c_eq] at h_all3

  have h_M_le : M ≤ 22 := by
    by_contra hc
    have hM23 : M ≥ 23 := by omega
    have hM_sq : M * M ≥ 23 * 23 := Nat.mul_le_mul hM23 hM23
    have h_sq_le : (sqrt K) * (sqrt K) ≤ K := Nat.sqrt_le K
    rw [h_sqrt] at h_sq_le
    omega

  have h_linear_le : 3 * x + 10 * y + 36 * z ≤ 3 * M + 10 * M + 36 * M := by omega

  have h_s_lt : s < 35 := by
    have : s * s ≤ 1078 := by
      have h_s2_eq : s^2 = s * s := by ring
      rw [← h_s2_eq]
      calc
        s^2 = 3 * x + 10 * y + 36 * z := h_c.symm
        _ ≤ 3 * M + 10 * M + 36 * M := h_linear_le
        _ = 49 * M := by ring
        _ ≤ 49 * 22 := by
          have : 49 * M ≤ 49 * 22 := by omega
          omega
        _ = 1078 := by rfl
    by_contra hc
    have h2 : s ≥ 35 := by omega
    have h3 : s * s ≥ 35 * 35 := Nat.mul_le_mul h2 h2
    have h4 : 35 * 35 = 1225 := by rfl
    rw [h4] at h3
    omega

  have h_sq_c := is_square_of_square s h_s_lt
  have h_c_pos : s^2 > 0 := by
    have h_pos : s * s > 0 := Nat.mul_pos h_s h_s
    have h_sq : s^2 = s * s := by ring
    omega
  have h_dec_pos : (decide (s^2 > 0)) = true := decide_eq_true h_c_pos
  rw [h_dec_pos, h_sq_c] at h_all3
  dsimp at h_all3
  contradiction

lemma no_solution_base (m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) (x y z w : ℕ) (h_sum : x^2 + y^2 + z^2 + w^2 = 8 * m) (s : ℕ) (h_c : 3 * x + 10 * y + 36 * z = s^2) (h_s : s > 0) : False := by
  rcases hm with rfl | rfl | rfl | rfl
  · -- m = 1
    exact no_solution_base_for_K 8 2 (by decide) check_sol_8
      (sqrt_eq_of_bounds 8 2 (by decide) (by decide)) x y z w h_sum s h_c h_s
  · -- m = 3
    exact no_solution_base_for_K 24 4 (by decide) check_sol_24
      (sqrt_eq_of_bounds 24 4 (by decide) (by decide)) x y z w h_sum s h_c h_s
  · -- m = 5
    exact no_solution_base_for_K 40 6 (by decide) check_sol_40
      (sqrt_eq_of_bounds 40 6 (by decide) (by decide)) x y z w h_sum s h_c h_s
  · -- m = 61
    exact no_solution_base_for_K 488 22 (by decide) check_sol_488
      (sqrt_eq_of_bounds 488 22 (by decide) (by decide)) x y z w h_sum s h_c h_s

lemma no_solution_induction (k : ℕ) : ∀ m, (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) → ∀ x y z w,
    x^2 + y^2 + z^2 + w^2 = 2^(4 * k + 3) * m → ∀ s, 3 * x + 10 * y + 36 * z = s^2 → s > 0 → False := by
  induction k with
  | zero =>
    intro m hm x y z w h_sum s h_c h_s
    have h_pow : 2^(4 * 0 + 3) = 8 := by rfl
    rw [h_pow] at h_sum
    exact no_solution_base m hm x y z w h_sum s h_c h_s
  | succ k ih =>
    intro m hm x y z w h_sum s h_c h_s
    have h_pow_succ : 2^(4 * (k + 1) + 3) * m = 8 * (2^(4 * k + 4) * m) := by
      calc
        2^(4 * (k + 1) + 3) * m = 2^(4 * k + 7) * m := by ring_nf
        _ = 8 * (2^(4 * k + 4) * m) := by ring
    rw [h_pow_succ] at h_sum
    obtain ⟨x2, y1, z1, w1, s1, h1, h2, h3⟩ := descent_step x y z w (2^(4 * k + 4) * m) h_sum s h_c h_s
    have h_sum2 : (2 * x2)^2 + y1^2 + z1^2 + w1^2 = 8 * (2^(4 * k + 2) * m) := by
      calc
        (2 * x2)^2 + y1^2 + z1^2 + w1^2 = 4 * x2^2 + y1^2 + z1^2 + w1^2 := by ring
        _ = 2 * (2^(4 * k + 4) * m) := h1
        _ = 8 * (2^(4 * k + 2) * m) := by ring
    have h_even2 := even_of_sum_squares_eq_eight_mul (2 * x2) y1 z1 w1 (2^(4 * k + 2) * m) h_sum2
    rcases h_even2.1 with ⟨x3, hx3⟩
    rcases h_even2.2.1 with ⟨y2, hy2⟩
    rcases h_even2.2.2.1 with ⟨z2, hz2⟩
    rcases h_even2.2.2.2 with ⟨w2, hw2⟩
    have h_y1_eq : y1 = 2 * y2 := by omega
    have h_z1_eq : z1 = 2 * z2 := by omega
    have h_w1_eq : w1 = 2 * w2 := by omega
    have h_x2_eq : x2 = x3 := by omega
    have h_s1_sq2 : 3 * x3 + 10 * y2 + 36 * z2 = s1^2 := by
      rw [← h2, h_x2_eq, h_y1_eq, h_z1_eq]
      ring
    have h_sum3 : x3^2 + y2^2 + z2^2 + w2^2 = 2^(4 * k + 3) * m := by
      have h_ring : (2 * x2)^2 + y1^2 + z1^2 + w1^2 = 4 * (x3^2 + y2^2 + z2^2 + w2^2) := by
        rw [h_x2_eq, h_y1_eq, h_z1_eq, h_w1_eq]
        ring
      have h_total : 4 * (x3^2 + y2^2 + z2^2 + w2^2) = 4 * (2^(4 * k + 3) * m) := by
        rw [← h_ring, h_sum2]
        ring
      omega
    exact ih m hm x3 y2 z2 w2 h_sum3 s1 h_s1_sq2 h3


lemma a_pos_of_a_pos_div_sixteen (d : ℕ) (h : a d > 0) : a (16 * d) > 0 := by
  rw [a_pos_iff_exists] at h
  rcases h with ⟨x, y, z, w, h_sum, h_c_pos, h_c_sq⟩
  let s := (3 * x + 10 * y + 36 * z).sqrt
  have h_c_eq : 3 * x + 10 * y + 36 * z = s^2 := by
    rw [Nat.pow_two]
    exact h_c_sq.symm
  have h_s_pos : s > 0 := by
    by_contra hc
    have : s = 0 := by omega
    rw [this] at h_c_eq
    simp at h_c_eq
    omega
  rw [a_pos_iff_exists]
  refine ⟨4 * x, 4 * y, 4 * z, 4 * w, ?_, ?_⟩
  · calc
      (4 * x)^2 + (4 * y)^2 + (4 * z)^2 + (4 * w)^2 = 16 * (x^2 + y^2 + z^2 + w^2) := by ring
      _ = 16 * d := by rw [h_sum]
  · dsimp
    have h_c_new : 3 * (4 * x) + 10 * (4 * y) + 36 * (4 * z) = (2 * s)^2 := by
      calc
        3 * (4 * x) + 10 * (4 * y) + 36 * (4 * z) = 4 * (3 * x + 10 * y + 36 * z) := by ring
        _ = 4 * s^2 := by rw [h_c_eq]
        _ = (2 * s)^2 := by ring
    refine ⟨?_, ?_⟩
    · rw [h_c_new]
      have : 2 * s > 0 := by omega
      positivity
    · have h_sqrt_new : (3 * (4 * x) + 10 * (4 * y) + 36 * (4 * z)).sqrt = 2 * s := by
        rw [h_c_new]
        exact Nat.sqrt_eq' (2 * s)
      rw [h_sqrt_new]
      rw [Nat.pow_two] at h_c_new
      exact h_c_new.symm

lemma a_pos_div_sixteen (d : ℕ) (h : a (16 * d) > 0) : a d > 0 := by
  rw [a_pos_iff_exists] at h
  rcases h with ⟨x, y, z, w, h_sum, h_c_pos, h_c_sq⟩
  let s := (3 * x + 10 * y + 36 * z).sqrt
  have h_c_eq : 3 * x + 10 * y + 36 * z = s^2 := by
    rw [Nat.pow_two]
    exact h_c_sq.symm
  have h_s_pos : s > 0 := by
    by_contra hc
    have : s = 0 := by omega
    rw [this] at h_c_eq
    simp at h_c_eq
    omega
  have h_sum_eight : x^2 + y^2 + z^2 + w^2 = 8 * (2 * d) := by
    calc
      x^2 + y^2 + z^2 + w^2 = 16 * d := h_sum
      _ = 8 * (2 * d) := by ring
  obtain ⟨x2, y1, z1, w1, s1, h1, h2, h3⟩ := descent_step x y z w (2 * d) h_sum_eight s h_c_eq h_s_pos
  have h_sum_three : y1^2 + z1^2 + w1^2 = 4 * (d - x2^2) := by
    have : 4 * x2^2 ≤ 4 * d := by omega
    have h_le : x2^2 ≤ d := by omega
    omega
  have h_even := even_of_sum_three_squares_eq_four_mul y1 z1 w1 (d - x2^2) h_sum_three
  rcases h_even.1 with ⟨y2, hy2⟩
  rcases h_even.2.1 with ⟨z2, hz2⟩
  rcases h_even.2.2 with ⟨w2, hw2⟩
  have hy1_eq : y1 = 2 * y2 := by omega
  have hz1_eq : z1 = 2 * z2 := by omega
  have hw1_eq : w1 = 2 * w2 := by omega
  rw [a_pos_iff_exists]
  refine ⟨x2, y2, z2, w2, ?_, ?_⟩
  · have h_ring : 4 * x2^2 + y1^2 + z1^2 + w1^2 = 4 * (x2^2 + y2^2 + z2^2 + w2^2) := by
      rw [hy1_eq, hz1_eq, hw1_eq]
      ring
    have h_total : 4 * (x2^2 + y2^2 + z2^2 + w2^2) = 4 * d := by
      rw [← h_ring, h1]
      ring
    omega
  · dsimp
    have h_sq_s1 : 3 * x2 + 10 * y2 + 36 * z2 = s1^2 := by
      calc
        3 * x2 + 10 * y2 + 36 * z2 = 3 * x2 + 5 * y1 + 18 * z1 := by
          rw [hy1_eq, hz1_eq]
          ring
        _ = s1^2 := h2
    refine ⟨?_, ?_⟩
    · rw [h_sq_s1]
      positivity
    · have h_sqrt : (3 * x2 + 10 * y2 + 36 * z2).sqrt = s1 := by
        rw [h_sq_s1]
        exact Nat.sqrt_eq' s1
      rw [h_sqrt]
      rw [Nat.pow_two] at h_sq_s1
      exact h_sq_s1.symm


lemma a_sixteen_iff (d : ℕ) : a (16 * d) = 0 ↔ a d = 0 := by
  constructor
  · intro h
    by_contra hc
    have h_pos : a d > 0 := Nat.pos_of_ne_zero hc
    have h16 := a_pos_of_a_pos_div_sixteen d h_pos
    omega
  · intro h
    by_contra hc
    have h_pos : a (16 * d) > 0 := Nat.pos_of_ne_zero hc
    have hd := a_pos_div_sixteen d h_pos
    omega





def sol_for_n (n : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match n with
  | 1 => some (0, 0, 1, 0)
  | 2 => some (0, 0, 1, 1)
  | 3 => some (1, 1, 1, 0)
  | 4 => some (1, 1, 1, 1)
  | 5 => some (0, 0, 1, 2)
  | 6 => some (2, 1, 0, 1)
  | 7 => some (1, 1, 1, 2)
  | 9 => some (2, 1, 0, 2)
  | 10 => some (0, 0, 1, 3)
  | 11 => some (1, 1, 3, 0)
  | 12 => some (1, 1, 1, 3)
  | 13 => some (2, 3, 0, 0)
  | 14 => some (2, 1, 0, 3)
  | 15 => some (1, 1, 3, 2)
  | 17 => some (0, 0, 1, 4)
  | 18 => some (3, 0, 0, 3)
  | 19 => some (1, 1, 1, 4)
  | 20 => some (0, 0, 4, 2)
  | 21 => some (2, 1, 0, 4)
  | 22 => some (2, 3, 0, 3)
  | 23 => some (2, 3, 3, 1)
  | 25 => some (0, 0, 4, 3)
  | 26 => some (0, 0, 1, 5)
  | 27 => some (1, 1, 3, 4)
  | 28 => some (1, 1, 1, 5)
  | 29 => some (2, 3, 0, 4)
  | 30 => some (2, 1, 0, 5)
  | 31 => some (2, 1, 5, 1)
  | 33 => some (3, 4, 2, 2)
  | 34 => some (2, 1, 5, 2)
  | 35 => some (5, 1, 0, 3)
  | 36 => some (1, 1, 3, 5)
  | 37 => some (0, 0, 1, 6)
  | 38 => some (2, 3, 0, 5)
  | 39 => some (1, 1, 1, 6)
  | 41 => some (0, 0, 4, 5)
  | 42 => some (5, 1, 0, 4)
  | 43 => some (5, 1, 4, 1)
  | 44 => some (5, 3, 1, 3)
  | 45 => some (3, 0, 0, 6)
  | 46 => some (2, 1, 5, 4)
  | 47 => some (1, 1, 3, 6)
  | 49 => some (2, 3, 0, 6)
  | 50 => some (0, 0, 1, 7)
  | 51 => some (5, 1, 0, 5)
  | 52 => some (0, 0, 4, 6)
  | 53 => some (0, 4, 6, 1)
  | 54 => some (2, 1, 0, 7)
  | 55 => some (2, 1, 5, 5)
  | 56 => some (0, 4, 6, 2)
  | 57 => some (4, 4, 4, 3)
  | 58 => some (2, 3, 3, 6)
  | 59 => some (5, 3, 5, 0)
  | 60 => some (1, 1, 3, 7)
  | 61 => some (0, 4, 6, 3)
  | 62 => some (2, 3, 0, 7)
  | 63 => some (5, 3, 5, 2)
  | 65 => some (0, 0, 1, 8)
  | 66 => some (2, 1, 5, 6)
  | 67 => some (1, 1, 1, 8)
  | 68 => some (0, 4, 6, 4)
  | 69 => some (2, 1, 0, 8)
  | 70 => some (3, 0, 6, 5)
  | 71 => some (2, 3, 3, 7)
  | 72 => some (4, 6, 2, 4)
  | 73 => some (3, 0, 0, 8)
  | 74 => some (3, 4, 0, 7)
  | 75 => some (1, 1, 3, 8)
  | 76 => some (5, 7, 1, 1)
  | 77 => some (0, 4, 6, 5)
  | 78 => some (2, 3, 8, 1)
  | 79 => some (2, 1, 5, 7)
  | 81 => some (0, 0, 9, 0)
  | 82 => some (0, 0, 1, 9)
  | 83 => some (7, 4, 3, 3)
  | 84 => some (1, 1, 1, 9)
  | 85 => some (0, 0, 9, 2)
  | 86 => some (1, 7, 6, 0)
  | 87 => some (1, 7, 6, 1)
  | 88 => some (0, 4, 6, 6)
  | 89 => some (3, 4, 0, 8)
  | 90 => some (0, 0, 9, 3)
  | 91 => some (5, 1, 4, 7)
  | 92 => some (1, 1, 3, 9)
  | 93 => some (2, 3, 8, 4)
  | 94 => some (2, 1, 5, 8)
  | 95 => some (1, 7, 6, 3)
  | 97 => some (0, 0, 4, 9)
  | 98 => some (6, 7, 3, 2)
  | 99 => some (5, 3, 1, 8)
  | 100 => some (0, 10, 0, 0)
  | 101 => some (0, 0, 1, 10)
  | 102 => some (1, 7, 6, 4)
  | 103 => some (1, 1, 1, 10)
  | 104 => some (0, 10, 0, 2)
  | 105 => some (2, 1, 0, 10)
  | 106 => some (0, 0, 9, 5)
  | 107 => some (5, 1, 0, 9)
  | 108 => some (5, 3, 5, 7)
  | 109 => some (0, 10, 0, 3)
  | 110 => some (3, 4, 2, 9)
  | 111 => some (1, 1, 3, 10)
  | 113 => some (2, 3, 0, 10)
  | 114 => some (1, 7, 8, 0)
  | 115 => some (1, 7, 8, 1)
  | 116 => some (0, 0, 4, 10)
  | 117 => some (0, 0, 9, 6)
  | 118 => some (1, 7, 8, 2)
  | 119 => some (6, 1, 1, 9)
  | 120 => some (0, 4, 10, 2)
  | 121 => some (7, 6, 0, 6)
  | 122 => some (0, 0, 1, 11)
  | 123 => some (1, 7, 8, 3)
  | 124 => some (1, 1, 1, 11)
  | 125 => some (0, 4, 10, 3)
  | 126 => some (2, 1, 0, 11)
  | 127 => some (2, 7, 5, 7)
  | 129 => some (3, 4, 2, 10)
  | 130 => some (0, 0, 9, 7)
  | 131 => some (9, 1, 7, 0)
  | 132 => some (0, 4, 10, 4)
  | 133 => some (0, 4, 6, 9)
  | 134 => some (2, 3, 0, 11)
  | 135 => some (1, 7, 6, 7)
  | 136 => some (0, 10, 0, 6)
  | 137 => some (0, 0, 4, 11)
  | 138 => some (2, 7, 9, 2)
  | 139 => some (1, 7, 8, 5)
  | 140 => some (5, 3, 5, 9)
  | 141 => some (0, 4, 10, 5)
  | 142 => some (2, 7, 5, 8)
  | 143 => some (2, 3, 3, 11)
  | 145 => some (0, 0, 1, 12)
  | 146 => some (3, 4, 0, 11)
  | 147 => some (1, 1, 1, 12)
  | 148 => some (4, 4, 4, 10)
  | 149 => some (0, 10, 0, 7)
  | 150 => some (1, 7, 6, 8)
  | 151 => some (2, 1, 5, 11)
  | 152 => some (0, 4, 6, 10)
  | 153 => some (3, 0, 0, 12)
  | 154 => some (3, 0, 12, 1)
  | 155 => some (1, 1, 3, 12)
  | 156 => some (4, 6, 2, 10)
  | 157 => some (2, 3, 0, 12)
  | 158 => some (2, 3, 8, 9)
  | 159 => some (2, 7, 5, 9)
  | 161 => some (8, 4, 0, 9)
  | 162 => some (0, 0, 9, 9)
  | 163 => some (1, 7, 8, 7)
  | 164 => some (0, 10, 0, 8)
  | 165 => some (0, 4, 10, 7)
  | 166 => some (2, 3, 3, 12)
  | 167 => some (1, 7, 6, 9)
  | 168 => some (4, 10, 4, 6)
  | 169 => some (3, 0, 12, 4)
  | 170 => some (0, 0, 1, 13)
  | 171 => some (1, 13, 1, 0)
  | 172 => some (1, 1, 1, 13)
  | 173 => some (0, 4, 6, 11)
  | 174 => some (2, 1, 0, 13)
  | 175 => some (1, 13, 1, 2)
  | 177 => some (2, 3, 8, 10)
  | 178 => some (1, 7, 8, 8)
  | 179 => some (5, 3, 1, 12)
  | 180 => some (0, 4, 10, 8)
  | 181 => some (0, 0, 9, 10)
  | 182 => some (2, 3, 0, 13)
  | 183 => some (2, 1, 13, 3)
  | 184 => some (4, 10, 8, 2)
  | 185 => some (0, 0, 4, 13)
  | 186 => some (1, 7, 6, 10)
  | 187 => some (1, 13, 1, 4)
  | 188 => some (9, 1, 9, 5)
  | 189 => some (3, 0, 6, 12)
  | 190 => some (2, 1, 13, 4)
  | 191 => some (2, 3, 3, 13)
  | 193 => some (8, 10, 2, 5)
  | 194 => some (3, 4, 0, 13)
  | 195 => some (1, 7, 8, 9)
  | 196 => some (0, 4, 6, 12)
  | 197 => some (0, 0, 1, 14)
  | 198 => some (2, 3, 8, 11)
  | 199 => some (1, 1, 1, 14)
  | 200 => some (0, 10, 0, 10)
  | 201 => some (2, 1, 0, 14)
  | 202 => some (0, 0, 9, 11)
  | 203 => some (5, 3, 5, 12)
  | 204 => some (5, 3, 1, 13)
  | 205 => some (3, 0, 0, 14)
  | 206 => some (6, 7, 11, 0)
  | 207 => some (1, 1, 3, 14)
  | 209 => some (2, 3, 0, 14)
  | 210 => some (2, 1, 13, 6)
  | 211 => some (5, 1, 4, 13)
  | 212 => some (0, 0, 4, 14)
  | 213 => some (4, 10, 4, 9)
  | 214 => some (1, 7, 8, 10)
  | 215 => some (2, 7, 9, 9)
  | 216 => some (0, 4, 10, 10)
  | 217 => some (3, 0, 12, 8)
  | 218 => some (2, 3, 3, 14)
  | 219 => some (5, 3, 11, 8)
  | 220 => some (1, 13, 1, 7)
  | 221 => some (0, 4, 6, 13)
  | 222 => some (2, 7, 5, 12)
  | 223 => some (2, 1, 13, 7)
  | 225 => some (0, 0, 9, 12)
  | 226 => some (0, 0, 1, 15)
  | 227 => some (9, 1, 9, 8)
  | 228 => some (1, 1, 1, 15)
  | 229 => some (4, 10, 8, 7)
  | 230 => some (1, 7, 6, 12)
  | 231 => some (1, 15, 2, 1)
  | 232 => some (4, 10, 4, 10)
  | 233 => some (8, 12, 0, 5)
  | 234 => some (1, 15, 2, 2)
  | 235 => some (1, 7, 8, 11)
  | 236 => some (1, 1, 3, 15)
  | 237 => some (0, 4, 10, 11)
  | 238 => some (2, 1, 13, 8)
  | 239 => some (1, 15, 2, 3)
  | 241 => some (0, 0, 4, 15)
  | 242 => some (2, 3, 15, 2)
  | 243 => some (7, 4, 3, 13)
  | 244 => some (0, 10, 0, 12)
  | 245 => some (4, 6, 7, 12)
  | 246 => some (1, 15, 2, 4)
  | 247 => some (2, 3, 3, 15)
  | 248 => some (0, 4, 6, 14)
  | 249 => some (4, 6, 14, 1)
  | 250 => some (0, 0, 9, 13)
  | 251 => some (5, 1, 0, 15)
  | 252 => some (1, 13, 1, 9)
  | 253 => some (3, 0, 12, 10)
  | 254 => some (2, 3, 15, 4)
  | 255 => some (1, 7, 6, 13)
  | 257 => some (0, 0, 1, 16)
  | 258 => some (0, 16, 1, 1)
  | 259 => some (1, 1, 1, 16)
  | 260 => some (0, 0, 16, 2)
  | 261 => some (0, 16, 1, 2)
  | 262 => some (6, 9, 1, 12)
  | 263 => some (2, 3, 15, 5)
  | 264 => some (4, 6, 14, 4)
  | 265 => some (0, 0, 16, 3)
  | 266 => some (0, 16, 1, 3)
  | 267 => some (1, 1, 3, 16)
  | 268 => some (8, 10, 2, 10)
  | 269 => some (0, 10, 0, 13)
  | 270 => some (3, 0, 6, 15)
  | 271 => some (1, 13, 1, 10)
  | 273 => some (0, 16, 1, 4)
  | 274 => some (2, 1, 13, 10)
  | 275 => some (9, 1, 7, 12)
  | 276 => some (4, 4, 12, 10)
  | 277 => some (0, 0, 9, 14)
  | 278 => some (2, 3, 3, 16)
  | 279 => some (1, 15, 2, 7)
  | 280 => some (4, 10, 8, 10)
  | 281 => some (0, 0, 16, 5)
  | 282 => some (0, 16, 1, 5)
  | 283 => some (1, 7, 8, 13)
  | 284 => some (4, 6, 14, 6)
  | 285 => some (0, 4, 10, 13)
  | 286 => some (2, 1, 5, 16)
  | 287 => some (2, 3, 15, 7)
  | 289 => some (8, 10, 2, 11)
  | 290 => some (0, 0, 1, 17)
  | 291 => some (1, 1, 17, 0)
  | 292 => some (0, 0, 16, 6)
  | 293 => some (0, 16, 1, 6)
  | 294 => some (1, 15, 2, 8)
  | 295 => some (1, 1, 17, 2)
  | 296 => some (0, 10, 0, 14)
  | 297 => some (3, 0, 12, 12)
  | 298 => some (3, 0, 0, 17)
  | 299 => some (1, 15, 8, 3)
  | 300 => some (1, 1, 3, 17)
  | 301 => some (3, 0, 6, 16)
  | 302 => some (2, 3, 0, 17)
  | 303 => some (2, 7, 5, 15)
  | 305 => some (0, 0, 4, 17)
  | 306 => some (0, 0, 9, 15)
  | 307 => some (1, 1, 17, 4)
  | 308 => some (0, 4, 6, 16)
  | 309 => some (14, 3, 2, 10)
  | 310 => some (1, 7, 8, 14)
  | 311 => some (1, 7, 6, 15)
  | 312 => some (0, 4, 10, 14)
  | 313 => some (8, 10, 10, 7)
  | 314 => some (3, 4, 0, 17)
  | 315 => some (1, 13, 1, 12)
  | 316 => some (1, 1, 17, 5)
  | 317 => some (3, 4, 16, 6)
  | 318 => some (2, 1, 13, 12)
  | 319 => some (2, 1, 5, 17)
  | 321 => some (0, 16, 1, 8)
  | 322 => some (3, 0, 12, 13)
  | 323 => some (7, 16, 3, 3)
  | 324 => some (4, 10, 8, 12)
  | 325 => some (0, 0, 1, 18)
  | 326 => some (1, 15, 8, 6)
  | 327 => some (1, 1, 1, 18)
  | 328 => some (4, 10, 4, 14)
  | 329 => some (2, 1, 0, 18)
  | 330 => some (1, 15, 2, 10)
  | 331 => some (5, 1, 4, 17)
  | 332 => some (9, 1, 9, 13)
  | 333 => some (2, 3, 8, 16)
  | 334 => some (2, 7, 5, 16)
  | 335 => some (1, 1, 3, 18)
  | 337 => some (0, 0, 9, 16)
  | 338 => some (0, 16, 1, 9)
  | 339 => some (1, 7, 8, 15)
  | 340 => some (0, 0, 4, 18)
  | 341 => some (0, 4, 6, 17)
  | 342 => some (1, 7, 6, 16)
  | 343 => some (2, 1, 13, 13)
  | 344 => some (0, 18, 4, 2)
  | 345 => some (3, 4, 16, 8)
  | 346 => some (0, 16, 9, 3)
  | 347 => some (13, 13, 0, 3)
  | 348 => some (4, 6, 14, 10)
  | 349 => some (0, 18, 4, 3)
  | 350 => some (3, 18, 1, 4)
  | 351 => some (1, 15, 2, 11)
  | 353 => some (0, 16, 9, 4)
  | 354 => some (1, 15, 8, 8)
  | 355 => some (1, 1, 17, 8)
  | 356 => some (0, 0, 16, 10)
  | 357 => some (0, 10, 16, 1)
  | 358 => some (6, 13, 3, 12)
  | 359 => some (2, 3, 15, 11)
  | 360 => some (0, 10, 16, 2)
  | 361 => some (6, 1, 18, 0)
  | 362 => some (0, 0, 1, 19)
  | 363 => some (5, 7, 15, 8)
  | 364 => some (1, 1, 1, 19)
  | 365 => some (0, 10, 16, 3)
  | 366 => some (2, 1, 0, 19)
  | 367 => some (1, 13, 1, 14)
  | 369 => some (2, 19, 0, 2)
  | 370 => some (0, 0, 9, 17)
  | 371 => some (1, 15, 8, 9)
  | 372 => some (0, 4, 10, 16)
  | 373 => some (0, 16, 9, 6)
  | 374 => some (1, 15, 2, 12)
  | 375 => some (1, 7, 6, 17)
  | 376 => some (0, 4, 6, 18)
  | 377 => some (0, 0, 4, 19)
  | 378 => some (0, 16, 1, 11)
  | 379 => some (5, 13, 4, 13)
  | 380 => some (4, 6, 2, 18)
  | 381 => some (0, 10, 16, 5)
  | 382 => some (2, 3, 15, 12)
  | 383 => some (2, 3, 3, 19)
  | 385 => some (8, 4, 17, 4)
  | 386 => some (0, 16, 9, 7)
  | 387 => some (5, 1, 0, 19)
  | 388 => some (4, 10, 4, 16)
  | 389 => some (0, 10, 0, 17)
  | 390 => some (1, 15, 8, 10)
  | 391 => some (1, 1, 17, 10)
  | 392 => some (0, 10, 16, 6)
  | 393 => some (8, 10, 2, 15)
  | 394 => some (7, 10, 14, 7)
  | 395 => some (5, 3, 19, 0)
  | 396 => some (1, 13, 1, 15)
  | 397 => some (6, 1, 18, 6)
  | 398 => some (2, 13, 15, 0)
  | 399 => some (1, 15, 2, 13)
  | 401 => some (0, 0, 1, 20)
  | 402 => some (2, 7, 5, 18)
  | 403 => some (1, 1, 1, 20)
  | 404 => some (0, 18, 4, 8)
  | 405 => some (0, 0, 9, 18)
  | 406 => some (3, 0, 6, 19)
  | 407 => some (2, 3, 15, 13)
  | 408 => some (8, 10, 10, 12)
  | 409 => some (3, 0, 0, 20)
  | 410 => some (1, 7, 6, 18)
  | 411 => some (1, 1, 3, 20)
  | 412 => some (1, 1, 17, 11)
  | 413 => some (0, 4, 6, 19)
  | 414 => some (2, 13, 15, 4)
  | 415 => some (3, 18, 1, 9)
  | 417 => some (4, 6, 2, 19)
  | 418 => some (0, 16, 9, 9)
  | 419 => some (9, 1, 9, 16)
  | 420 => some (0, 10, 16, 8)
  | 421 => some (0, 18, 4, 9)
  | 422 => some (2, 3, 3, 20)
  | 423 => some (2, 7, 9, 17)
  | 424 => some (0, 10, 0, 18)
  | 425 => some (0, 0, 16, 13)
  | 426 => some (0, 16, 1, 13)
  | 427 => some (1, 13, 1, 16)
  | 428 => some (9, 13, 13, 3)
  | 429 => some (2, 19, 0, 8)
  | 430 => some (2, 1, 5, 20)
  | 431 => some (3, 18, 7, 7)
  | 433 => some (2, 19, 8, 2)
  | 434 => some (1, 15, 8, 12)
  | 435 => some (1, 1, 17, 12)
  | 436 => some (4, 10, 8, 16)
  | 437 => some (0, 10, 16, 9)
  | 438 => some (1, 7, 8, 18)
  | 439 => some (2, 7, 5, 19)
  | 440 => some (0, 4, 10, 18)
  | 441 => some (6, 1, 2, 20)
  | 442 => some (0, 0, 1, 21)
  | 443 => some (5, 7, 15, 12)
  | 444 => some (1, 1, 1, 21)
  | 445 => some (0, 18, 11, 0)
  | 446 => some (0, 18, 11, 1)
  | 447 => some (1, 7, 6, 19)
  | 449 => some (0, 18, 11, 2)
  | 450 => some (3, 0, 0, 21)
  | 451 => some (7, 16, 5, 11)
  | 452 => some (0, 0, 16, 14)
  | 453 => some (0, 16, 1, 14)
  | 454 => some (0, 18, 11, 3)
  | 455 => some (1, 15, 2, 15)
  | 456 => some (0, 10, 16, 10)
  | 457 => some (0, 0, 4, 21)
  | 458 => some (0, 16, 9, 11)
  | 459 => some (1, 15, 8, 13)
  | 460 => some (1, 1, 17, 13)
  | 461 => some (0, 10, 0, 19)
  | 462 => some (0, 10, 19, 1)
  | 463 => some (2, 1, 13, 17)
  | 465 => some (0, 10, 19, 2)
  | 466 => some (3, 4, 0, 21)
  | 467 => some (5, 1, 0, 21)
  | 468 => some (4, 16, 14, 0)
  | 469 => some (4, 10, 8, 17)
  | 470 => some (0, 10, 19, 3)
  | 471 => some (2, 1, 5, 21)
  | 472 => some (4, 16, 14, 2)
  | 473 => some (3, 0, 20, 8)
  | 474 => some (7, 4, 3, 20)
  | 475 => some (1, 7, 8, 19)
  | 476 => some (5, 3, 1, 21)
  | 477 => some (0, 4, 10, 19)
  | 478 => some (2, 7, 5, 20)
  | 479 => some (2, 13, 15, 9)
  | 481 => some (0, 0, 9, 20)
  | 482 => some (0, 16, 1, 15)
  | 483 => some (1, 15, 16, 1)
  | 484 => some (0, 18, 4, 12)
  | 485 => some (0, 0, 1, 22)
  | 486 => some (0, 10, 19, 5)
  | 487 => some (1, 1, 1, 22)
  | _ => none

def verify_sol (n : ℕ) : Bool :=
  match sol_for_n n with
  | some (x, y, z, w) =>
    let c := 3 * x + 10 * y + 36 * z
    let c_is_sq := (List.range 35).any (fun s => s * s == c)
    (x^2 + y^2 + z^2 + w^2 == n) && (c > 0) && c_is_sq
  | none => true

def check_sol_none (n : ℕ) : Bool :=
  match sol_for_n n with
  | none => (n == 0) || (n % 16 == 0) || (n == 8) || (n == 24) || (n == 40) || (n == 488)
  | some _ => true

lemma verify_all_sol : (List.range 489).all verify_sol = true := by decide
lemma check_sol_none_all : (List.range 489).all check_sol_none = true := by decide



lemma a_pos_of_sol_some (n : ℕ) (x y z w : ℕ) (h_sol : sol_for_n n = some (x, y, z, w)) (h_verify : verify_sol n = true) : a n > 0 := by
  dsimp [verify_sol] at h_verify
  rw [h_sol] at h_verify
  dsimp at h_verify
  rw [Bool.and_eq_true, Bool.and_eq_true] at h_verify
  rcases h_verify with ⟨⟨h_sum_eq, h_c_pos⟩, h_c_sq⟩
  rw [beq_iff_eq] at h_sum_eq
  rw [decide_eq_true_iff] at h_c_pos
  rw [a_pos_iff_exists]
  refine ⟨x, y, z, w, h_sum_eq, ?_⟩
  dsimp
  refine ⟨h_c_pos, ?_⟩
  rw [List.any_eq_true] at h_c_sq
  rcases h_c_sq with ⟨s, hs_mem, hs_sq⟩
  rw [beq_iff_eq] at hs_sq
  have h_sqrt : (3 * x + 10 * y + 36 * z).sqrt = s := by
    rw [← hs_sq]
    rw [← Nat.pow_two]
    exact Nat.sqrt_eq' s
  rw [h_sqrt]
  exact hs_sq

lemma a_zero_impl_le_488 (n : ℕ) (hn : n > 0) (h16 : ¬ 16 ∣ n) (hn489 : n < 489) (h_zero : a n = 0) :
    n = 8 ∨ n = 24 ∨ n = 40 ∨ n = 488 := by
  have h_none : sol_for_n n = none := by
    by_contra hc
    obtain ⟨⟨x, y, z, w⟩, h_sol⟩ := Option.ne_none_iff_exists.mp hc
    have h_verify : verify_sol n = true := by
      have h_all := verify_all_sol
      rw [List.all_eq_true] at h_all
      apply h_all
      rw [List.mem_range]
      exact hn489
    have h_pos := a_pos_of_sol_some n x y z w h_sol.symm h_verify
    omega
  have h_check : check_sol_none n = true := by
    have h_all := check_sol_none_all
    rw [List.all_eq_true] at h_all
    apply h_all
    rw [List.mem_range]
    exact hn489
  dsimp [check_sol_none] at h_check
  rw [h_none] at h_check
  dsimp at h_check
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h_check
  rcases h_check with (((((h0 | h16') | h8) | h24) | h40) | h488)
  · rw [beq_iff_eq] at h0
    omega
  · rw [beq_iff_eq] at h16'
    have : 16 ∣ n := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h16'
    contradiction
  · rw [beq_iff_eq] at h8; left; exact h8
  · rw [beq_iff_eq] at h24; right; left; exact h24
  · rw [beq_iff_eq] at h40; right; right; left; exact h40
  · rw [beq_iff_eq] at h488; right; right; right; exact h488


lemma a_zero_impl (n : ℕ) (hn : n > 0) (h_zero : a n = 0) :
    ∃ k : ℕ, ∃ m : ℕ, (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h16 : 16 ∣ n
  · rcases h16 with ⟨d, rfl⟩
    have h_d_pos : d > 0 := by
      by_contra hc
      have : d = 0 := by omega
      subst this
      omega
    have h_zero' : a d = 0 := by
      have h_mul : a (16 * d) = 0 := h_zero
      rwa [a_sixteen_iff] at h_mul
    have ih_d := ih d (by omega) h_d_pos h_zero'
    rcases ih_d with ⟨k, m, hm, rfl⟩
    refine ⟨k + 1, m, hm, ?_⟩
    calc
      16 * (2^(4 * k + 3) * m) = 2^4 * 2^(4 * k + 3) * m := by ring
      _ = 2^(4 * (k + 1) + 3) * m := by ring_nf
  · by_cases hn489 : n < 489
    · have h_cases := a_zero_impl_le_488 n hn h16 hn489 h_zero
      rcases h_cases with rfl | rfl | rfl | rfl
      · refine ⟨0, 1, by decide, by rfl⟩
      · refine ⟨0, 3, by decide, by rfl⟩
      · refine ⟨0, 5, by decide, by rfl⟩
      · refine ⟨0, 61, by decide, by rfl⟩
    · sorry

/-- Conjecture: a(n) > 0 if n is not divisible by 8. Moreover, a(n) = 0 if and only if n has the form $2^{4k+3} \cdot m$ ($k \ge 0$ and $m \in \{1, 3, 5, 61\}$). -/
theorem oeis_338019_conjecture_0 (n : ℕ) (h_n_pos : n > 0) :
  (a n = 0 ↔ ∃ k : ℕ, ∃ m : ℕ,
    (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m) ∧
  (¬ (8 ∣ n) → a n > 0) := by
  have h1 : a n = 0 ↔ ∃ k : ℕ, ∃ m : ℕ, (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m := by
    constructor
    · intro h_zero
      exact a_zero_impl n h_n_pos h_zero
    · rintro ⟨k, m, hm, rfl⟩
      by_contra h_zero
      have h_pos : a (2 ^ (4 * k + 3) * m) > 0 := Nat.pos_of_ne_zero h_zero
      rw [a_pos_iff_exists] at h_pos
      rcases h_pos with ⟨x, y, z, w, h_sum, h_c_pos, h_c_sq⟩
      let s := (3 * x + 10 * y + 36 * z).sqrt
      have h_c_eq : 3 * x + 10 * y + 36 * z = s^2 := by
        rw [Nat.pow_two]
        exact h_c_sq.symm
      have h_s : s > 0 := by
        by_contra hc
        have : s = 0 := by omega
        rw [this] at h_c_eq
        simp at h_c_eq
        omega
      exact no_solution_induction k m hm x y z w h_sum s h_c_eq h_s
  refine ⟨h1, ?_⟩
  intro h8
  by_contra h_zero
  have h_zero' : a n = 0 := by omega
  have h_exists := h1.mp h_zero'
  rcases h_exists with ⟨k, m, h_m, rfl⟩
  apply h8
  have h_pow : 2^(4 * k + 3) * m = 8 * (2^(4 * k) * m) := by ring
  rw [h_pow]
  exact dvd_mul_right 8 (2 ^ (4 * k) * m)


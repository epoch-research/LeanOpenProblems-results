import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A282091: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + y - z$ a cube of an integer,
where $x,y,z,w$ are nonnegative integers with $x \ge y \le z$ and $x \equiv y \pmod 2$.
-/

-- Helper predicate for the core number theory constraint
def is_perfect_cube (m : ℤ) : Prop := ∃ k : ℤ, m = k ^ 3

-- We assert this is decidable using classical logic, as it is true constructively.
noncomputable instance decidable_is_perfect_cube (m : ℤ) : Decidable (is_perfect_cube m) :=
  Classical.dec _

noncomputable def A282091 (n : ℕ) : ℕ :=
  let B := n.sqrt + 1
  let R := Finset.range B

  let is_square (m : ℕ) : Prop := m.sqrt * m.sqrt = m

  -- Search space for (x, y, z) in N^3
  let search_space := R.product R |>.product R

  search_space.filter (fun p : (ℕ × ℕ) × ℕ =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd

    let sum_xyz_sq := x^2 + y^2 + z^2
    let w_sq := n - sum_xyz_sq

    -- 1. Ensure $w^2 \ge 0$ (i.e., sum_xyz_sq ≤ n)
    sum_xyz_sq ≤ n ∧
    -- 2. Ensure $w^2$ is a perfect square, implicitly defining $w \in \mathbb{N}$
    is_square w_sq ∧

    -- 3. Order constraints: $x \ge y \le z$
    x ≥ y ∧ y ≤ z ∧

    -- 4. Parity constraint: $x \equiv y \pmod 2$
    (x % 2 = y % 2) ∧

    -- 5. Cube constraint on $x + y - z$
    is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ))
  )
  |>.card

-- Base Case Proof for Part 1 (n = 0)
theorem part1_zero : A282091 0 > 0 := by
  dsimp [A282091]
  apply Finset.card_pos.mpr
  use ((0, 0), 0)
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · -- ((0,0),0) is in search_space
    rw [Finset.mem_product, Finset.mem_product]
    refine ⟨⟨by simp, by simp⟩, by simp⟩
  · -- conditions hold
    refine ⟨by decide, ?_⟩
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    use 0
    rfl

-- Base Case Proof for Part 2 (n = 0)
theorem part2_zero : ∃ x y z w : ℕ,
    0 = x^2 + y^2 + z^2 + w^2 ∧
    x ≤ y ∧ y ≤ z ∧
    is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ)) := by
  use 0, 0, 0, 0
  refine ⟨by rfl, by decide, by decide, ?_⟩
  use 0
  rfl

-- 64-scaling lemma for Part 2
lemma reduction_p2 (k : ℕ) (x' y' z' w' : ℕ) (c' : ℤ)
    (h_eq : k = x'^2 + y'^2 + z'^2 + w'^2)
    (h1 : x' ≤ y') (h2 : y' ≤ z')
    (h_cube : (x' : ℤ) + (y' : ℤ) - (z' : ℤ) = c'^3) :
    ∃ x y z w : ℕ,
      64 * k = x^2 + y^2 + z^2 + w^2 ∧
      x ≤ y ∧ y ≤ z ∧
      is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ)) := by
  use 8 * x', 8 * y', 8 * z', 8 * w'
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sum of squares
    rw [h_eq]
    ring
  · -- x <= y
    omega
  · -- y <= z
    omega
  · -- perfect cube
    use 2 * c'
    push_cast
    have h_calc : (8 * (x' : ℤ) + 8 * (y' : ℤ) - 8 * (z' : ℤ)) = 8 * ((x' : ℤ) + (y' : ℤ) - (z' : ℤ)) := by ring
    rw [h_calc, h_cube]
    ring


-- 64-scaling lemma for Part 1
lemma reduction_p1 (k : ℕ) (x' y' z' w' : ℕ) (c' : ℤ)
    (h_eq : k = x'^2 + y'^2 + z'^2 + w'^2)
    (h1 : x' ≥ y') (h2 : y' ≤ z')
    (h_cube : (x' : ℤ) + (y' : ℤ) - (z' : ℤ) = c'^3) :
    ∃ x y z w : ℕ,
      64 * k = x^2 + y^2 + z^2 + w^2 ∧
      x ≥ y ∧ y ≤ z ∧
      (x % 2 = y % 2) ∧
      is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ)) := by
  use 8 * x', 8 * y', 8 * z', 8 * w'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- sum of squares
    rw [h_eq]
    ring
  · -- x >= y
    omega
  · -- y <= z
    omega
  · -- parity
    omega
  · -- perfect cube
    use 2 * c'
    push_cast
    have h_calc : (8 * (x' : ℤ) + 8 * (y' : ℤ) - 8 * (z' : ℤ)) = 8 * ((x' : ℤ) + (y' : ℤ) - (z' : ℤ)) := by ring
    rw [h_calc, h_cube]
    ring


lemma exists_sorted_four_squares (n : ℕ) :
    ∃ x y z w : ℕ, n = x^2 + y^2 + z^2 + w^2 ∧ x ≤ y ∧ y ≤ z ∧ z ≤ w := by
  rcases Nat.sum_four_squares n with ⟨a, b, c, d, h⟩
  rcases le_total a b with h_a_b | h_b_a
  · rcases le_total a c with h_a_c | h_c_a
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b c with h_b_c | h_c_b
        · rcases le_total b d with h_b_d | h_d_b
          · rcases le_total c d with h_c_d | h_d_c
            · use a, b, c, d
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use a, b, d, c
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · use a, d, b, c
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · rcases le_total b d with h_b_d | h_d_b
          · use a, c, b, d
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · rcases le_total c d with h_c_d | h_d_c
            · use a, c, d, b
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use a, d, c, b
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b c with h_b_c | h_c_b
        · use d, a, b, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, a, c, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b d with h_b_d | h_d_b
        · use c, a, b, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use c, a, d, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total c d with h_c_d | h_d_c
        · use c, d, a, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, c, a, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
  · rcases le_total a c with h_a_c | h_c_a
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total c d with h_c_d | h_d_c
        · use b, a, c, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use b, a, d, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b d with h_b_d | h_d_b
        · use b, d, a, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, b, a, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b c with h_b_c | h_c_b
        · use b, c, a, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use c, b, a, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b c with h_b_c | h_c_b
        · rcases le_total b d with h_b_d | h_d_b
          · rcases le_total c d with h_c_d | h_d_c
            · use b, c, d, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use b, d, c, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · use d, b, c, a
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · rcases le_total b d with h_b_d | h_d_b
          · use c, b, d, a
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · rcases le_total c d with h_c_d | h_d_c
            · use c, d, b, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use d, c, b, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩

lemma part2_non_64 (n : ℕ) (hn : n > 0) (h_not : ¬ 64 ∣ n) :
    ∃ x y z w : ℕ,
      n = x^2 + y^2 + z^2 + w^2 ∧
      x ≤ y ∧ y ≤ z ∧
      is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ)) := by
  sorry

lemma part1_non_64 (n : ℕ) (hn : n > 0) (h_not : ¬ 64 ∣ n) :
    A282091 n > 0 := by
  sorry

theorem oeis_282091_conjecture_0 :
  -- Part 1: a(n) > 0
  (∀ n : ℕ, A282091 n > 0) ∧
  -- Part 2: Existence with different constraints (x ≤ y ≤ z)
  (∀ n : ℕ, ∃ x y z w : ℕ,
      n = x^2 + y^2 + z^2 + w^2 ∧
      x ≤ y ∧ y ≤ z ∧
      is_perfect_cube ((x : ℤ) + (y : ℤ) - (z : ℤ))) :=
by
  refine ⟨?_, ?_⟩
  · -- Part 1
    intro n
    induction' n using Nat.strong_induction_on with n IH
    rcases n with rfl | n
    · exact part1_zero
    · have hn : n + 1 > 0 := by omega
      by_cases h_div : 64 ∣ n + 1
      · rcases h_div with ⟨k, hk⟩
        have h_k_lt : k < n + 1 := by
          have : n + 1 > 0 := by omega
          omega
        have h_sol_k := IH k h_k_lt
        -- a(k) > 0 means there is at least one element in the Finset
        -- Let us extract a solution from a(k) > 0
        dsimp [A282091] at h_sol_k
        obtain ⟨p, hp⟩ := Finset.card_pos.mp h_sol_k
        rw [Finset.mem_filter] at hp
        let x' := p.1.1
        let y' := p.1.2
        let z' := p.2
        let sum_sq := x'^2 + y'^2 + z'^2
        let w'_sq := k - sum_sq
        have h_sum_le : sum_sq ≤ k := hp.2.1
        have h_is_sq : (k - sum_sq).sqrt * (k - sum_sq).sqrt = k - sum_sq := hp.2.2.1
        have h_x_ge_y : x' ≥ y' := hp.2.2.2.1
        have h_y_le_z : y' ≤ z' := hp.2.2.2.2.1
        have h_parity : x' % 2 = y' % 2 := hp.2.2.2.2.2.1
        have h_cube : is_perfect_cube ((x' : ℤ) + (y' : ℤ) - (z' : ℤ)) := hp.2.2.2.2.2.2
        obtain ⟨c', h_c'⟩ := h_cube
        -- We can scale this solution
        have h_eq_k : k = x'^2 + y'^2 + z'^2 + (k - sum_sq).sqrt ^ 2 := by
          have h_pow : (k - sum_sq).sqrt ^ 2 = (k - sum_sq).sqrt * (k - sum_sq).sqrt := by ring
          rw [h_pow, h_is_sq]
          omega
        obtain ⟨x, y, z, w, h_eq_64k, h1, h2, h3, h4⟩ := reduction_p1 k x' y' z' (k - sum_sq).sqrt c' h_eq_k h_x_ge_y h_y_le_z h_c'
        dsimp [A282091]
        apply Finset.card_pos.mpr
        use ((x, y), z)
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · -- ((x, y), z) is in search space
          rw [Finset.mem_product, Finset.mem_product]
          have h_x_le : x < (n + 1).sqrt + 1 := by
            have h_eq_x_sq : x^2 = x * x := by ring
            have h_eq_y_sq : y^2 = y * y := by ring
            have h_eq_z_sq : z^2 = z * z := by ring
            have h_eq_w_sq : w^2 = w * w := by ring
            have h_sum : x^2 + y^2 + z^2 + w^2 = n + 1 := by
              rw [← h_eq_64k, hk]
            have h_xx_le : x * x ≤ n + 1 := by
              rw [h_eq_x_sq, h_eq_y_sq, h_eq_z_sq, h_eq_w_sq] at h_sum
              omega
            have : x ≤ (n + 1).sqrt := Nat.le_sqrt.mpr h_xx_le
            omega
          have h_y_le : y < (n + 1).sqrt + 1 := by
            have h_eq_x_sq : x^2 = x * x := by ring
            have h_eq_y_sq : y^2 = y * y := by ring
            have h_eq_z_sq : z^2 = z * z := by ring
            have h_eq_w_sq : w^2 = w * w := by ring
            have h_sum : x^2 + y^2 + z^2 + w^2 = n + 1 := by
              rw [← h_eq_64k, hk]
            have h_yy_le : y * y ≤ n + 1 := by
              rw [h_eq_x_sq, h_eq_y_sq, h_eq_z_sq, h_eq_w_sq] at h_sum
              omega
            have : y ≤ (n + 1).sqrt := Nat.le_sqrt.mpr h_yy_le
            omega
          have h_z_le : z < (n + 1).sqrt + 1 := by
            have h_eq_x_sq : x^2 = x * x := by ring
            have h_eq_y_sq : y^2 = y * y := by ring
            have h_eq_z_sq : z^2 = z * z := by ring
            have h_eq_w_sq : w^2 = w * w := by ring
            have h_sum : x^2 + y^2 + z^2 + w^2 = n + 1 := by
              rw [← h_eq_64k, hk]
            have h_zz_le : z * z ≤ n + 1 := by
              rw [h_eq_x_sq, h_eq_y_sq, h_eq_z_sq, h_eq_w_sq] at h_sum
              omega
            have : z ≤ (n + 1).sqrt := Nat.le_sqrt.mpr h_zz_le
            omega
          exact ⟨⟨by simp [h_x_le], by simp [h_y_le]⟩, by simp [h_z_le]⟩
        · -- conditions hold
          have h_sum_le : x^2 + y^2 + z^2 ≤ n + 1 := by omega
          refine ⟨h_sum_le, ?_⟩
          have h_is_sq : (n + 1 - (x^2 + y^2 + z^2)).sqrt * (n + 1 - (x^2 + y^2 + z^2)).sqrt = n + 1 - (x^2 + y^2 + z^2) := by
            have h_eq_w_sq : w^2 = w * w := by ring
            have : n + 1 - (x^2 + y^2 + z^2) = w * w := by
              have : x^2 + y^2 + z^2 + w^2 = n + 1 := by
                rw [← h_eq_64k, hk]
              rw [← h_eq_w_sq]
              omega
            rw [this, Nat.sqrt_eq w]
          refine ⟨h_is_sq, h1, h2, h3, h4⟩
      · exact part1_non_64 (n + 1) hn h_div
  · -- Part 2
    intro n
    induction' n using Nat.strong_induction_on with n IH
    rcases n with rfl | n
    · exact part2_zero
    · have hn : n + 1 > 0 := by omega
      by_cases h_div : 64 ∣ n + 1
      · rcases h_div with ⟨k, hk⟩
        have h_k_lt : k < n + 1 := by
          have : n + 1 > 0 := by omega
          omega
        have h_sol_k := IH k h_k_lt
        obtain ⟨x', y', z', w', h_eq, h1, h2, h_cube⟩ := h_sol_k
        obtain ⟨c', h_c'⟩ := h_cube
        obtain ⟨x, y, z, w, h_eq_64k, h1_new, h2_new, h_cube_new⟩ := reduction_p2 k x' y' z' w' c' h_eq h1 h2 h_c'
        use x, y, z, w
        refine ⟨by omega, h1_new, h2_new, h_cube_new⟩
      · exact part2_non_64 (n + 1) hn h_div







import FormalConjectures.Util.ProblemImports

set_option warn.sorry true

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

lemma family_y1_identity (z : ℕ) :
    (4 * z ^ 2 + 1) ^ 2 + 8 * 1 ^ 2 + 16 * z ^ 2 = (4 * z ^ 2 + 3) ^ 2 := by
  ring

lemma family_y1_is_square (z : ℕ) :
    let x := 4 * z ^ 2 + 1
    let y := 1
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro x y
  have h : x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (4 * z ^ 2 + 3) ^ 2 := by
    dsimp [x, y]
    exact family_y1_identity z
  rw [h]
  rw [Nat.sqrt_eq']
  ring

lemma family1_is_square (y z : ℕ) (h : 2 ≤ y^2 + 2 * z^2) :
    let x := y^2 + 2 * z^2 - 2
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro x
  have hx : y^2 + 2 * z^2 = x + 2 := (Nat.sub_add_cancel h).symm
  have h1 : x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (x + 4) ^ 2 := by
    calc
      x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = x ^ 2 + 8 * (y ^ 2 + 2 * z ^ 2) := by ring
      _ = x ^ 2 + 8 * (x + 2) := by rw [hx]
      _ = (x + 4) ^ 2 := by ring
  rw [h1]
  rw [Nat.sqrt_eq']
  ring

/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem integer_identity (y z : ℤ) :
  (y ^ 2 + 2 * z ^ 2 - 2) ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (y ^ 2 + 2 * z ^ 2 + 2) ^ 2 := by
  ring

lemma mem_search_space_of_sum_squares_eq {n x y z w : ℕ} (h : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    (((x, y), z), w) ∈ (((Finset.range (n.sqrt + 1)).product (Finset.range (n.sqrt + 1))).product (Finset.range (n.sqrt + 1))).product (Finset.range (n.sqrt + 1)) := by
  have h_le_x : x ^ 2 ≤ n := by
    omega
  have h_le_y : y ^ 2 ≤ n := by
    omega
  have h_le_z : z ^ 2 ≤ n := by
    omega
  have h_le_w : w ^ 2 ≤ n := by
    omega
  rw [← Nat.le_sqrt'] at h_le_x h_le_y h_le_z h_le_w
  have hx : x < n.sqrt + 1 := by omega
  have hy : y < n.sqrt + 1 := by omega
  have hz : z < n.sqrt + 1 := by omega
  have hw : w < n.sqrt + 1 := by omega
  rw [← Finset.mem_range] at hx hy hz hw
  exact Finset.mk_mem_product (Finset.mk_mem_product (Finset.mk_mem_product hx hy) hz) hw

#eval A271510 2
#eval A271510 10
#eval A271510 50
#eval A271510 100


lemma family_zero_is_square (x : ℕ) :
    let y := 0
    let z := 0
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro y z
  dsimp [y, z]
  rw [Nat.sqrt_eq']
  ring

lemma family_diag_is_square (x : ℕ) :
    let y := x
    let z := 0
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro y z
  dsimp [y, z]
  have h : x ^ 2 + 8 * x ^ 2 = (3 * x) ^ 2 := by ring
  rw [h]
  rw [Nat.sqrt_eq']
  ring

lemma family_diag_z_is_square (x : ℕ) :
    let y := x
    let z := x
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro y z
  dsimp [y, z]
  have h : x ^ 2 + 8 * x ^ 2 + 16 * x ^ 2 = (5 * x) ^ 2 := by ring
  rw [h]
  rw [Nat.sqrt_eq']
  ring

lemma A271510_pos_of_exists (n : ℕ) (x y z w : ℕ)
    (h_sum : x^2 + y^2 + z^2 + w^2 = n)
    (h_le : y ≤ x)
    (h_sq : (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2) :
    0 < A271510 n := by
  dsimp [A271510]
  apply Finset.card_pos.mpr
  use (((x, y), z), w)
  rw [Finset.mem_filter]
  refine ⟨mem_search_space_of_sum_squares_eq h_sum, ?_⟩
  refine ⟨h_sum, h_le, h_sq⟩


lemma sqrt_four_mul_of_is_square (A : ℕ) (hA : A.sqrt * A.sqrt = A) :
    (4 * A).sqrt = 2 * A.sqrt := by
  have h1 : 4 * A = (2 * A.sqrt) ^ 2 := by
    calc
      4 * A = 4 * (A.sqrt * A.sqrt) := by rw [hA]
      _ = (2 * A.sqrt) ^ 2 := by ring
  rw [h1]
  rw [Nat.sqrt_eq']

lemma A271510_exists_of_pos (n : ℕ) (h : 0 < A271510 n) :
    ∃ x y z w, x^2 + y^2 + z^2 + w^2 = n ∧ y ≤ x ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2 := by
  dsimp [A271510] at h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter] at hp
  use p.fst.fst.fst, p.fst.fst.snd, p.fst.snd, p.snd
  exact hp.2

lemma A271510_scale (n : ℕ) (h : 0 < A271510 n) : 0 < A271510 (4 * n) := by
  obtain ⟨x, y, z, w, h_sum, h_le, h_sq⟩ := A271510_exists_of_pos n h
  apply A271510_pos_of_exists (4 * n) (2 * x) (2 * y) (2 * z) (2 * w)
  · calc
      (2 * x) ^ 2 + (2 * y) ^ 2 + (2 * z) ^ 2 + (2 * w) ^ 2 = 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
      _ = 4 * n := by rw [h_sum]
  · omega
  · have h_sq_four : (2 * x) ^ 2 + 8 * (2 * y) ^ 2 + 16 * (2 * z) ^ 2 = 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by ring
    rw [h_sq_four]
    have h_sqrt : (4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)).sqrt = 2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt := by
      apply sqrt_four_mul_of_is_square
      exact h_sq
    rw [h_sqrt]
    calc
      (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) * (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) = 4 * ((x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) := by ring
      _ = 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by rw [h_sq]

lemma sqrt_sq_mul_of_is_square (M A : ℕ) (hA : A.sqrt * A.sqrt = A) :
    (M^2 * A).sqrt = M * A.sqrt := by
  have h1 : M^2 * A = (M * A.sqrt) ^ 2 := by
    calc
      M^2 * A = M^2 * (A.sqrt * A.sqrt) := by rw [hA]
      _ = (M * A.sqrt) ^ 2 := by ring
  rw [h1]
  rw [Nat.sqrt_eq']

lemma A271510_scale_square (n M : ℕ) (h : 0 < A271510 n) : 0 < A271510 (M^2 * n) := by
  obtain ⟨x, y, z, w, h_sum, h_le, h_sq⟩ := A271510_exists_of_pos n h
  apply A271510_pos_of_exists (M^2 * n) (M * x) (M * y) (M * z) (M * w)
  · calc
      (M * x) ^ 2 + (M * y) ^ 2 + (M * z) ^ 2 + (M * w) ^ 2 = M^2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
      _ = M^2 * n := by rw [h_sum]
  · exact Nat.mul_le_mul_left M h_le
  · have h_sq_M : (M * x) ^ 2 + 8 * (M * y) ^ 2 + 16 * (M * z) ^ 2 = M^2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by ring
    rw [h_sq_M]
    have h_sqrt : (M^2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)).sqrt = M * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt := by
      apply sqrt_sq_mul_of_is_square
      exact h_sq
    rw [h_sqrt]
    calc
      (M * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) * (M * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) = M^2 * ((x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) := by ring
      _ = M^2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by rw [h_sq]

lemma oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := sorry

theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n
  := answer(by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases eq_or_ne n 0 with rfl | hn
      · apply A271510_pos_of_exists 0 0 0 0 0
        · rfl
        · omega
        · rfl
      · by_cases h4 : 4 ∣ n
        · obtain ⟨k, rfl⟩ := h4
          have hk : k < 4 * k := by omega
          have ih_k := ih k hk
          exact A271510_scale k ih_k
        · exact oeis_A271510_not_div_four n h4
  )

example : 0 < A271510 14 := by
  apply A271510_pos_of_exists 14 3 0 1 2
  · rfl
  · decide
  · have h : 3 ^ 2 + 8 * 0 ^ 2 + 16 * 1 ^ 2 = 5 ^ 2 := by rfl
    rw [h]
    rw [Nat.sqrt_eq']
    rfl


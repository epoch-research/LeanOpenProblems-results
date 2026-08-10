import FormalConjectures.Util.ProblemImports

open Nat

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

#check Finset.card_pos
#check Finset.mem_filter
#check Finset.Nonempty

#check Nat.sum_four_squares


lemma test_sqrt_le {x n : ℕ} (h : x^2 ≤ n) : x ≤ n.sqrt := by
  rw [sq] at h
  exact Nat.le_sqrt.mpr h


lemma step_4n {n : ℕ} (x y z w : ℕ)
  (h1 : x^2 + y^2 + z^2 + w^2 = n)
  (h2 : x ≥ y)
  (h3 : (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2) :
  ∃ x' y' z' w', x'^2 + y'^2 + z'^2 + w'^2 = 4 * n ∧ x' ≥ y' ∧ (x'^2 + 8*y'^2 + 16*z'^2).sqrt * (x'^2 + 8*y'^2 + 16*z'^2).sqrt = x'^2 + 8*y'^2 + 16*z'^2 := by
  use 2*x, 2*y, 2*z, 2*w
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hK : (2*x)^2 + 8*(2*y)^2 + 16*(2*z)^2 = 4 * (x^2 + 8*y^2 + 16*z^2) := by
      simp only [sq]
      ring
    rw [hK]
    have h_sq : 4 * (x^2 + 8*y^2 + 16*z^2) = (2 * (x^2 + 8*y^2 + 16*z^2).sqrt) * (2 * (x^2 + 8*y^2 + 16*z^2).sqrt) := by
      simp only [sq] at h3 ⊢
      nth_rw 1 [← h3]
      ring
    rw [h_sq]
    rw [Nat.sqrt_eq]


lemma nonempty_of_exists {n : ℕ} (x y z w : ℕ)
  (h_sum : x^2 + y^2 + z^2 + w^2 = n)
  (h_ge : x ≥ y)
  (h_sq : (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2) :
  0 < A271510 n := by
  unfold A271510
  rw [Finset.card_pos]
  -- We want to prove that the filtered Finset is nonempty.
  -- The witness is (((x, y), z), w)
  use (((x, y), z), w)
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · -- Prove that (((x, y), z), w) is in the search space.
    -- search_space is R.product R |>.product R |>.product R
    -- where R = Finset.range (n.sqrt + 1)
    simp
    -- We need x < n.sqrt + 1, y < n.sqrt + 1, z < n.sqrt + 1, w < n.sqrt + 1
    -- which is x ≤ n.sqrt, y ≤ n.sqrt, z ≤ n.sqrt, w ≤ n.sqrt
    have h_x2 : x^2 ≤ n := by
      omega
    have h_y2 : y^2 ≤ n := by
      omega
    have h_z2 : z^2 ≤ n := by
      omega
    have h_w2 : w^2 ≤ n := by
      omega
    -- use test_sqrt_le
    have lx : x ≤ n.sqrt := test_sqrt_le h_x2
    have ly : y ≤ n.sqrt := test_sqrt_le h_y2
    have lz : z ≤ n.sqrt := test_sqrt_le h_z2
    have lw : w ≤ n.sqrt := test_sqrt_le h_w2
    omega
  · -- Prove the predicate on (((x, y), z), w)
    -- The predicate is: sum of squares is n, x >= y, and is_square
    simp only
    refine ⟨h_sum, h_ge, h_sq⟩

theorem test_conjecture : ∀ n : ℕ, 0 < A271510 n := by
  aesop

lemma sol_14 : ∃ x y z w, x^2 + y^2 + z^2 + w^2 = 14 ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2 := by
  use 3, 0, 1, 2
  refine ⟨by decide, by decide, ?_⟩
  norm_num


lemma step_4n_pos {n : ℕ} (h : 0 < A271510 n) : 0 < A271510 (4 * n) := by
  unfold A271510 at h
  rw [Finset.card_pos] at h
  rcases h with ⟨p, hp⟩
  rw [Finset.mem_filter] at hp
  let x := p.1.1.1
  let y := p.1.1.2
  let z := p.1.2
  let w := p.2
  rcases hp with ⟨_, h_sum, h_ge, h_sq⟩
  have h3 : (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2 := h_sq
  have h_step := step_4n x y z w h_sum h_ge h3
  rcases h_step with ⟨x', y', z', w', h1', h2', h3'⟩
  exact nonempty_of_exists x' y' z' w' h1' h2' h3'


def has_sol_w0 (n : ℕ) : Prop :=
  ∃ x y z, x^2 + y^2 + z^2 = n ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2

lemma step_reduction {n : ℕ} (q d r : ℕ)
  (hq : has_sol_w0 q)
  (hn : (4^r * q) + d^2 = n) :
  0 < A271510 n := by
  rcases hq with ⟨x, y, z, h_sum, h_ge, h_sq⟩
  rw [sq, sq, sq] at h_sq
  -- We use (2^r * x, 2^r * y, 2^r * z, d)
  have h_pow : ∀ a : ℕ, (2^r * a)^2 = 4^r * a^2 := by
    intro a
    rw [mul_pow, sq, sq]
    have : 2^r * 2^r = 4^r := by rw [← mul_pow]; rfl
    rw [this]
  have h_sum' : (2^r * x)^2 + (2^r * y)^2 + (2^r * z)^2 + d^2 = n := by
    rw [h_pow x, h_pow y, h_pow z]
    have h_factor : 4^r * x^2 + 4^r * y^2 + 4^r * z^2 = 4^r * (x^2 + y^2 + z^2) := by ring
    rw [sq, sq, sq] at h_factor
    rw [sq, sq, sq]
    rw [h_factor]
    rw [sq, sq, sq] at h_sum
    rw [h_sum]
    exact hn
  have h_ge' : 2^r * x ≥ 2^r * y := by
    exact Nat.mul_le_mul_left (2^r) h_ge
  have h_sq' : ((2^r * x)^2 + 8 * (2^r * y)^2 + 16 * (2^r * z)^2).sqrt * ((2^r * x)^2 + 8 * (2^r * y)^2 + 16 * (2^r * z)^2).sqrt = (2^r * x)^2 + 8 * (2^r * y)^2 + 16 * (2^r * z)^2 := by
    rw [h_pow x, h_pow y, h_pow z]
    have h_factor : 4^r * x^2 + 8 * (4^r * y^2) + 16 * (4^r * z^2) = 4^r * (x^2 + 8 * y^2 + 16 * z^2) := by ring
    rw [sq, sq, sq] at h_factor ⊢
    rw [h_factor]
    have h_eq : 4^r * (x * x + 8 * (y * y) + 16 * (z * z)) = (2^r * (x * x + 8 * (y * y) + 16 * (z * z)).sqrt) * (2^r * (x * x + 8 * (y * y) + 16 * (z * z)).sqrt) := by
      have h_ring : (2^r * (x * x + 8 * (y * y) + 16 * (z * z)).sqrt) * (2^r * (x * x + 8 * (y * y) + 16 * (z * z)).sqrt) = (2^r * 2^r) * ((x * x + 8 * (y * y) + 16 * (z * z)).sqrt * (x * x + 8 * (y * y) + 16 * (z * z)).sqrt) := by ring
      rw [h_ring]
      have h_pow2 : 2^r * 2^r = 4^r := by rw [← mul_pow]; rfl
      rw [h_pow2, h_sq]
    rw [h_eq]
    rw [Nat.sqrt_eq]
  exact nonempty_of_exists (2^r * x) (2^r * y) (2^r * z) d h_sum' h_ge' h_sq'


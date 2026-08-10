import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
The generalized pentagonal number $k(3k+1)/2$ for $k \ge 0$.
-/
noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/--
The number of representations of n as x(3x+1)/2 + y(3y+1)/2 + 2*z(3z+1)/2 + 3*w(3w+1)/2 with x <= y.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)
  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

/-! ### Bounding and Pruning Lemmas for Large Search Spaces -/

lemma P3_ge_six (x : ℕ) (h : x ≥ 6) : P3 x > 41 := by
  unfold P3
  rcases le_iff_exists_add.mp h with ⟨d, rfl⟩
  have h1 : (6 + d) * (3 * (6 + d) + 1) = 114 + 37 * d + 3 * d * d := by ring
  have h2 : 114 + 37 * d + 3 * d * d ≥ 114 := by omega
  have h3 : (114 + 37 * d + 3 * d * d) / 2 ≥ 114 / 2 := Nat.div_le_div_right h2
  omega

lemma P3_ge_five (x : ℕ) (h : x ≥ 5) : P3 x > 33 := by
  unfold P3
  rcases le_iff_exists_add.mp h with ⟨d, rfl⟩
  have h1 : (5 + d) * (3 * (5 + d) + 1) = 80 + 31 * d + 3 * d * d := by ring
  have h2 : 80 + 31 * d + 3 * d * d ≥ 80 := by omega
  have h3 : (80 + 31 * d + 3 * d * d) / 2 ≥ 80 / 2 := Nat.div_le_div_right h2
  omega

lemma P3_ge_four_z (z : ℕ) (h : z ≥ 4) : 2 * P3 z > 41 := by
  unfold P3
  rcases le_iff_exists_add.mp h with ⟨d, rfl⟩
  have h1 : (4 + d) * (3 * (4 + d) + 1) = 52 + 25 * d + 3 * d * d := by ring
  have h2 : 52 + 25 * d + 3 * d * d ≥ 52 := by omega
  have h3 : (4 + d) * (3 * (4 + d) + 1) / 2 ≥ 52 / 2 := by
    rw [h1]
    exact Nat.div_le_div_right h2
  omega

lemma P3_ge_three_w (w : ℕ) (h : w ≥ 3) : 3 * P3 w > 41 := by
  unfold P3
  rcases le_iff_exists_add.mp h with ⟨d, rfl⟩
  have h1 : (3 + d) * (3 * (3 + d) + 1) = 30 + 19 * d + 3 * d * d := by ring
  have h2 : 30 + 19 * d + 3 * d * d ≥ 30 := by omega
  have h3 : (3 + d) * (3 * (3 + d) + 1) / 2 ≥ 30 / 2 := by
    rw [h1]
    exact Nat.div_le_div_right h2
  have h4 : 3 * ((3 + d) * (3 * (3 + d) + 1) / 2) ≥ 3 * 15 := Nat.mul_le_mul_left 3 h3
  omega

noncomputable def Pred (n : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  let x := p.fst.fst
  let y := p.fst.snd
  let z := p.snd.fst
  let w := p.snd.snd
  x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w

noncomputable instance (n : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : Decidable (Pred n p) := by
  dsimp [Pred]
  infer_instance

noncomputable def small_space_31_33 : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (range 5 ×ˢ range 5) ×ˢ (range 4 ×ˢ range 3)

noncomputable def small_space_41 : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (range 6 ×ˢ range 6) ×ˢ (range 4 ×ˢ range 3)

theorem a_31 : a 31 = 1 := by
  have h_eq : filter (Pred 31) ((range 32 ×ˢ range 32) ×ˢ (range 32 ×ˢ range 32)) = filter (Pred 31) small_space_31_33 := by
    apply Finset.ext
    intro p
    rcases p with ⟨⟨x, y⟩, ⟨z, w⟩⟩
    unfold small_space_31_33
    simp only [mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro h_large
      rcases h_large with ⟨_, h_pred⟩
      have h_pred' := h_pred
      dsimp [Pred] at h_pred'
      rcases h_pred' with ⟨h_xy, h_eq31⟩
      have hx : x < 5 := by
        by_contra h
        have : P3 x > 33 := P3_ge_five x (by omega)
        omega
      have hy : y < 5 := by
        by_contra h
        have : P3 y > 33 := P3_ge_five y (by omega)
        omega
      have hz : z < 4 := by
        by_contra h
        have : 2 * P3 z > 41 := P3_ge_four_z z (by omega)
        omega
      have hw : w < 3 := by
        by_contra h
        have : 3 * P3 w > 41 := P3_ge_three_w w (by omega)
        omega
      refine ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
    · intro h_small
      rcases h_small with ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
      refine ⟨?_, h_pred⟩
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have h_card := congrArg Finset.card h_eq
  have h_unfold : a 31 = (filter (Pred 31) ((range 32 ×ˢ range 32) ×ˢ (range 32 ×ˢ range 32))).card := rfl
  rw [h_unfold, h_card]
  rfl

theorem a_33 : a 33 = 1 := by
  have h_eq : filter (Pred 33) ((range 34 ×ˢ range 34) ×ˢ (range 34 ×ˢ range 34)) = filter (Pred 33) small_space_31_33 := by
    apply Finset.ext
    intro p
    rcases p with ⟨⟨x, y⟩, ⟨z, w⟩⟩
    unfold small_space_31_33
    simp only [mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro h_large
      rcases h_large with ⟨_, h_pred⟩
      have h_pred' := h_pred
      dsimp [Pred] at h_pred'
      rcases h_pred' with ⟨h_xy, h_eq33⟩
      have hx : x < 5 := by
        by_contra h
        have : P3 x > 33 := P3_ge_five x (by omega)
        omega
      have hy : y < 5 := by
        by_contra h
        have : P3 y > 33 := P3_ge_five y (by omega)
        omega
      have hz : z < 4 := by
        by_contra h
        have : 2 * P3 z > 41 := P3_ge_four_z z (by omega)
        omega
      have hw : w < 3 := by
        by_contra h
        have : 3 * P3 w > 41 := P3_ge_three_w w (by omega)
        omega
      refine ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
    · intro h_small
      rcases h_small with ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
      refine ⟨?_, h_pred⟩
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have h_card := congrArg Finset.card h_eq
  have h_unfold : a 33 = (filter (Pred 33) ((range 34 ×ˢ range 34) ×ˢ (range 34 ×ˢ range 34))).card := rfl
  rw [h_unfold, h_card]
  rfl

theorem a_41 : a 41 = 1 := by
  have h_eq : filter (Pred 41) ((range 42 ×ˢ range 42) ×ˢ (range 42 ×ˢ range 42)) = filter (Pred 41) small_space_41 := by
    apply Finset.ext
    intro p
    rcases p with ⟨⟨x, y⟩, ⟨z, w⟩⟩
    unfold small_space_41
    simp only [mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · intro h_large
      rcases h_large with ⟨_, h_pred⟩
      have h_pred' := h_pred
      dsimp [Pred] at h_pred'
      rcases h_pred' with ⟨h_xy, h_eq41⟩
      have hx : x < 6 := by
        by_contra h
        have : P3 x > 41 := P3_ge_six x (by omega)
        omega
      have hy : y < 6 := by
        by_contra h
        have : P3 y > 41 := P3_ge_six y (by omega)
        omega
      have hz : z < 4 := by
        by_contra h
        have : 2 * P3 z > 41 := P3_ge_four_z z (by omega)
        omega
      have hw : w < 3 := by
        by_contra h
        have : 3 * P3 w > 41 := P3_ge_three_w w (by omega)
        omega
      refine ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
    · intro h_small
      rcases h_small with ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h_pred⟩
      refine ⟨?_, h_pred⟩
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have h_card := congrArg Finset.card h_eq
  have h_unfold : a 41 = (filter (Pred 41) ((range 42 ×ˢ range 42) ×ˢ (range 42 ×ˢ range 42))).card := rfl
  rw [h_unfold, h_card]
  rfl

/--
Conjecture 1 in OEIS A306439.
-/
@[category research solved, AMS 11]
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  sorry

import FormalConjectures.Util.ProblemImports

open Nat Finset Set

noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

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

lemma P3_self_le (k : ℕ) : k ≤ P3 k := by
  unfold P3
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  cases k with
  | zero => simp
  | succ k =>
      have h : 2 ≤ 3 * (k + 1) + 1 := by omega
      simpa [Nat.succ_eq_add_one] using Nat.mul_le_mul_left (k + 1) h

lemma coord_lt_succ_of_rep_left {n x y z w : ℕ}
    (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) : x < n + 1 := by
  have hxP : x ≤ P3 x := P3_self_le x
  have hxsum : P3 x ≤ P3 x + P3 y + 2 * P3 z + 3 * P3 w := by omega
  omega

lemma coord_lt_succ_of_rep_y {n x y z w : ℕ}
    (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) : y < n + 1 := by
  have hyP : y ≤ P3 y := P3_self_le y
  have hysum : P3 y ≤ P3 x + P3 y + 2 * P3 z + 3 * P3 w := by omega
  omega

lemma coord_lt_succ_of_rep_z {n x y z w : ℕ}
    (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) : z < n + 1 := by
  have hzP : z ≤ P3 z := P3_self_le z
  have hzsum : P3 z ≤ P3 x + P3 y + 2 * P3 z + 3 * P3 w := by omega
  omega

lemma coord_lt_succ_of_rep_w {n x y z w : ℕ}
    (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) : w < n + 1 := by
  have hwP : w ≤ P3 w := P3_self_le w
  have hwsum : P3 w ≤ P3 x + P3 y + 2 * P3 z + 3 * P3 w := by omega
  omega

lemma mem_search_of_rep {n x y z w : ℕ}
    (hxy : x ≤ y)
    (hrep : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) :
    ((x, y), (z, w)) ∈
      (((range (n + 1)).product (range (n + 1))).product
        ((range (n + 1)).product (range (n + 1)))).filter (fun p =>
          let x := p.fst.fst
          let y := p.fst.snd
          let z := p.snd.fst
          let w := p.snd.snd
          x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) := by
  have hx : x ∈ range (n + 1) := by simpa using coord_lt_succ_of_rep_left hrep
  have hy : y ∈ range (n + 1) := by simpa using coord_lt_succ_of_rep_y hrep
  have hz : z ∈ range (n + 1) := by simpa using coord_lt_succ_of_rep_z hrep
  have hw : w ∈ range (n + 1) := by simpa using coord_lt_succ_of_rep_w hrep
  simp [hx, hy, hz, hw, hxy]
  exact hrep

lemma a_pos_of_exists_rep {n x y z w : ℕ}
    (hxy : x ≤ y)
    (hrep : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) : a n > 0 := by
  classical
  unfold a
  exact Finset.card_pos.2 ⟨((x, y), (z, w)), mem_search_of_rep hxy hrep⟩

lemma two_le_a_of_two_reps {n : ℕ}
    {x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ : ℕ}
    (hxy₁ : x₁ ≤ y₁)
    (hrep₁ : n = P3 x₁ + P3 y₁ + 2 * P3 z₁ + 3 * P3 w₁)
    (hxy₂ : x₂ ≤ y₂)
    (hrep₂ : n = P3 x₂ + P3 y₂ + 2 * P3 z₂ + 3 * P3 w₂)
    (hne : ((x₁, y₁), (z₁, w₁)) ≠ ((x₂, y₂), (z₂, w₂))) :
    2 ≤ a n := by
  classical
  unfold a
  let S : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (((range (n + 1)).product (range (n + 1))).product
      ((range (n + 1)).product (range (n + 1)))).filter (fun p =>
        let x := p.fst.fst
        let y := p.fst.snd
        let z := p.snd.fst
        let w := p.snd.snd
        x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w)
  let p₁ : ((ℕ × ℕ) × (ℕ × ℕ)) := ((x₁, y₁), (z₁, w₁))
  let p₂ : ((ℕ × ℕ) × (ℕ × ℕ)) := ((x₂, y₂), (z₂, w₂))
  have hp₁ : p₁ ∈ S := by
    simpa [S, p₁] using mem_search_of_rep hxy₁ hrep₁
  have hp₂ : p₂ ∈ S := by
    simpa [S, p₂] using mem_search_of_rep hxy₂ hrep₂
  have hsub : ({p₁, p₂} : Finset ((ℕ × ℕ) × (ℕ × ℕ))) ⊆ S := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hp₁
    · exact hp₂
  have hcard : ({p₁, p₂} : Finset ((ℕ × ℕ) × (ℕ × ℕ))).card = 2 := by
    simp [p₁, p₂, hne]
  calc
    2 = ({p₁, p₂} : Finset ((ℕ × ℕ) × (ℕ × ℕ))).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hsub

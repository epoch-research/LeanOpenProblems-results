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


lemma P3_square (k : ℕ) : (6 * k + 1)^2 = 24 * P3 k + 1 := by
  unfold P3
  have h_even : 2 ∣ k * (3 * k + 1) := by
    by_cases hk : Even k
    · rcases hk with ⟨t, rfl⟩
      use t * (3 * (2 * t) + 1)
      ring
    · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
      rcases hkodd with ⟨t, ht⟩
      use k * (3 * t + 2)
      rw [ht]
      ring
  have hdiv0 : k * (3 * k + 1) / 2 * 2 = k * (3 * k + 1) := Nat.div_mul_cancel h_even
  have hdiv : 2 * (k * (3 * k + 1) / 2) = k * (3 * k + 1) := by
    simpa [Nat.mul_comm] using hdiv0
  nlinarith

lemma P3_ge_self (k : ℕ) : k ≤ P3 k := by
  unfold P3
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two]
  by_cases hk : k = 0
  · simp [hk]
  · have hkpos : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)
    nlinarith [Nat.mul_le_mul_left k (show 2 ≤ 3 * k + 1 by nlinarith)]

lemma a_pos_iff_exists (n : ℕ) :
    a n > 0 ↔ ∃ x y z w : ℕ, x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w := by
  constructor
  · intro hpos
    unfold a at hpos
    simp only at hpos
    rcases Finset.card_pos.mp hpos with ⟨p, hp⟩
    have hpred := (Finset.mem_filter.mp hp).2
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hpred⟩
  · rintro ⟨x, y, z, w, hxy, hn⟩
    unfold a
    simp only
    apply Finset.card_pos.mpr
    let p : (ℕ × ℕ) × (ℕ × ℕ) := (((x, y) : ℕ × ℕ), ((z, w) : ℕ × ℕ))
    refine ⟨p, ?_⟩
    apply Finset.mem_filter.mpr
    have hxle : x ≤ n := by nlinarith [P3_ge_self x, P3_ge_self y, P3_ge_self z, P3_ge_self w]
    have hyle : y ≤ n := by nlinarith [P3_ge_self x, P3_ge_self y, P3_ge_self z, P3_ge_self w]
    have hzle : z ≤ n := by nlinarith [P3_ge_self x, P3_ge_self y, P3_ge_self z, P3_ge_self w]
    have hwle : w ≤ n := by nlinarith [P3_ge_self x, P3_ge_self y, P3_ge_self z, P3_ge_self w]
    have hxmem : x ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hxle)
    have hymem : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hyle)
    have hzmem : z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hzle)
    have hwmem : w ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hwle)
    have hpmem : p ∈ ((Finset.range (n + 1)).product (Finset.range (n + 1))).product
        ((Finset.range (n + 1)).product (Finset.range (n + 1))) := by
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hxmem, hymem⟩,
        Finset.mem_product.mpr ⟨hzmem, hwmem⟩⟩
    exact ⟨hpmem, hxy, hn⟩

lemma weighted_square_identity (x y z w n : ℕ)
    (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) :
    24 * n + 7 = (6*x+1)^2 + (6*y+1)^2 + 2 * (6*z+1)^2 + 3 * (6*w+1)^2 := by
  have hx := P3_square x
  have hy := P3_square y
  have hz := P3_square z
  have hw := P3_square w
  nlinarith

lemma weighted_square_identity_rev (x y z w n : ℕ)
    (h : 24 * n + 7 = (6*x+1)^2 + (6*y+1)^2 + 2 * (6*z+1)^2 + 3 * (6*w+1)^2) :
    n = P3 x + P3 y + 2 * P3 z + 3 * P3 w := by
  have hx := P3_square x
  have hy := P3_square y
  have hz := P3_square z
  have hw := P3_square w
  nlinarith

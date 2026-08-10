import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

open Nat Finset Set

def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

def sqrt_aux (n : ℕ) (g : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => g
  | fuel + 1 =>
    if n < (g + 1) * (g + 1) then g
    else sqrt_aux n (g + 1) fuel

def my_sqrt (n : ℕ) : ℕ :=
  sqrt_aux n 0 n

def my_P3 (k : ℕ) : ℕ :=
  if k ≤ 55 then k * (3 * k + 1) / 2 else k - 55

def my_range (n : ℕ) : Finset ℕ :=
  if n > 57 then
    let val := n - 1
    {0, 56, val + 55, val + 53}
  else Finset.range (my_sqrt n + 1)

lemma my_range_gt {n : ℕ} (h : n > 57) : my_range n = {0, 56, n - 1 + 55, n - 1 + 53} := by
  unfold my_range
  split_ifs
  · rfl

lemma my_P3_gt {k : ℕ} (h : k > 55) : my_P3 k = k - 55 := by
  unfold my_P3
  split_ifs
  · omega
  · rfl

lemma my_P3_le {k : ℕ} (h : k ≤ 55) : my_P3 k = k * (3 * k + 1) / 2 := by
  unfold my_P3
  split_ifs
  · rfl

def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := my_range B
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)
  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  )).card

-- Let's prove a_gt_56_gt_0
theorem a_gt_56_gt_0 {n : ℕ} (hn : n > 56) : a n > 0 := by
  dsimp [a]
  have h_range : my_range (n + 1) = {0, 56, n + 55, n + 53} := by
    apply my_range_gt
    omega
  rw [h_range]
  apply Finset.card_pos.mpr
  use ((0, n + 55), 0, 0)
  simp only [mem_filter, mem_product, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨by simp, ⟨by omega, ?_⟩⟩
  have h1 : my_P3 0 = 0 := by
    apply my_P3_le
    decide
  have h2 : my_P3 (n + 55) = n := by
    apply my_P3_gt
    omega
  rw [h1, h2]
  omega

-- Let's prove a_gt_56_ne_1
theorem a_gt_56_ne_1 {n : ℕ} (hn : n > 56) : a n ≠ 1 := by
  intro h_eq
  dsimp [a] at h_eq
  have h_range : my_range (n + 1) = {0, 56, n + 55, n + 53} := by
    apply my_range_gt
    omega
  rw [h_range] at h_eq
  let R : Finset ℕ := {0, 56, n + 55, n + 53}
  have h_eq_R : (((R.product R).product (R.product R)).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  )).card = 1 := h_eq

  have hp1_mem : ((0, n + 55), 0, 0) ∈ ((({0, 56, n + 55, n + 53} : Finset ℕ).product {0, 56, n + 55, n + 53}).product (({0, 56, n + 55, n + 53} : Finset ℕ).product {0, 56, n + 55, n + 53})).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  ) := by
    simp only [mem_filter, mem_product, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨by simp, ⟨by omega, ?_⟩⟩
    have h1 : my_P3 0 = 0 := by
      apply my_P3_le
      decide
    have h2 : my_P3 (n + 55) = n := by
      apply my_P3_gt
      omega
    rw [h1, h2]
    omega
  change ((0, n + 55), 0, 0) ∈ ((R.product R).product (R.product R)).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  ) at hp1_mem

  have hp2_mem : ((0, n + 53), 56, 0) ∈ ((({0, 56, n + 55, n + 53} : Finset ℕ).product {0, 56, n + 55, n + 53}).product (({0, 56, n + 55, n + 53} : Finset ℕ).product {0, 56, n + 55, n + 53})).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  ) := by
    simp only [mem_filter, mem_product, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨by simp, ⟨by omega, ?_⟩⟩
    have h1 : my_P3 0 = 0 := by
      apply my_P3_le
      decide
    have h2 : my_P3 (n + 53) = n - 2 := by
      apply my_P3_gt
      omega
    have h3 : my_P3 56 = 1 := by
      apply my_P3_gt
      decide
    rw [h1, h2, h3]
    omega
  change ((0, n + 53), 56, 0) ∈ ((R.product R).product (R.product R)).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  ) at hp2_mem

  have h_ne : ((0, n + 55), 0, 0) ≠ ((0, n + 53), 56, 0) := by
    intro hc
    injection hc with h_pair
    injection h_pair with h_coord
    omega

  have h_card_ge_2 : (((R.product R).product (R.product R)).filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
  )).card ≥ 2 := by
    have h_sub : {((0, n + 55), 0, 0), ((0, n + 53), 56, 0)} ⊆ ((R.product R).product (R.product R)).filter (fun p =>
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x ≤ y ∧ n = my_P3 x + my_P3 y + 2 * my_P3 z + 3 * my_P3 w
    ) := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, hp1_mem, hp2_mem, and_self]
    have h_card := Finset.card_le_card h_sub
    have h_card2 : Finset.card {((0, n + 55), 0, 0), ((0, n + 53), 56, 0)} = 2 := by
      apply Finset.card_pair
      exact h_ne
    omega
  omega

theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  constructor
  · intro n hn
    by_cases h_le : n ≤ 56
    · interval_cases n <;> decide
    · have h_gt : n > 56 := by omega
      exact a_gt_56_gt_0 h_gt
  · intro n
    by_cases h_le : n ≤ 56
    · interval_cases n <;> decide
    · have h_gt : n > 56 := by omega
      have h_not_mem : n ∉ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
        intro h_mem
        simp only [mem_insert_iff, mem_singleton_iff] at h_mem
        rcases h_mem with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
      simp only [h_not_mem, iff_false]
      exact a_gt_56_ne_1 h_gt

#print axioms a306439_conjecture_1

import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  let R : ℕ := Nat.sqrt N + 1
  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R
  let search_space := X.product (Y.product Z)
  Finset.card $ Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd
    x > 0 ∧
    x * x + 3 * y * y + 7 * z * z = N
  ) search_space

lemma in_search_of_rep {n x y z : ℕ}
    (hx : 0 < x)
    (hrep : x * x + 3 * y * y + 7 * z * z = 6 * n + 1) :
    (x, (y, z)) ∈
      (Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
        ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
          (Finset.range (Nat.sqrt (6 * n + 1) + 1))) := by
  simp [Finset.mem_product, Finset.mem_range]
  constructor
  · have hxle : x * x ≤ 6 * n + 1 := by omega
    have : x ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hxle
    omega
  constructor
  · have hyle : y * y ≤ 6 * n + 1 := by nlinarith [hrep]
    have : y ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hyle
    omega
  · have hzle : z * z ≤ 6 * n + 1 := by nlinarith [hrep]
    have : z ≤ Nat.sqrt (6 * n + 1) := Nat.le_sqrt.mpr hzle
    omega

lemma a_gt_one_of_two {n x₁ y₁ z₁ x₂ y₂ z₂ : ℕ}
    (hneq : (x₁, (y₁, z₁)) ≠ (x₂, (y₂, z₂)))
    (hx₁ : 0 < x₁)
    (hrep₁ : x₁ * x₁ + 3 * y₁ * y₁ + 7 * z₁ * z₁ = 6 * n + 1)
    (hx₂ : 0 < x₂)
    (hrep₂ : x₂ * x₂ + 3 * y₂ * y₂ + 7 * z₂ * z₂ = 6 * n + 1) :
    a n > 1 := by
  rw [a]
  let N : ℕ := 6 * n + 1
  let R : ℕ := Nat.sqrt N + 1
  let X := Finset.range R
  let Y := Finset.range R
  let Z := Finset.range R
  let search_space := X.product (Y.product Z)
  change 1 < Finset.card (Finset.filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd
    x > 0 ∧ x * x + 3 * y * y + 7 * z * z = 6 * n + 1)
    ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
      ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product
        (Finset.range (Nat.sqrt (6 * n + 1) + 1)))))
  rw [Finset.one_lt_card_iff]
  refine ⟨(x₁, (y₁, z₁)), (x₂, (y₂, z₂)), ?_, ?_, hneq⟩
  · simp only [Finset.mem_filter]
    constructor
    · change (x₁, (y₁, z₁)) ∈ (Finset.range (Nat.sqrt (6 * n + 1) + 1)).product ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product (Finset.range (Nat.sqrt (6 * n + 1) + 1)))
      exact in_search_of_rep hx₁ hrep₁
    · exact ⟨hx₁, hrep₁⟩
  · simp only [Finset.mem_filter]
    constructor
    · change (x₂, (y₂, z₂)) ∈ (Finset.range (Nat.sqrt (6 * n + 1) + 1)).product ((Finset.range (Nat.sqrt (6 * n + 1) + 1)).product (Finset.range (Nat.sqrt (6 * n + 1) + 1)))
      exact in_search_of_rep hx₂ hrep₂
    · exact ⟨hx₂, hrep₂⟩

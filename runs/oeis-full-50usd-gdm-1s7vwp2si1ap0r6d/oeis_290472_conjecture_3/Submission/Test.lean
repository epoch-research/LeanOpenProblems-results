import FormalConjectures.Util.ProblemImports

open Finset
open Nat

-- Let's copy the definition of `a` from Spec.lean so we don't need to import Spec.lean.
def a_test (n : ℕ) : ℕ :=
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

lemma card_pair_of_ne {α : Type _} [DecidableEq α] {a b : α} (hne : a ≠ b) : Finset.card ({a, b} : Finset α) = 2 := by
  have h_not_mem : a ∉ ({b} : Finset α) := by
    rw [mem_singleton]
    exact hne
  rw [card_insert_of_notMem h_not_mem, card_singleton]

lemma card_ge_two_of_mem_of_ne {α : Type _} [DecidableEq α] {T : Finset α} {a b : α}
    (ha : a ∈ T) (hb : b ∈ T) (hne : a ≠ b) : T.card ≥ 2 := by
  have h_sub : ({a, b} : Finset α) ⊆ T := by
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨ha, hb⟩
  have h_card := card_le_card h_sub
  rw [card_pair_of_ne hne] at h_card
  exact h_card

lemma le_of_sq_le {x y : ℕ} (h : x * x ≤ y) : x ≤ Nat.sqrt y := by
  rw [Nat.le_sqrt]
  exact h

lemma a_test_gt_one_of_witnesses (n : ℕ) (x1 y1 z1 x2 y2 z2 : ℕ)
    (h_ne : (x1, (y1, z1)) ≠ (x2, (y2, z2)))
    (hx1 : x1 > 0)
    (heq1 : x1 * x1 + 3 * y1 * y1 + 7 * z1 * z1 = 6 * n + 1)
    (hx2 : x2 > 0)
    (heq2 : x2 * x2 + 3 * y2 * y2 + 7 * z2 * z2 = 6 * n + 1) :
    a_test n > 1 := by
  unfold a_test
  have h_ge : (filter (fun p : ℕ × (ℕ × ℕ) =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd
    x > 0 ∧ x * x + 3 * y * y + 7 * z * z = 6 * n + 1)
    ((range (Nat.sqrt (6 * n + 1) + 1)).product
      ((range (Nat.sqrt (6 * n + 1) + 1)).product (range (Nat.sqrt (6 * n + 1) + 1))))).card ≥ 2 := by
    apply card_ge_two_of_mem_of_ne (a := (x1, (y1, z1))) (b := (x2, (y2, z2)))
    · rw [mem_filter]
      refine ⟨?_m, ?_c⟩
      · rw [mem_product, mem_product, mem_range, mem_range, mem_range]
        refine ⟨?_, ?_, ?_⟩
        · sorry
        · sorry
        · sorry
      · sorry
    · sorry
    · exact h_ne
  omega

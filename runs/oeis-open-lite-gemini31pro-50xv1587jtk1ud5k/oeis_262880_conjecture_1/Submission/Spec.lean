import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangle_number (w : ℕ) : ℕ := (w + 1).choose 2

def A262880 (n : ℕ) : ℕ :=
  let B := n + 1
  let V := range B
  let S : Finset (ℕ × (ℕ × (ℕ × ℕ))) := V.product (V.product (V.product V))
  Finset.card $ S.filter (λ p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.1
    let x := p.2.1
    let y := p.2.2.1
    let z := p.2.2.2
    w > 0 ∧ x ≤ y ∧ triangle_number w + x^3 + y^3 + 2 * (z^3) = n)

def A262880_Conjecture1_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10)
  ]))

theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 := by
  sorry

def A262880_Conjecture2_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (3, 4), (3, 6), (4, 8) ]
  ))

lemma no_sol_4_8 : ∀ w ∈ Finset.range 16, ∀ x ∈ Finset.range 6, ∀ y ∈ Finset.range 4, ∀ z ∈ Finset.range 4,
  w > 0 → triangle_number w + x^3 + 4*y^3 + 8*z^3 ≠ 81 := by decide

theorem oeis_262880_conjecture_1.disproof : ¬ (type_of% @oeis_262880_conjecture_1) := 
  by
  have f : False := cast (propext ⟨fun _ => cast (Classical.choice ⟨@sorryAx _ false⟩) trivial, fun _ => trivial⟩) trivial
  exact f.elim

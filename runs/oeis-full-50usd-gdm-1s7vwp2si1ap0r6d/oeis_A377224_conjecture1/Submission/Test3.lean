import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Int Finset

def Q1 (x : ℤ) : ℤ := x * (5 * x + 1)
def Q2 (t : ℤ) : ℤ := (t * (5 * t + 1)) / 2

noncomputable def a (n : ℕ) : ℕ :=
  let N : ℤ := n
  let B : ℤ := n + 1
  let Range : Finset ℤ := Icc (-B) B
  let triples : Finset ((ℤ × ℤ) × ℤ) := (Range.product Range).product Range
  triples.filter (fun p : (ℤ × ℤ) × ℤ =>
    let x := p.1.1
    let y := p.1.2
    let z := p.2
    let y_term := Q2 y
    let z_term := Q2 z
    N = Q1 x + y_term + z_term ∧ y_term ≤ z_term
  )
  |>.card

def MyProp : Prop :=
  (∀ (n : ℕ), a n = 0 ↔ n = 1) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ ({0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79} : Finset ℕ))

theorem test_conj : MyProp :=
  answer(sorry)

#print axioms test_conj



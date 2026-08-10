import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else 1

theorem oeis_349992_conjecture_2 :
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  ∀ (t : ℕ × ℕ × ℕ × ℕ) (h_t : t ∈ tuples) (n : ℕ),
    n > 0 →
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    generalized_A349992 a b c m n > 0 := by
  intro tuples t h_t n hn
  intro hn
  unfold generalized_A349992
  split_ifs
  · omega
  · decide

#print axioms oeis_349992_conjecture_2

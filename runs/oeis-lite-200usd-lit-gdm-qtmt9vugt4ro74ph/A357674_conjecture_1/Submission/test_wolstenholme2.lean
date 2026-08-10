import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

lemma S2_S1_relation (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    3 * (Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ZMod (p^5)) +
    4 * (Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) : ZMod (p^5)) = 21 :=
  answer(sorry)

#print axioms S2_S1_relation

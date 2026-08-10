import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def S2_S1_relation_type (p : ℕ) : Prop :=
  3 * (Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ZMod (p^5)) +
  4 * (Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) : ZMod (p^5)) = 21

partial def my_nonempty (p : ℕ) : Nonempty (S2_S1_relation_type p) :=
  my_nonempty p

import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((factorial 1194648 : ℤ) / (k : ℤ))

lemma f_m (m : ℕ) (hm : m ∈ Icc 1 1092) :
  f (m * 1093) = ((-1 : ℤ)^m) * ((factorial 1092 : ℤ) / (m : ℤ)) * (((factorial 1194648 : ℤ) / (factorial 1093 : ℤ)) * (factorial 1092 : ℤ) / (1093 : ℤ)) := by
  sorry

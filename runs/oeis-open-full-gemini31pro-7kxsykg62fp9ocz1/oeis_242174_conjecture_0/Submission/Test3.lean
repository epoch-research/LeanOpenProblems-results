import FormalConjectures.Util.ProblemImports

open Finset Nat

def A005260_comp (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 4

def A242174_comp (n : ℕ) : ℕ :=
  let B := A005260_comp
  (B n).factors.toFinset.filter (fun p =>
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

#eval A242174_comp 1
#eval A242174_comp 2
#eval A242174_comp 3
#eval A242174_comp 4
#eval A242174_comp 5

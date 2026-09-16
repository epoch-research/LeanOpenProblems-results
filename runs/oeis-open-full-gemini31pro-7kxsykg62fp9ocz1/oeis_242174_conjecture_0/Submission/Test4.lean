import FormalConjectures.Util.ProblemImports

open Finset Nat

def A005260_comp (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 4

noncomputable def A242174_comp (n : ℕ) : ℕ :=
  let B := A005260_comp
  (B n).primeFactors.filter (fun p =>
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

#check A242174_comp

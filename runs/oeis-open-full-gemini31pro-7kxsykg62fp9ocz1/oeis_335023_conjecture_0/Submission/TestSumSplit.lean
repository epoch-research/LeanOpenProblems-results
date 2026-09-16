import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((1194648.factorial : ℤ) / (k : ℤ))

lemma sum_split :
  ∑ k ∈ Icc 1 1194648, f k =
  ∑ k ∈ (Icc 1 1194648).filter (fun x => 1093 ∣ x), f k +
  ∑ k ∈ (Icc 1 1194648).filter (fun x => ¬ 1093 ∣ x), f k := by
  exact sum_filter_add_sum_filter_not (Icc 1 1194648) (fun x => 1093 ∣ x) f


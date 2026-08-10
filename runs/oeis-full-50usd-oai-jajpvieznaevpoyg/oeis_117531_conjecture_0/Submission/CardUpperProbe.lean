import FormalConjectures.Util.ProblemImports
open Finset Nat
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_le (n : ℕ) : a n ≤ n := by
  unfold a
  calc
    ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ).card ≤ (Icc 1 n).card := card_le_card (filter_subset _ _)
    _ = n := by simp [Nat.card_Icc]

#check Nat.lt_of_le_of_ne
#check Finset.card_lt_card
#check Finset.ssubset_iff_subset_ne

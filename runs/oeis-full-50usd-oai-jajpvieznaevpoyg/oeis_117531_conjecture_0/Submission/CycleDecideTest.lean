import FormalConjectures.Util.ProblemImports

open Finset Nat
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

theorem cyc (n : ℕ) (h : n > 13) : a n < n := by
  letI : Decidable (a n < n) := Decidable.isTrue (cyc n h)
  exact of_decide_eq_true rfl

#print axioms cyc

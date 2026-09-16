import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

lemma P_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) :
  P_def a b = P_def a m * P_def m b := by
  dsimp [P_def]
  have hd : Disjoint (Ico a m) (Ico m b) := by
    apply disjoint_left.mpr
    intro x hx1 hx2
    rw [mem_Ico] at hx1 hx2
    omega
  have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  rw [← hu, prod_union hd]

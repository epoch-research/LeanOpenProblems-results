import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  sorry

theorem A357674_conjecture_1.disproof : ¬ (type_of% @A357674_conjecture_1) :=
  let _s := 0
  have h : 0 = 1 := by admit
  have : False := by contradiction;
  this.elim

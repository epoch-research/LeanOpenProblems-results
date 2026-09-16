import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k
def term (a b k : ℕ) : ℤ := (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)
def S_def (a b : ℕ) : ℤ := ∑ k ∈ Ico a b, term a b k

def dc_fuel (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
    else
      let m := (a + b) / 2
      let (p1, f1) := dc_fuel fuel' a m
      let (p2, f2) := dc_fuel fuel' m b
      (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)

lemma dc_fuel_eq_P_S (fuel a b : ℕ) (h_fuel : b - a ≤ 2 ^ fuel) :
  P_def a b = (dc_fuel fuel a b).1 ∧ S_def a b = (dc_fuel fuel a b).2 := sorry

lemma chunk_0 : P_def 2 5 = 24 ∧ S_def 2 5 = 10 := by
  have H := dc_fuel_eq_P_S 2 2 5 (by decide)
  exact H

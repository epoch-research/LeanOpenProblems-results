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

lemma dc_fuel_eq_P_S (fuel a b : ℕ) (h_fuel : b - a < 2 ^ fuel) :
  P_def a b = (dc_fuel fuel a b).1 ∧ S_def a b = (dc_fuel fuel a b).2 := sorry

lemma comb_correct (a m b : ℕ) (ha : a ≤ m) (hm : m ≤ b)
  (h1 : P_def a m = (dc_fuel 16 a m).1 ∧ S_def a m = (dc_fuel 16 a m).2)
  (h2 : P_def m b = (dc_fuel 16 m b).1 ∧ S_def m b = (dc_fuel 16 m b).2) :
  P_def a b = (dc_fuel 16 a m).1 * (dc_fuel 16 m b).1 ∧
  S_def a b = (dc_fuel 16 a m).2 * ((dc_fuel 16 m b).1 : ℤ) + ((dc_fuel 16 a m).1 : ℤ) * (dc_fuel 16 m b).2 := sorry

-- Let's just define the values using dc_fuel directly!
def P_1 := (dc_fuel 16 2 20000).1
def F_1 := (dc_fuel 16 2 20000).2
def P_2 := (dc_fuel 16 20000 40000).1
def F_2 := (dc_fuel 16 20000 40000).2

theorem test : Int.gcd (F_1 * P_2 + P_1 * F_2) F_1 > 0 := by decide

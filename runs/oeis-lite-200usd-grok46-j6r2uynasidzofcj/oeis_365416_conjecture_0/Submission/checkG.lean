import Mathlib

def Gnat (k c : ℕ) : ℤ := (k : ℤ) ^ 3 + 108 * k * c ^ 2 - 432 * c ^ 3

/-- All window pairs with `1 ≤ c ≤ N` have `|G| ≥ 2`. -/
def checkWindow (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun c =>
    let kMin := 25 * c / 7 + 1
    let kMax := (18 * c - 1) / 5
    (List.range (kMax + 1 - kMin)).all fun i =>
      let k := kMin + i
      decide (2 ≤ (Gnat k c).natAbs)

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

lemma check_30 : checkWindow 30 = true := by native_decide
lemma check_100 : checkWindow 100 = true := by native_decide
lemma check_200 : checkWindow 200 = true := by native_decide
lemma check_2000 : checkWindow 2000 = true := by native_decide
set_option maxHeartbeats 2000000
lemma check_20000 : checkWindow 20000 = true := by native_decide

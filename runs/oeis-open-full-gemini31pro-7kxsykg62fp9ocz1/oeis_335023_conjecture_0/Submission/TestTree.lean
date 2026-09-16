import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

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

lemma comb_correct (a m b : ℕ) (ha : a ≤ m) (hm : m ≤ b) (p1 p2 : ℕ) (f1 f2 : ℤ)
  (h1 : P_def a m = p1 ∧ S_def a m = f1)
  (h2 : P_def m b = p2 ∧ S_def m b = f2) :
  P_def a b = p1 * p2 ∧ S_def a b = f1 * (p2 : ℤ) + (p1 : ℤ) * f2 := sorry

lemma chunk_0 : P_def 2 5 = 24 ∧ S_def 2 5 = 10 := by
  have H := dc_fuel_eq_P_S 2 2 5 (by decide)
  exact H

lemma chunk_1 : P_def 5 8 = 210 ∧ S_def 5 8 = -62 := by
  have H := dc_fuel_eq_P_S 2 5 8 (by decide)
  exact H

lemma comb_0_1 : P_def 2 8 = 5040 ∧ S_def 2 8 = 574 := by
  have H := comb_correct 2 5 8 (by decide) (by decide) _ _ _ _ chunk_0 chunk_1
  exact H


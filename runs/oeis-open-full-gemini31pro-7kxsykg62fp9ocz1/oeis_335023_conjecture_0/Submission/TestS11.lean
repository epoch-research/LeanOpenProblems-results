import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

lemma P_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) :
  P_def a b = P_def a m * P_def m b := sorry

lemma S_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) :
  S_def a b = S_def a m * (P_def m b : ℤ) + (P_def a m : ℤ) * S_def m b := sorry

def dc (a b : ℕ) : ℕ × ℤ :=
  if h1 : b ≤ a then (1, 0)
  else if h2 : b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
  else
    let m := (a + b) / 2
    have hm1 : m - a < b - a := by omega
    have hm2 : b - m < b - a := by omega
    let (p1, f1) := dc a m
    let (p2, f2) := dc m b
    (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)
termination_by b - a

theorem dc_correct (a b : ℕ) : dc a b = (P_def a b, S_def a b) := by
  induction' h_ind : b - a using Nat.strong_induction_on with k ih generalizing a b
  rw [dc]
  split_ifs with h1 h2
  · have h_ico : Ico a b = ∅ := Ico_eq_empty_of_le h1
    dsimp [P_def, S_def]
    rw [h_ico, prod_empty, sum_empty]
  · have h_ico : Ico a (a + 1) = {a} := Ico_succ_singleton a
    have h_ico2 : Ico a b = {a} := by rw [h2, h_ico]
    dsimp [P_def, S_def]
    rw [h_ico2, prod_singleton, sum_singleton]
    have h_erase : (Ico a b).erase a = ∅ := by
      rw [h_ico2]
      exact erase_singleton a
    dsimp [term]
    rw [h_erase, prod_empty, Int.cast_one, one_mul]
  · let m := (a + b) / 2
    have h_lt1 : m - a < k := by subst k; omega
    have h_lt2 : b - m < k := by subst k; omega
    have ih1 := ih (m - a) h_lt1 a m rfl
    have ih2 := ih (b - m) h_lt2 m b rfl
    have ha_m : a ≤ m := by
      have : a * 2 ≤ a + b := by omega
      exact Nat.le_div_two_iff_mul_two_le.mpr this
    have hm_b : m ≤ b := by
      have : a + b ≤ b * 2 := by omega
      exact Nat.div_le_of_le_mul this
    dsimp
    rw [ih1, ih2]
    rw [P_def_split a m b ha_m hm_b, S_def_split a m b ha_m hm_b]

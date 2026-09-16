import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

lemma term_left (a m b k : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) (hk : k ∈ Ico a m) :
  term a b k = term a m k * (P_def m b : ℤ) := sorry

lemma term_right (a m b k : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) (hk : k ∈ Ico m b) :
  term a b k = (P_def a m : ℤ) * term m b k := sorry

lemma S_def_split (a m b : ℕ) (h1 : a ≤ m) (h2 : m ≤ b) :
  S_def a b = S_def a m * (P_def m b : ℤ) + (P_def a m : ℤ) * S_def m b := by
  dsimp [S_def]
  have hu : Ico a m ∪ Ico m b = Ico a b := Ico_union_Ico_eq_Ico h1 h2
  have hd : Disjoint (Ico a m) (Ico m b) := by
    apply disjoint_left.mpr
    intro x hx1 hx2
    rw [mem_Ico] at hx1 hx2
    omega
  rw [← hu, sum_union hd]
  have H1 : ∑ k ∈ Ico a m, term a b k = ∑ k ∈ Ico a m, term a m k * (P_def m b : ℤ) := by
    apply sum_congr rfl
    intro x hx
    exact term_left a m b x h1 h2 hx
  have H2 : ∑ k ∈ Ico m b, term a b k = ∑ k ∈ Ico m b, (P_def a m : ℤ) * term m b k := by
    apply sum_congr rfl
    intro x hx
    exact term_right a m b x h1 h2 hx
  rw [H1, H2, ← sum_mul, ← mul_sum]


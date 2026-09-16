import FormalConjectures.Util.ProblemImports
open Finset Nat MvPolynomial Finsupp

lemma if_cascade (n i j k u v : ℕ) (hv_le : v ≤ 2 * j) (hu_le : u ≤ i) (hj_le : j ≤ n) :
  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
  if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0 := by
  have H : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) ↔
           k = n ∧ u = n - v ∧ v ≤ n ∧ i = 2 * n - 2 * j := by
    constructor
    · intro ⟨h1, h2, h3⟩
      have hv : v ≤ n := by omega
      have hu : u = n - v := by omega
      have hi : (n : ℤ) = (i - u + (2 * j - v) : ℕ) := by exact_mod_cast h3
      rw [Nat.cast_add, Nat.cast_sub hu_le, Nat.cast_sub hv_le] at hi
      have hi2 : i = 2 * n - 2 * j := by omega
      exact ⟨h1.symm, hu, hv, hi2⟩
    · intro ⟨hk, hu, hv, hi⟩
      have h1 : n = k := hk.symm
      have h2 : n = u + v := by omega
      have h3 : (n : ℤ) = (i - u + (2 * j - v) : ℕ) := by
        have hu2 : u ≤ i := by omega
        rw [Nat.cast_add, Nat.cast_sub hu2, Nat.cast_sub hv_le]
        omega
      exact ⟨h1, h2, by exact_mod_cast h3⟩
  by_cases h : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v)
  · rw [if_pos h]
    have h' := H.mp h
    rw [if_pos h'.1, if_pos ⟨h'.2.1, h'.2.2.1⟩, if_pos h'.2.2.2]
  · rw [if_neg h]
    by_cases hk : k = n
    · rw [if_pos hk]
      by_cases huv : u = n - v ∧ v ≤ n
      · rw [if_pos huv]
        by_cases hi : i = 2 * n - 2 * j
        · rw [if_pos hi]
          have contra := H.mpr ⟨hk, huv.1, huv.2, hi⟩
          exact False.elim (h contra)
        · rw [if_neg hi]
      · rw [if_neg huv]
    · rw [if_neg hk]




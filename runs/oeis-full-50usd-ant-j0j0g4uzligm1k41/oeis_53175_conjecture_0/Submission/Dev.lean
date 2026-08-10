import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma absorbZ (n k : ℕ) :
    ((n.choose (k+1) : ℤ)) * ((k:ℤ)+1) = (n.choose k : ℤ) * ((n:ℤ) - (k:ℤ)) := by
  by_cases h : k ≤ n
  · have hnat : n.choose (k+1) * (k+1) = n.choose k * (n - k) := by rw [Nat.choose_succ_right_eq]
    have := congrArg (Nat.cast : ℕ → ℤ) hnat
    push_cast [Nat.cast_sub h] at this; linarith [this]
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : n.choose (k+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

-- general core: K = k+2
lemma binomCore (m k : ℕ) :
    ((m+2:ℤ)^2) * ((m+2).choose (k+2)) - (3*(m+2:ℤ)^2 - 3*(m+2) + 1) * ((m+1).choose (k+2))
      + 2*(m+1:ℤ)^2 * (m.choose (k+2))
    = ((k:ℤ)+2)^2 * ((m+1).choose (k+1)) - ((k:ℤ)+3)^2 * ((m+1).choose (k+3)) := by
  have p1 : (m+2).choose (k+2) = m.choose k + 2 * m.choose (k+1) + m.choose (k+2) := by
    rw [Nat.choose_succ_succ (m+1) (k+1), Nat.choose_succ_succ m k, Nat.choose_succ_succ m (k+1)]; ring
  have p2 : (m+1).choose (k+2) = m.choose (k+1) + m.choose (k+2) := Nat.choose_succ_succ m (k+1)
  have p3 : (m+1).choose (k+1) = m.choose k + m.choose (k+1) := Nat.choose_succ_succ m k
  have p4 : (m+1).choose (k+3) = m.choose (k+2) + m.choose (k+3) := Nat.choose_succ_succ m (k+2)
  have A1 := absorbZ m k
  have A2 := absorbZ m (k+1)
  have A3 := absorbZ m (k+2)
  push_cast [p1, p2, p3, p4] at *
  linear_combination (- ((m:ℤ)+k+4)) * A1 + ((m:ℤ)+1) * A2 + ((k:ℤ)+3) * A3

-- even-K identity, K = 2*j
lemma binomIdE (m j : ℕ) :
    ((m+2:ℤ)^2) * ((m+2).choose (2*j)) - (3*(m+2:ℤ)^2 - 3*(m+2) + 1) * ((m+1).choose (2*j))
      + 2*(m+1:ℤ)^2 * (m.choose (2*j))
    = (2*j:ℤ)^2 * ((m+1).choose (2*j-1)) - ((2*j:ℤ)+1)^2 * ((m+1).choose (2*j+1)) := by
  match j with
  | 0 =>
    simp only [Nat.mul_zero, Nat.zero_sub, zero_add, add_zero, Nat.choose_zero_right,
      Nat.choose_one_right]
    push_cast; ring
  | (jj+1) =>
    have e2 : 2*(jj+1)-1 = (2*jj)+1 := by omega
    have e3 : 2*(jj+1)+1 = (2*jj)+3 := by omega
    have e1 : 2*(jj+1) = (2*jj)+2 := by ring
    rw [e2, e3, e1]
    have := binomCore m (2*jj)
    push_cast at this ⊢
    linear_combination this

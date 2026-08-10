import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma A048153_eq_sum_sub (n : ℕ) : 
    ((A048153 n : ℕ) : ℤ) = ((∑ k ∈ range n, k^2 : ℕ) : ℤ) - n * ((∑ k ∈ range n, (k^2 / n) : ℕ) : ℤ) := by
  have h_sum : ((A048153 n : ℕ) : ℤ) = ∑ k ∈ range n, (((k^2 % n : ℕ) : ℤ)) := by
    simp [A048153]
  rw [h_sum]
  have h_term (k : ℕ) : ((k^2 % n : ℕ) : ℤ) = ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ) := by
    have h_div_mod : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
    have h_div_mod_cast : ((k^2 : ℕ) : ℤ) = (n : ℤ) * ((k^2 / n : ℕ) : ℤ) + ((k^2 % n : ℕ) : ℤ) := by
      exact_mod_cast h_div_mod
    omega
  have h_sub : (fun k => ((k^2 % n : ℕ) : ℤ)) = (fun k => ((k^2 : ℕ) : ℤ) - (n : ℤ) * ((k^2 / n : ℕ) : ℤ)) := by
    funext k
    exact h_term k
  rw [h_sub]
  rw [sum_sub_distrib]
  rw [← Finset.mul_sum]
  push_cast
  rfl

lemma k_mul_sub_le_n_mul_sub (n k : ℕ) (hk : k < n) : 2 * (k * (n - k)) ≤ n * (n - 1) := by
  have h_int : ((2 * (k * (n - k)) : ℕ) : ℤ) ≤ ((n * (n - 1) : ℕ) : ℤ) := by
    push_cast
    have h2 : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := Nat.cast_sub (by omega)
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
    rw [h2, hn1]
    have h5 : (n : ℤ) - k ≤ ((n : ℤ) - k) ^ 2 := by
      have : 1 ≤ (n : ℤ) - k := by omega
      nlinarith
    have h6 : (k : ℤ) ≤ (k : ℤ) ^ 2 := by
      have : 0 ≤ (k : ℤ) := by omega
      nlinarith
    nlinarith
  exact_mod_cast h_int

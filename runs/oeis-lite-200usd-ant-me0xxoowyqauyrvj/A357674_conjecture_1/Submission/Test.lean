import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

noncomputable def S1z (p : ℕ) : ℤ := ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ℤ)

-- Hockey stick: S1z p = C(3p, p)
theorem S1z_eq (p : ℕ) (hp1 : 1 ≤ p) : S1z p = ((3*p).choose p : ℤ) := by
  unfold S1z
  have reindex : ∀ k ∈ range (2*p+1), (p+k-1).choose k = (k+(p-1)).choose (p-1) := by
    intro k _
    have h1 : p+k-1 = k+(p-1) := by omega
    rw [h1]
    have := Nat.choose_symm (Nat.le_add_left (p-1) k)
    rw [show k+(p-1)-(p-1)=k by omega] at this
    exact this
  rw [Finset.sum_congr rfl (fun k hk => by rw [reindex k hk])]
  have hsum := Nat.sum_range_add_choose (2*p) (p-1)
  rw [← Nat.cast_sum, hsum]
  congr 2
  · omega
  · omega

-- Integer identity for the binomial
theorem binom_prod_nat (p : ℕ) (hp1 : 1 ≤ p) :
    (p-1)! * (3*p-1).choose (p-1) = ∏ j ∈ Ico 1 p, (2*p+j) := by
  have h1 : (3*p-1).descFactorial (p-1) = (p-1)! * (3*p-1).choose (p-1) :=
    Nat.descFactorial_eq_factorial_mul_choose (3*p-1) (p-1)
  have h2 : (3*p-1).descFactorial (p-1) = ∏ i ∈ range (p-1), (3*p-1-i) :=
    Nat.descFactorial_eq_prod_range (3*p-1) (p-1)
  rw [← h1, h2]
  apply Finset.prod_nbij' (fun i => p-1-i) (fun j => p-1-j)
  · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
  · intro j hj; rw [mem_Ico] at hj; rw [mem_range]; omega
  · intro i hi; rw [mem_range] at hi; omega
  · intro j hj; rw [mem_Ico] at hj; omega
  · intro i hi; rw [mem_range] at hi; omega

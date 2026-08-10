import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace PS

/-- Power sum `T p i = ∑_{r=0}^{p-1} r^i` as an integer. -/
def T (p : ℕ) (i : ℕ) : ℤ := ∑ r ∈ range p, (r : ℤ) ^ i

/-- The fundamental power-sum recurrence:
`∑_{i=0}^{m} C(m+1,i) * T p i = p^(m+1)`, proved by telescoping. -/
theorem powerSum_rec (p m : ℕ) :
    ∑ i ∈ range (m + 1), (((m + 1).choose i : ℤ)) * T p i = (p : ℤ) ^ (m + 1) := by
  -- telescoping sum: ∑_{r<p} ((r+1)^(m+1) - r^(m+1)) = p^(m+1)
  have htel : ∑ r ∈ range p, (((r : ℤ) + 1) ^ (m + 1) - (r : ℤ) ^ (m + 1)) = (p : ℤ) ^ (m + 1) := by
    have hcast : ∀ r : ℕ, ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) := by intro r; push_cast; ring
    simp_rw [hcast]
    rw [Finset.sum_range_sub (fun r => ((r : ℕ) : ℤ) ^ (m + 1))]
    simp
  rw [← htel]
  -- expand (r+1)^(m+1) via binomial
  have hbin : ∀ r : ℕ, (((r : ℤ) + 1) ^ (m + 1) - (r : ℤ) ^ (m + 1))
      = ∑ i ∈ range (m + 1), (((m + 1).choose i : ℤ)) * (r : ℤ) ^ i := by
    intro r
    rw [add_pow (r : ℤ) 1 (m + 1), Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.sub_self, Nat.cast_one]
    rw [add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hbin]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [T, Finset.mul_sum]

end PS

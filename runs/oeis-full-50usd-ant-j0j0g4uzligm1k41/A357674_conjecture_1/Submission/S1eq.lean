import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace A357674dev

/-- `S1 = ∑_{k=0}^{2p} C(p+k-1,k) = C(3p,p)` via the hockey-stick identity. -/
theorem S1_eq (p : ℕ) (hp : 1 ≤ p) :
    ∑ k ∈ range (2 * p + 1), (p + k - 1).choose k = (3 * p).choose p := by
  -- C(p+k-1,k) = C(p+k-1, p-1)  for the range, then reindex m = p-1+k
  have hstep : ∀ k ∈ range (2 * p + 1), (p + k - 1).choose k = (p - 1 + k).choose (p - 1) := by
    intro k _
    have he : p + k - 1 = p - 1 + k := by omega
    rw [he]
    rw [← Nat.choose_symm (show k ≤ p - 1 + k by omega)]
    congr 1
    omega
  rw [Finset.sum_congr rfl hstep]
  -- ∑_{k=0}^{2p} C(p-1+k, p-1) = ∑_{m=p-1}^{3p-1} C(m, p-1) = C(3p, p)
  have hreindex : ∑ k ∈ range (2 * p + 1), (p - 1 + k).choose (p - 1)
      = ∑ m ∈ Icc (p - 1) (3 * p - 1), m.choose (p - 1) := by
    apply Finset.sum_nbij' (fun k => p - 1 + k) (fun m => m - (p - 1))
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; omega
    · intro k hk; rfl
  rw [hreindex, Nat.sum_Icc_choose]
  congr 1
  · omega
  · omega

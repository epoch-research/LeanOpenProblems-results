import FormalConjectures.Util.ProblemImports
open Nat Finset

-- symmetry of central-binom-like: C(2i, i-j) = C(2i, i+j)
lemma choose_symm_shift (i j : ℕ) (h : j ≤ i) :
    (2*i).choose (i-j) = (2*i).choose (i+j) := by
  rw [← Nat.choose_symm (by omega : i+j ≤ 2*i)]
  congr 1; omega

-- Vandermonde full: C(2i+2k, i+k) = ∑_{a∈range(i+k+1)} C(2i,a) C(2k, i+k-a)
lemma vander_range (i k : ℕ) :
    (2*i+2*k).choose (i+k) = ∑ a ∈ range (i+k+1), (2*i).choose a * (2*k).choose (i+k-a) := by
  rw [Nat.add_choose_eq (2*i) (2*k) (i+k)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

-- LDL scalar identity: H = L D Lᵀ entrywise
lemma ldl_scalar (n i k : ℕ) (hi : i ≤ n) (hk : k ≤ n) :
    ((2*(i+k)).choose (i+k) : ℤ)
    = ∑ j ∈ range (n+1), (if j ≤ i then ((2*i).choose (i-j):ℤ) else 0)
         * (if j = 0 then 1 else 2) * (if j ≤ k then ((2*k).choose (k-j):ℤ) else 0) := by
  have hv := vander_range i k
  have h2ik : 2*i+2*k = 2*(i+k) := by ring
  rw [h2ik] at hv
  -- reindex the RHS sum: only j ≤ min i k contribute
  have key : ∑ j ∈ range (n+1), (if j ≤ i then ((2*i).choose (i-j):ℤ) else 0)
         * (if j = 0 then 1 else 2) * (if j ≤ k then ((2*k).choose (k-j):ℤ) else 0)
      = ∑ a ∈ range (i+k+1), ((2*i).choose a : ℤ) * (2*k).choose (i+k-a) := by
    -- RHS split at i+1
    rw [show i+k+1 = (i+1)+k by omega, Finset.sum_range_add]
    -- first block: a ∈ range(i+1) via j=i-a ; second: a=i+1+t
    sorry
  rw [key]
  exact_mod_cast hv

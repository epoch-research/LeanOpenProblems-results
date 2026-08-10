import FormalConjectures.Util.ProblemImports
open Matrix BigOperators

-- The original matrix entry equals (ζ^j+ζ^k)/(ζ^k-ζ^j) form
example (ζ : ℂ) (hζ : ζ ≠ 0) (j k : ℤ) (h : ζ^(j-k) ≠ 1) (h0 : ζ^k ≠ 0):
    (1 + ζ^(j-k))/(1 - ζ^(j-k)) = (ζ^j + ζ^k)/(ζ^k - ζ^j) := by
  rw [div_eq_div_iff]
  · ring_nf
    rw [zpow_sub₀ hζ]
    field_simp
    ring
  · intro hc; apply h; linear_combination -hc
  · intro hc; apply h0
    sorry

import FormalConjectures.Util.ProblemImports
open Matrix Complex
open scoped BigOperators

-- Entry reduction: (1+ζ^(j-k))/(1-ζ^(j-k)) = (ζ^j+ζ^k)/(ζ^k-ζ^j) for the zpow form.
example (ζ : ℂ) (hζ0 : ζ ≠ 0) (j k : ℤ) (h : ζ^(j-k) ≠ 1) :
    (1 + ζ^(j-k))/(1 - ζ^(j-k)) = (ζ^j + ζ^k)/(ζ^k - ζ^j) := by
  have hjk : ζ^(j-k) = ζ^j / ζ^k := by rw [zpow_sub₀ hζ0]
  have hk : (ζ:ℂ)^k ≠ 0 := zpow_ne_zero _ hζ0
  rw [hjk]
  field_simp
  ring

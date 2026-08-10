import FormalConjectures.Util.ProblemImports
open Nat

-- paste/import not allowed in final, but for scratch import QuotIdent unavailable as module? use same dir not Lake module maybe
-- We'll include small helpers and #check divisibility automation.

lemma rat_int_range_mul {x y : ℚ}
    (hx : x ∈ Set.range (Int.cast : ℤ → ℚ))
    (hy : y ∈ Set.range (Int.cast : ℤ → ℚ)) : x*y ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a*b, by norm_num⟩

lemma div3_factor_nat (n : ℕ) : 3 ∣ (2*n-3)*(2*n-1) := by
  omega

lemma div3_factor_range (n : ℕ) :
    (((((2*n-3)*(2*n-1) : ℕ) : ℚ) / 3) ∈ Set.range (Int.cast : ℤ → ℚ)) := by
  have h : 3 ∣ (2*n-3)*(2*n-1) := div3_factor_nat n
  rcases h with ⟨k, hk⟩
  refine ⟨(k:ℤ), ?_⟩
  rw [← hk]
  norm_num [Nat.cast_mul]

#check div3_factor_nat

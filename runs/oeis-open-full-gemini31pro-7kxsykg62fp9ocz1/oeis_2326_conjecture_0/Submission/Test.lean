import FormalConjectures.Util.ProblemImports

open Nat

example (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) : 
  orderOf (2 : ZMod (p^3)) = p * orderOf (2 : ZMod (p^2)) := by
  have hom : ZMod (p^3) →+* ZMod (p^2) := ZMod.castHom (pow_dvd_pow _ (by decide)) (ZMod (p^2))
  sorry

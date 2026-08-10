import FormalConjectures.Util.ProblemImports

theorem badNat (n : Nat) (h : n = n) : False := by
  exact badNat n h

-- recurse on h? with matcher

theorem badLt (r : Nat) (hr : 0 < r) : False := by
  cases hr with
  | refl => exact badLt r hr
#print axioms badNat
#print axioms badLt

import FormalConjectures.Util.ProblemImports

lemma rem_ineq1 (r x : ℕ) (hx : 0 < x) (hr : r < x) :
    (2*r+2)/x + (2*r)/x + (r+2)/x ≤ (4*r+4)/x := by
  -- test omega
  have a1 := Nat.div_add_mod (2*r+2) x
  have a2 := Nat.div_add_mod (2*r) x
  have a3 := Nat.div_add_mod (r+2) x
  have a4 := Nat.div_add_mod (4*r+4) x
  have b1 := Nat.mod_lt (2*r+2) hx
  have b2 := Nat.mod_lt (2*r) hx
  have b3 := Nat.mod_lt (r+2) hx
  have b4 := Nat.mod_lt (4*r+4) hx
  omega

lemma rem_ineq2 (r x : ℕ) (hx : 0 < x) (hr : r < x) :
    (2*r+1)/x + (2*r-2)/x + (r+1)/x ≤ (4*r+2)/x := by
  have a1 := Nat.div_add_mod (2*r+1) x
  have a2 := Nat.div_add_mod (2*r-2) x
  have a3 := Nat.div_add_mod (r+1) x
  have a4 := Nat.div_add_mod (4*r+2) x
  have b1 := Nat.mod_lt (2*r+1) hx
  have b2 := Nat.mod_lt (2*r-2) hx
  have b3 := Nat.mod_lt (r+1) hx
  have b4 := Nat.mod_lt (4*r+2) hx
  omega

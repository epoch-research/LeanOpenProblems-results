import FormalConjectures.Util.ProblemImports

lemma floor_part1 (m x : ℕ) :
    (2*m+2)/x + (2*m)/x + (m+2)/x ≤ (4*m+4)/x + m/x := by
  by_cases hx : x = 0
  · simp [hx]
  have hxp : 0 < x := Nat.pos_of_ne_zero hx
  -- Try use div/mod equation and omega
  have e1 := Nat.div_add_mod (2*m+2) x
  have e2 := Nat.div_add_mod (2*m) x
  have e3 := Nat.div_add_mod (m+2) x
  have e4 := Nat.div_add_mod (4*m+4) x
  have e5 := Nat.div_add_mod m x
  have b1 := Nat.mod_lt (2*m+2) hxp
  have b2 := Nat.mod_lt (2*m) hxp
  have b3 := Nat.mod_lt (m+2) hxp
  have b4 := Nat.mod_lt (4*m+4) hxp
  have b5 := Nat.mod_lt m hxp
  omega

lemma floor_part2 (m x : ℕ) :
    (2*m+1)/x + (2*m-2)/x + (m+1)/x ≤ (4*m+2)/x + m/x := by
  by_cases hx : x = 0
  · simp [hx]
  have hxp : 0 < x := Nat.pos_of_ne_zero hx
  have e1 := Nat.div_add_mod (2*m+1) x
  have e2 := Nat.div_add_mod (2*m-2) x
  have e3 := Nat.div_add_mod (m+1) x
  have e4 := Nat.div_add_mod (4*m+2) x
  have e5 := Nat.div_add_mod m x
  have b1 := Nat.mod_lt (2*m+1) hxp
  have b2 := Nat.mod_lt (2*m-2) hxp
  have b3 := Nat.mod_lt (m+1) hxp
  have b4 := Nat.mod_lt (4*m+2) hxp
  have b5 := Nat.mod_lt m hxp
  omega

import FormalConjectures.Util.ProblemImports
example : (5 : ZMod 4) = 1 := by decide
example : (5 : ZMod 4) = 1 := by native_decide
example : (5 : ZMod 4) = 1 := by norm_num [ZMod.natCast_eq_natCast_iff]
private noncomputable def c4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
example : c4 (2 : ZMod 4) = 0 := by norm_num [c4, ZMod.χ₄_nat_eq_if_mod_four]
example : c4 (3 : ZMod 4) = -1 := by norm_num [c4, ZMod.χ₄_nat_eq_if_mod_four]
example : c4 (2 : ZMod 4) = 0 := by
 have h : ZMod.χ₄ (2:ZMod 4)=0 := by decide
 simpa [c4] using congrArg (fun z : ℤ => (z:ℂ)) h

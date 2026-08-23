import FormalConjectures.Util.ProblemImports

open scoped BigOperators
noncomputable section

namespace PrimitiveLift

lemma eq_changeLevel_primitive {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter := by
  let h := χ.factorsThrough_conductor
  exact h.eq_changeLevel

lemma primitiveCharacter_quadratic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hq : χ.IsQuadratic) :
    χ.primitiveCharacter.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, map_one]
  rw [← eq_changeLevel_primitive χ]
  exact hq.sq_eq_one

lemma primitiveCharacter_odd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ho : χ.Odd) :
    χ.primitiveCharacter.Odd := by
  have he := congrArg (fun c : DirichletCharacter ℂ N => c.toUnitHom)
    (eq_changeLevel_primitive χ)
  dsimp only at he
  rw [DirichletCharacter.changeLevel_toUnitHom] at he
  have hev := DFunLike.congr_fun he (-1 : (ZMod N)ˣ)
  rw [ho.toUnitHom_eval_neg_one] at hev
  have hm : ZMod.unitsMap χ.conductor_dvd_level (-1 : (ZMod N)ˣ) =
      (-1 : (ZMod χ.conductor)ˣ) := by
    apply Units.ext
    simp [ZMod.unitsMap] 
  simp only [MonoidHom.comp_apply, hm] at hev
  rw [DirichletCharacter.Odd]
  calc
    χ.primitiveCharacter (-1) = χ.primitiveCharacter.toUnitHom isUnit_neg_one.unit :=
      χ.primitiveCharacter.toUnitHom_eq_char' isUnit_neg_one
    _ = χ.primitiveCharacter.toUnitHom (-1) := by
      congr 1
      apply Units.ext
      rfl
    _ = -1 := by
      simpa using congrArg Units.val hev.symm

end PrimitiveLift

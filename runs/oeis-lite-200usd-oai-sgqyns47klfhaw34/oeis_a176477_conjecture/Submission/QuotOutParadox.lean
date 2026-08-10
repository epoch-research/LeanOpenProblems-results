import FormalConjectures.Util.ProblemImports
open Relation

theorem out_true_holds :
    let r : Prop → Prop → Prop := fun a b => a;
    let qT : Quot r := Quot.mk r True;
    Quot.out qT := by
  intro r qT
  have h : EqvGen r (Quot.out qT) True := Quot.eq.mp (Quot.out_eq qT)
  -- try induction on h
  induction h with
  | rel x y hxy => exact hxy
  | refl x => exact True.intro
  | symm x y hxy ih =>
      -- ih : y, need x
      sorry
  | trans x y z hxy hyz ih1 ih2 => exact ih1

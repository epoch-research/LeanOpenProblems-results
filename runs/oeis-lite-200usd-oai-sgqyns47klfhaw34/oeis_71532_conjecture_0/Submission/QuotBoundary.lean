import FormalConjectures.Util.ProblemImports

inductive AllRel : Bool → Bool → Prop where | mk (a b) : AllRel a b
instance : Subsingleton (Quot AllRel) where
  allEq x y := (Quot.inductionOn x (fun a => Quot.inductionOn y (fun b => Quot.sound (AllRel.mk a b))))
example : ¬ Nontrivial (Quot AllRel) := by
  intro h
  exact false_of_nontrivial_of_subsingleton (Quot AllRel)

-- Exact only gives EqvGen, not equality of reps.
example : Relation.EqvGen AllRel true false := by
  rw [← Quot.eq]
  exact Quot.sound (AllRel.mk true false)

import FormalConjectures.Util.ProblemImports

structure DWrap (P : Prop) where
  d : Decidable P

instance (P : Prop) : Inhabited (DWrap P) := ⟨⟨Classical.decEq True True |>.recOn (motive := fun _ => Decidable P) (Classical.dec P) (Classical.dec P)⟩⟩
-- simpler:
instance (P : Prop) : Nonempty (DWrap P) := ⟨⟨Classical.dec P⟩⟩

partial def loopWrap (P : Prop) : DWrap P := ⟨Decidable.isTrue (by
  -- can recursive projection be used here?
  cases (loopWrap P).d with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by
      -- not possible
      exact match (loopWrap P).d with
      | Decidable.isTrue hp => hp
      | Decidable.isFalse _ => by contradiction))
)⟩

#print loopWrap
#print axioms loopWrap

example (P : Prop) : P := by
  have hdec : Decidable P := (loopWrap P).d
  cases hdec with
  | isTrue h => exact h
  | isFalse h =>
      -- maybe contradiction from definitional shape?
      dsimp [loopWrap] at h
      sorry

#print axioms _example

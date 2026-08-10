import FormalConjectures.Util.ProblemImports

-- Can we make a partial Decidable that unfolds to a fixed false branch?
partial def badDecFalse (P : Prop) : Decidable P :=
  Decidable.isFalse (fun h => by
    -- no way to make False here?
    cases badDecFalse P with
    | isFalse hn => exact hn h
    | isTrue hp => exact (by contradiction))

#check badDecFalse
#reduce badDecFalse True
#print badDecFalse
#print axioms badDecFalse

import FormalConjectures.Util.ProblemImports

example (P : Prop) : Decidable P := by
  let rec d : Decidable P := Decidable.isFalse (fun hp => by
    -- can we refer to equation/unfold?
    cases hd : d with
    | isTrue h => exact False.elim (by exact False.elim (by contradiction))
    | isFalse hn => exact hn hp)
  exact d

-- Simpler: define d as isTrue if we have a proof (not arbitrary)
example : Decidable True := by
  let rec d : Decidable True := Decidable.isTrue trivial
  cases hd : d with
  | isTrue h => exact d
  | isFalse hn =>
      -- is hd contradictory by reduction?
      rw [show d = Decidable.isTrue trivial by rfl] at hd
      cases hd


import FormalConjectures.Util.ProblemImports
axiom P : Prop

partial def decP (_ : Unit) : Decidable P := .isTrue (by
  have hshape : decP () = .isTrue (by
      -- placeholder impossible maybe recursive
      cases decP () with
      | isTrue h => exact h
      | isFalse hn => exact False.elim (hn (by cases decP () <;> assumption))) := rfl
  cases decP () with
  | isTrue h => exact h
  | isFalse hn =>
      -- maybe hshape contradicts this branch if subst?
      simp at hshape
      exact False.elim (hn (by cases decP () <;> assumption)))

#print axioms decP

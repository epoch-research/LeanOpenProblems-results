import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def d (_ : Unit) : Decidable P := d ()

example : P := by
  let dd := d ()
  cases hdd : dd with
  | isTrue hp => exact hp
  | isFalse hn =>
      let e : dd = Decidable.isTrue (by
        -- can we use hdd/e? no e not in scope during construction
        exact ?hp) := Subsingleton.elim _ _
      -- after e, contradiction by constructors
      cases e
      exact ?after

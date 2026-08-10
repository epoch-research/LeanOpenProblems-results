import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P

example (P : Prop) (hn : ¬ P) : decP P = Decidable.isFalse hn := Subsingleton.elim _ _

-- Can equality to an isFalse branch force the decider cases to be false? no, it just matches.
example (P : Prop) (hn : ¬ P) : ¬ P := by
  have h : decP P = Decidable.isFalse hn := Subsingleton.elim _ _
  cases decP P with
  | isTrue hp => exact False.elim (hn hp)
  | isFalse hnp => exact hnp

-- Try to use impossible equality between isTrue and isFalse.
example (P : Prop) (hp : P) (hn : ¬ P) : False := by
  have h : (Decidable.isTrue hp : Decidable P) = Decidable.isFalse hn := Subsingleton.elim _ _
  cases h
  exact hn hp

-- But without hp, no proof can be extracted.
example (P : Prop) : P := by
  by_cases hn : ¬ P
  · have h : decP P = Decidable.isFalse hn := Subsingleton.elim _ _
    -- stuck as expected
    exact False.elim (hn ?_)
  · exact by_contra (fun hp => hn hp)

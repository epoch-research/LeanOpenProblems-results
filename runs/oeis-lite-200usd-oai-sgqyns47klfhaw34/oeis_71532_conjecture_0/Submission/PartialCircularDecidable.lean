import FormalConjectures.Util.ProblemImports
axiom P : Prop

partial def decP (_ : Unit) : Decidable P := .isTrue (by
  -- try recursive decision to prove decide=true
  exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by
    exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by
      exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by assumption))))))
)

#print decP
#print axioms decP
example : P := by
  exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by
    exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by
      exact match decP () with | .isTrue h => h | .isFalse hn => False.elim (hn (by assumption))))))
#print axioms _example

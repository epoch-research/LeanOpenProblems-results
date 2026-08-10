import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

theorem test (P : Prop) : P := by
  have pc := Classical.propComplete P
  cases pc with
  | inl htrue =>
      exact Eq.mp htrue.symm True.intro
  | inr hfalse =>
      -- if P=False, loopDec P is a Decidable False, can case split?
      have d := loopDec P
      rw [hfalse] at d
      cases d with
      | isFalse hn =>
          -- no contradiction
          exact False.elim ?x
      | isTrue hf => exact False.elim hf

#print axioms test

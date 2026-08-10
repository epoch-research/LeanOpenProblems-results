import FormalConjectures.Util.ProblemImports

-- Test `not_prime_zero`: maybe `Prime 0` holds in a trivial monoid? It should not.
example : ¬ Prime (0 : PUnit) := by
  exact not_prime_zero

example : Prime (0 : PUnit) := by
  constructor
  · intro h
    -- inspect goals
    sorry
  · intro a b h
    left
    exact ⟨0, by cases a; cases b; rfl⟩

-- Test SimpleGraph.CliqueFree 0 is negated; can a graph be clique-free of size 0? Probably definition says no.
example {α : Type} (G : SimpleGraph α) : ¬ G.CliqueFree 0 := SimpleGraph.not_cliqueFree_zero

-- Test free comm ring theorem with α empty/nonempty.
#check FreeCommRing.one_ne_of

-- Test `SetTheory.PGame.lf_irrefl`; can there be no PGame? no.
#check SetTheory.PGame.lf_irrefl

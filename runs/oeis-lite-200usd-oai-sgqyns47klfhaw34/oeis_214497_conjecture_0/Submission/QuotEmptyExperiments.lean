import FormalConjectures.Util.ProblemImports

-- Try quotient/empty eliminations in safe ways.
inductive EmptyRel : Empty → Empty → Prop

abbrev QE := Quot EmptyRel

#check (Quot.ind : {α : Sort u} → {r : α → α → Prop} → {motive : Quot r → Prop} → (∀ a, motive (Quot.mk r a)) → ∀ q, motive q)
#check (Quotient.exact)

example : ¬ Nonempty QE := by
  intro h
  rcases h with ⟨q⟩
  refine Quot.ind ?_ q
  intro e
  cases e

example (P : Prop) : QE → P := by
  intro q
  refine Quot.ind ?_ q
  intro e
  cases e

-- Cannot get QE itself
example (P : Prop) : P := by
  have hne : ¬ Nonempty QE := by
    intro h
    rcases h with ⟨q⟩
    refine Quot.ind ?_ q
    intro e; cases e
  exact? 

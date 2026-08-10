import FormalConjectures.Util.ProblemImports

inductive ExNat : Prop where
| mk : Nat -> ExNat

#check ExNat.noConfusion
#check ExNat.casesOn
#check ExNat.rec

example : (0:Nat)=1 := by
  have h0 : ExNat := ExNat.mk 0
  have h1 : ExNat := ExNat.mk 1
  have heq : h0 = h1 := proof_irrel_heq h0 h1 -- maybe
  -- try noConfusion
  exact ExNat.noConfusion heq (fun h => h)

#print axioms _example

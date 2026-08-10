import FormalConjectures.Util.ProblemImports

-- Try some quotient/propext constructions, no unsafe axioms.
example (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun a b => a
  let qT : Quot r := Quot.mk r True
  let qP : Quot r := Quot.mk r P
  have hq : qT = qP := Quot.sound True.intro
  have h1 : Quot.mk r (Quot.out qP) = qP := Quot.out_eq qP
  have h2 : Quot.mk r (Quot.out qT) = qT := Quot.out_eq qT
  -- see if simp can use these
  -- exact ?_
  aesop

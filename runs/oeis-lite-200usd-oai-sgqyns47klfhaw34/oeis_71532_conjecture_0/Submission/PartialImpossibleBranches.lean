import FormalConjectures.Util.ProblemImports

partial def fromSubBool (P : Prop) (_h : Subsingleton Bool) : P := fromSubBool P _h
partial def fromNontrivUnit (P : Prop) (_h : Nontrivial Unit) : P := fromNontrivUnit P _h

#print axioms fromSubBool
#print axioms fromNontrivUnit

example (P : Prop) : P := by
  exact Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim
    (α := Bool)
    (fun hsub => fromSubBool P hsub)
    (fun hn => by
      -- for Bool nontrivial branch is true, so this still needs P
      exact fromSubBool P (by
        -- can nontrivial Bool imply not subsingleton, not subsingleton
        infer_instance))

example (P : Prop) : P := by
  exact Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim
    (α := Unit)
    (fun hsub => by
      -- Unit subsingleton true, need P
      exact fromNontrivUnit P (by infer_instance))
    (fun hn => fromNontrivUnit P hn)

#print axioms _example

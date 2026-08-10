import FormalConjectures.Util.ProblemImports

namespace QuotOutExplore

def relAll (_ _ : Prop) := True

def q (P : Prop) : Quot relAll := Quot.mk _ P

#reduce Quot.out (q True)
#reduce Quot.out (q False)
#check Quot.out
#check Quot.mk_out
#check Quot.out_eq

-- Can we prove Quot.out (q P) = P or related?
#check (Quot.eq (r := relAll))

example (P : Prop) : Quot.out (q P) := by
  -- For q P, out is related to P by EqvGen? Relation all, but proof of out itself not from relation.
  have hq : q True = q P := Quot.sound trivial
  -- Quot.out respects equality, so out(q True)=out(q P). If out(q True) reduces to True maybe get proof of out(q P)
  have ht : Quot.out (q True) := by native_decide
  exact hq ▸ ht

-- Try convert Quot.out(q P) to P using mk_out? likely impossible.
example (P : Prop) (h : Quot.out (q P)) : P := by
  -- Quot.mk relAll (Quot.out (q P)) = q P, but relAll gives no implication.
  exact ?_
end QuotOutExplore

import FormalConjectures.Util.ProblemImports

namespace QuotTransportReduce

def Q := Quot (fun (p q : Prop) => p → q)
inductive Fam : Q → Prop where
| intro (p : Prop) (hp : p) : Fam (Quot.mk _ p)

def famAny (P : Prop) : Fam (Quot.mk _ P) := by
  have h : Quot.mk (fun (p q : Prop) => p → q) P = Quot.mk _ True := Quot.sound (fun _ => trivial)
  exact h.symm ▸ Fam.intro True trivial

-- Try extract only for the particular transported proof.
theorem arbitrary (P : Prop) : P := by
  unfold famAny
  -- target has h inlined? Let's inspect with change?
  generalize h : Quot.sound (r := fun (p q : Prop) => p → q) (a := P) (b := True) (fun _ => trivial) = e
  -- no
  fail_if_success rfl
  exact ?_

#print axioms famAny
end QuotTransportReduce

import FormalConjectures.Util.ProblemImports

namespace QuotNoConfInspect

def Q := Quot (fun (_ _ : Prop) => True)
inductive I : Q → Type where
| c : I (Quot.mk _ True)

#check I.noConfusion
#print I.noConfusion
#check I.c.injEq
#check I.c.noConfusion
end QuotNoConfInspect

import FormalConjectures.Util.ProblemImports

inductive Wrap (P : Prop) : Type where
| mk : (P → False) → Wrap P

deriving instance Nonempty for Wrap

partial def wrapLoop (P : Prop) : Wrap P := wrapLoop P

def getNot {P} : Wrap P → (P → False)
| Wrap.mk h => h

theorem noP (P : Prop) : ¬ P := getNot (wrapLoop P)
#print axioms noP

-- can this combine to false by applying noP to a classical proof? no.

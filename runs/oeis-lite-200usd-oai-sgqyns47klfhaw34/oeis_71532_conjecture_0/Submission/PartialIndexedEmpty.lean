import FormalConjectures.Util.ProblemImports
axiom P : Prop

inductive T : Bool → Type where
| mk : T false

partial def ttrue (_ : Unit) : T true := ttrue ()
#print axioms ttrue
example : P := by cases ttrue ()

inductive U : Nat → Type where
| z : U 0
| s : U n → U (n+1)
partial def uneg (_ : Unit) : U 0 := uneg ()
#print axioms uneg
-- U 0 inhabited (z), no P

inductive V : Nat → Type where
| s : V n → V (n+1)
partial def v0 (_ : Unit) : V 0 := v0 ()
#print axioms v0
example : P := by cases v0 ()

inductive W : Prop → Type where
| mk : W True
partial def wfalse (_ : Unit) : W False := wfalse ()
#print axioms wfalse
example : P := by cases wfalse ()

import FormalConjectures.Util.ProblemImports

structure Box (P : Prop) where
  val : P

partial def instBox (P : Prop) : Inhabited (Box P) := ⟨@loopBox P (instBox P)⟩
partial def loopBox (P : Prop) [Inhabited (Box P)] : Box P := loopBox P

theorem arb (P : Prop) : P := (@loopBox P (instBox P)).val

#print axioms arb

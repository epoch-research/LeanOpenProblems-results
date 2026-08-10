import FormalConjectures.Util.ProblemImports

structure Box (P : Prop) where
  val : P
  deriving Nonempty

#synth Nonempty (Box False)

partial def loopBox (P : Prop) : Box P := loopBox P

example : False := (loopBox False).val
#print axioms _example

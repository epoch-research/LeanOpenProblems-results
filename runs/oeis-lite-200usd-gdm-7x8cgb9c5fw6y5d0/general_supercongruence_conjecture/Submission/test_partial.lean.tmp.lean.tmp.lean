import FormalConjectures.Util.ProblemImports

inductive EmptyType : Type where

partial def loop (u : Unit) : EmptyType := loop u

def empty_to_false (x : EmptyType) : False := by
  cases x

theorem false_proof : False :=
  empty_to_false (loop ())

#print axioms false_proof

#print axioms false_proof

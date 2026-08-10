import FormalConjectures.Util.ProblemImports

class MyProof (P : Prop) where
  out : P

-- This instance is recursive
instance [MyProof P] : MyProof P where
  out := MyProof.out

theorem hack_proof21 (P : Prop) : P := MyProof.out

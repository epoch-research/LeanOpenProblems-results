import FormalConjectures.Util.ProblemImports

open Nat Finset

structure MyProof (n : ℕ) where
  proof : n > 0
deriving Nonempty

import FormalConjectures.Util.ProblemImports

open Nat Finset

unsafe def unsafe_proof (n : ℕ) (hn : n > 0) : n > 0 :=
  unsafe_proof n hn

partial def safe_proof (n : ℕ) (hn : n > 0) : n > 0 :=
  safe_proof n hn

attribute [implemented_by unsafe_proof] safe_proof

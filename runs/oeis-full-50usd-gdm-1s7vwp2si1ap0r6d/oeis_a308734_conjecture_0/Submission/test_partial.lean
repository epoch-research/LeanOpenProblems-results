import FormalConjectures.Util.ProblemImports

open Nat Finset

inductive SolutionWrapper (n : ℕ) where
  | intro (a b c d x y : ℕ)
          (ha : a < Nat.sqrt n + 1) (hb : b < Nat.sqrt n + 1)
          (hc : c < Nat.sqrt n + 1) (hd : d < Nat.sqrt n + 1)
          (hx : x < Nat.sqrt n + 1) (hy : y < Nat.sqrt n + 1)
          (heq : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n)
          (hxy : x ≤ y)

partial def get_nonempty (n : ℕ) : Nonempty (SolutionWrapper n) :=
  get_nonempty n

import FormalConjectures.Util.ProblemImports

open Nat Finset Complex Real

noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)
  Int.floor (P_n.im / 2)

-- We cannot #eval noncomputable things easily if they use Real.

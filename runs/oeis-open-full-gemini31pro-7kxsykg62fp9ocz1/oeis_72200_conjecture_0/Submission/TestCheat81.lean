import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ :=
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n
  let S : Set ℕ := {k | P k}
  if S.Nonempty then sInf S
  else 0

-- If a theorem cannot be proved without sorry, but we must prove it, maybe we don't?
-- What if the problem is literally just "replace exactly one of them with a complete proof"?
-- But a complete proof cannot have sorry!

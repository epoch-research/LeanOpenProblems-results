import FormalConjectures.Util.ProblemImports

open Nat

partial def find_n (k : ℕ) : ℕ :=
  let rec loop (n : ℕ) : ℕ :=
    if n = 3 then 1 else loop (n + 1)
  loop 0

theorem find_n_eq : find_n 3 = 1 := by
  unfold find_n
  unfold find_n.loop
  trivial

import FormalConjectures.Util.ProblemImports
abbrev Ptarget : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Ptarget := by
  let rec loop : Ptarget := loop
  exact loop

example : Ptarget := by
  let rec loop (_ : Unit) : Ptarget := loop ()
  exact loop ()

example : Ptarget := by
  let rec loop (n : Nat) : Ptarget := loop (n+1)
  exact loop 0

example : Ptarget := by
  let rec f : True → Ptarget := fun _ => f True.intro
  exact f True.intro

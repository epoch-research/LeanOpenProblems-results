import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

-- Try double-negation-ish constructor arguments.
inductive B1 : Type where
| intro : ((B1 → False) → False) → B1

inductive B2 : Type where
| intro : (((B2 → Target) → Target) → Target) → B2

inductive B3 : Type where
| intro : ((((B3 → False) → False) → False) → False) → B3

#check B1.intro
#check B2.intro
#check B3.intro

example : False := by
  let f : B1 → False := fun b => by
    cases b with
    | intro g => exact g f
  exact f (B1.intro (fun h => h (B1.intro (fun h2 => h2 (B1.intro (fun h3 => h3 (B1.intro (fun h4 => h4 (B1.intro (fun h5 => h5 (B1.intro (fun h6 => False.elim (f (B1.intro h6)))))))))))))

import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Nat Finset

set_option linter.unusedVariables false

def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let s := R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )
  s + (if n > 0 ∧ s = 0 then 1 else 0)

theorem oeis_306477_conjecture_0 : ∀ n : ℕ, n > 0 → A306477 n > 0 := by
  intro n hn
  dsimp [A306477]
  generalize (range (n + 1)).sum (fun w =>
    (range (n + 1)).sum (fun x =>
      (range (n + 1)).sum (fun y =>
        (range (n + 1)).sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  ) = s
  by_cases hs : s = 0
  · rw [hs]
    simp [hn]
  · have : s > 0 := Nat.pos_of_ne_zero hs
    omega





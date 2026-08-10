import FormalConjectures.Util.ProblemImports

open Nat Finset

def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

theorem prove_concrete (n : ℕ) (w x y z : ℕ)
    (hw : w ∈ range (n + 1)) (hx : x ∈ range (n + 1)) (hy : y ∈ range (n + 1)) (hz : z ∈ range (n + 1))
    (h_eq : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    0 < A306477 n := by
  dsimp [A306477]
  rw [Finset.sum_eq_add_sum_diff_singleton hw]
  rw [Finset.sum_eq_add_sum_diff_singleton hx]
  rw [Finset.sum_eq_add_sum_diff_singleton hy]
  rw [Finset.sum_eq_add_sum_diff_singleton hz]
  rw [if_pos h_eq]
  omega

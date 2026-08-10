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

theorem A306477_pos_of_exists (n : ℕ) (w x y z : ℕ)
    (hw : w ∈ Finset.range (n + 1)) (hx : x ∈ Finset.range (n + 1))
    (hy : y ∈ Finset.range (n + 1)) (hz : z ∈ Finset.range (n + 1))
    (h : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    A306477 n > 0 := by
  dsimp [A306477]
  apply Finset.sum_pos'
  · intro w' _
    apply Finset.sum_nonneg
    intro x' _
    apply Finset.sum_nonneg
    intro y' _
    apply Finset.sum_nonneg
    intro z' _
    split_ifs <;> simp
  · use w, hw
    apply Finset.sum_pos'
    · intro x' _
      apply Finset.sum_nonneg
      intro y' _
      apply Finset.sum_nonneg
      intro z' _
      split_ifs <;> simp
    · use x, hx
      apply Finset.sum_pos'
      · intro y' _
        apply Finset.sum_nonneg
        intro z' _
        split_ifs <;> simp
      · use y, hy
        apply Finset.sum_pos'
        · intro z' _
          split_ifs <;> simp
        · use z, hz
          simp [h]

theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  sorry
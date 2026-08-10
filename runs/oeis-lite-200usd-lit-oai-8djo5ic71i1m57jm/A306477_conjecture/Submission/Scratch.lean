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

lemma pos_of_rep {n w x y z : ℕ}
    (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (hrep : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    A306477 n > 0 := by
  classical
  simp [A306477]
  -- try finset positivity
  let f := fun w =>
    (Finset.range (n + 1)).sum (fun x =>
      (Finset.range (n + 1)).sum (fun y =>
        (Finset.range (n + 1)).sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)))
  have hwmem : w ∈ Finset.range (n+1) := by simpa using hw
  have hxmem : x ∈ Finset.range (n+1) := by simpa using hx
  have hymem : y ∈ Finset.range (n+1) := by simpa using hy
  have hzmem : z ∈ Finset.range (n+1) := by simpa using hz
  have hterm : (if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) = 1 := by simp [hrep]
  -- use single_le_sum
  have hzle : 1 ≤ (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) := by
    simpa [hterm] using Finset.single_le_sum (s := Finset.range (n+1)) (f := fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) (by intro z hz; split <;> omega) hzmem
  have hyle : 1 ≤ (Finset.range (n + 1)).sum (fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)) := by
    exact le_trans hzle (Finset.single_le_sum (s := Finset.range (n+1)) (f := fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)) (by intro y hy; exact Finset.sum_nonneg (by intro z hz; split <;> omega)) hymem)
  have hxle : 1 ≤ (Finset.range (n + 1)).sum (fun x => (Finset.range (n + 1)).sum (fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))) := by
    exact le_trans hyle (Finset.single_le_sum (s := Finset.range (n+1)) (f := fun x => (Finset.range (n + 1)).sum (fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0))) (by intro x hx; exact Finset.sum_nonneg (by intro y hy; exact Finset.sum_nonneg (by intro z hz; split <;> omega))) hxmem)
  have hwle : 1 ≤ (Finset.range (n + 1)).sum (fun w => (Finset.range (n + 1)).sum (fun x => (Finset.range (n + 1)).sum (fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)))) := by
    exact le_trans hxle (Finset.single_le_sum (s := Finset.range (n+1)) (f := fun w => (Finset.range (n + 1)).sum (fun x => (Finset.range (n + 1)).sum (fun y => (Finset.range (n + 1)).sum (fun z => if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0)))) (by intro w hw; exact Finset.sum_nonneg (by intro x hx; exact Finset.sum_nonneg (by intro y hy; exact Finset.sum_nonneg (by intro z hz; split <;> omega)))) hwmem)
  exact hwle

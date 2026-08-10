import FormalConjectures.Util.ProblemImports

open Nat Classical

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def B_200 : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 185, 186, 191, 193, 198, 199]

def is_bad_dt_all (x : ℕ) : Bool :=
  if x < 112 then true
  else decide (x ∈ B_200)

theorem is_bad_dt_all_crossing {y : ℕ} (h_gt : y > 200) (h_le : A006368_map y ≤ 200) (h_not_bad : y ∉ [201, 203, 209, 215, 217, 223, 225, 227, 233, 239, 247, 255, 257, 265]) : is_bad_dt_all (A006368_map y) = false := by
  have h_max : y ≤ 267 := by
    by_contra h_gt267
    push_neg at h_gt267
    unfold A006368_map at h_le
    split_ifs at h_le with h1 h2 <;> omega
  interval_cases y
  all_goals try (revert h_not_bad; decide)
  all_goals try (unfold is_bad_dt_all; decide)

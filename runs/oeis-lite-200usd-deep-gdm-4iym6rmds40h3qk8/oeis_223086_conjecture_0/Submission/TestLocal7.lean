import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

def my_map (B : ℕ) (k : ℕ) : ℕ :=
  if k ≤ B then
    A006368_map k
  else
    2 * B + k

theorem my_map_injective (B : ℕ) : ∀ x y, my_map B x = my_map B y → x = y := by
  intro x y h
  unfold my_map at h
  split_ifs at h
  · exact A006368_map_injective x y h
  · unfold A006368_map at h
    split_ifs at h <;> omega
  · unfold A006368_map at h
    split_ifs at h <;> omega
  · omega

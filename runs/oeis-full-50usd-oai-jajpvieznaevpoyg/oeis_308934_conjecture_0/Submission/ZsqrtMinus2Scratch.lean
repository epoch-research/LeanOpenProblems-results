import FormalConjectures.Util.ProblemImports

open Zsqrtd
local notation "ℤ√-2" => Zsqrtd (-2)

#check Zsqrtd.norm
#check Zsqrtd.norm_mul
#check Zsqrtd.norm_def
#check Zsqrtd.norm_nonneg
#check Zsqrtd.norm_eq_zero_iff

example (a b : ℤ) : Zsqrtd.norm (⟨a,b⟩ : ℤ√-2) = a*a + 2*b*b := by
  simp [Zsqrtd.norm, Zsqrtd.norm_def]
  ring

example (a b : ℤ) : (Zsqrtd.norm (⟨a,b⟩ : ℤ√-2)).natAbs = a.natAbs^2 + 2*b.natAbs^2 := by
  rw [show Zsqrtd.norm (⟨a,b⟩ : ℤ√-2) = a*a + 2*b*b by simp [Zsqrtd.norm]; ring]
  have hnon : 0 ≤ a*a + 2*b*b := by nlinarith [sq_nonneg a, sq_nonneg b]
  rw [Int.natAbs_of_nonneg hnon]
  norm_num [sq]
  -- maybe stuck at natAbs squares
  sorry

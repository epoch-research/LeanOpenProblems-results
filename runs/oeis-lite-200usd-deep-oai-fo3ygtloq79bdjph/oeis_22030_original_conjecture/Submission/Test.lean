import FormalConjectures.Util.ProblemImports
open Nat
open Rat

noncomputable def A022030_original (n : ℕ) : ℕ :=
  if h0 : n = 0 then 4
  else if h1 : n = 1 then 16
  else
    let b_n_1 := A022030_original (n - 1)
    let b_n_2 := A022030_original (n - 2)
    let num := b_n_1 ^ 2
    let den := b_n_2
    (num + den - 1) / den - 1
termination_by n

#print A022030_original.eq_def
#print Nat.div_eq_of_lt_le
#check Nat.div_eq_of_lt
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le
#check Nat.div_eq_iff_lt_le

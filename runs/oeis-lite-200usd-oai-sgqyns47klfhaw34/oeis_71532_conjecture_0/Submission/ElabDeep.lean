import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat
#check a
#print a
#check (sqrt (0:ℝ))
#check (floor ((3:ℝ)/2))
#check (Int.floor ((3:ℝ)/2))
#check (Real.sqrt (0:ℝ))
#check (fun n : ℕ => (a n : ℝ) > sqrt (n : ℝ))
#print Prefix Neg.neg
#reduce a 0
#eval a 0
#eval a 1
#eval a 2
#eval a 10
#eval ((a 10 : ℤ))

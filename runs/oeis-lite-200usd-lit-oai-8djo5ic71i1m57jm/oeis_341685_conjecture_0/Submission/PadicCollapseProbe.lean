import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.ext
#check Padic.ext_iff
#check Padic.eq_zero_iff
#check Padic.norm_eq_zero
#check Padic.norm_eq_zero_iff
#check norm_eq_zero
example : (0 : Padic 3) ≠ 1 := by norm_num
example : Nontrivial (Padic 3) := by infer_instance
example : ¬ Subsingleton (Padic 3) := by exact not_subsingleton (0 : Padic 3) 1 (by norm_num)

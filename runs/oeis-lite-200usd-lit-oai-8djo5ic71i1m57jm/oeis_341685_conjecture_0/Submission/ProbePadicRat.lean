import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.padicNormE.is_rat
#check Padic.rat_dense
#check Padic.rat_dense'
#check Padic.exi_rat_seq_conv
#check Padic.exi_rat_seq_conv_cauchy
#check Padic.ratNorm
#check PadicInt.exists_mem_range_of_norm_rat_le_one

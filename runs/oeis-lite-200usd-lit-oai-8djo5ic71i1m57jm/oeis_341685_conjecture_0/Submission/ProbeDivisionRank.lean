import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#check Module.Free.of_divisionRing
#check Module.finrank_self
#check Module.finrank_of_basis
#check Module.rank_self
#check Module.rank_subsingleton
#check Module.rank_eq_one_iff
#check Module.finrank_eq_one_iff
#check Module.finrank_of_divisionRing
#check Module.finrank_eq_card_basis
#check Module.rank_eq_card_basis
#check Module.Basis.mk
#check Module.Free.chooseBasis

import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 200000

example : False := by
  -- try contradictions from custom Set interval fintype instances
  first
  | exact false_of_nontrivial_of_subsingleton ℕ
  | exact not_finite ℕ inferInstance
  | exact Infinite.false ℕ
  | exact Set.infinite_univ.not_finite (Set.finite_univ_iff.mp inferInstance)
  | exact CharP.false_of_nontrivial_of_char_one ℕ
  | exact CategoryTheory.zero_not_simple
  | omega
  | norm_num
  | aesop

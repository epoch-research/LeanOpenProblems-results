import FormalConjectures.Util.ProblemImports
namespace TopoCycle
noncomputable instance badPre : PreirreducibleSpace Bool where
  isPreirreducible_univ := by
    exfalso
    exact @not_preirreducible_nontrivial_t2 Bool instTopologicalSpaceBool badPre Bool.instNontrivial inferInstance
#print axioms badPre
example : False := @not_preirreducible_nontrivial_t2 Bool instTopologicalSpaceBool badPre Bool.instNontrivial inferInstance
end TopoCycle

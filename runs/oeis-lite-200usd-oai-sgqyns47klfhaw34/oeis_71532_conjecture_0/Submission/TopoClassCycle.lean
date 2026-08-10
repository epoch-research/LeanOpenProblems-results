import FormalConjectures.Util.ProblemImports

namespace TopoCycle

-- Bool has discrete topology / T2 / Nontrivial from Mathlib presumably
#synth TopologicalSpace Bool
#synth T2Space Bool
#synth Nontrivial Bool

noncomputable instance badPre : PreirreducibleSpace Bool where
  isPreirreducible_univ := by
    -- goal IsPreirreducible univ; prove by contradiction using theorem requiring badPre
    exfalso
    exact  Bool inferInstance badPre inferInstance inferInstance

#print axioms badPre
example : False := not_preirreducible_nontrivial_t2 Bool
#print axioms _example

end TopoCycle

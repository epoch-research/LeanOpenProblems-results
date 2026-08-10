import FormalConjectures.Util.ProblemImports
-- Type-valued class may be partial-inhabitable if structure has data
partial def hzm (_ : Unit) : CategoryTheory.Limits.HasZeroMorphisms (Type) := hzm ()
#print axioms hzm
-- Prop-valued class likely not
partial def simpZero (_ : Unit) : @CategoryTheory.Simple (max 1 0) (max 1 0) Type inferInstance (hzm ()) (PUnit) := simpZero ()
#print axioms simpZero

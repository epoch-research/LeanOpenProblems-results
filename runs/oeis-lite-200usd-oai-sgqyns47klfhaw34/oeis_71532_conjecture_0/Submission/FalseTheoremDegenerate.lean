import FormalConjectures.Util.ProblemImports
#check PrincipalSeg.irrefl
#print PrincipalSeg
#print IsWellOrder

-- Try proving False from PrincipalSeg.irrefl on Empty/empty relation
example : False := by
  let r : Empty → Empty → Prop := fun _ _ => False
  haveI : IsWellOrder Empty r := by infer_instance
  let f : PrincipalSeg r r := ?_
  exact PrincipalSeg.irrefl f

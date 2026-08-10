import FormalConjectures.Util.ProblemImports
open CategoryTheory

abbrev C := Unit
instance : Category C := inferInstance
-- inspect PreGaloisCategory fields
#print CategoryTheory.PreGaloisCategory

def F : C ⥤ FintypeCat where
  obj _ := FintypeCat.of Empty
  map _ := PEmpty.elim -- wrong? hom is function Empty -> Empty
  map_id := by intro X; ext x; cases x
  map_comp := by intro X Y Z f g; ext x; cases x

-- try synth/construct
example : False := by
  letI : CategoryTheory.PreGaloisCategory C := by infer_instance
  letI : CategoryTheory.PreGaloisCategory.FiberFunctor F := by infer_instance
  letI : CategoryTheory.PreGaloisCategory.IsConnected (()) := by infer_instance
  have h : Nonempty (F.obj ()) := CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected F ()
  exact h.elim (by intro x; cases x)

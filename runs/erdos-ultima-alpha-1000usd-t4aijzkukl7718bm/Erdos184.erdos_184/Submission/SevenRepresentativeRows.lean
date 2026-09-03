import Submission.PureSevenFactor
import Submission.PureSixOrbitLookup0Base
namespace Erdos184Work.SevenRepresentativeRows
open PureSevenFactor
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

def representative : Fin 13 → Fin 381 := ![194,223,225,266,274,275,281,301,303,332,342,348,375]
lemma complete : ∀ r ∈ PureSixGoodLookup.representatives, ∃ t : Fin 13, representative t = r := by decide +kernel
lemma repRows_eq : ∀ t : Fin 13, repRows t =
    PureSixRowModel0.unkey (PureSixOrbitLookup0.representativeKey (representative t)) := by decide +kernel
#print axioms repRows_eq
#print axioms complete
end Erdos184Work.SevenRepresentativeRows

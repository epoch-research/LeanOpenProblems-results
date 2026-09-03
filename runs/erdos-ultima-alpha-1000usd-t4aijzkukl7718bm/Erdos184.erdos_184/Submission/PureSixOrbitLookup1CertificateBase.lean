import Submission.PureSixOrbitLookup1Base
import Submission.PureSixActionNumbers1
namespace Erdos184Work.PureSixOrbitLookup1
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option Elab.async false
def Certificate (j c : ℕ) : Prop :=
  PureSixActions1.actionKey (groupOfCode c) j = representativeKey (representativeOfCode c)
instance (j c : ℕ) : Decidable (Certificate j c) := inferInstanceAs (Decidable (_ = _))
end Erdos184Work.PureSixOrbitLookup1

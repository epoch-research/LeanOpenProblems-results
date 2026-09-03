import Submission.PureSixOrbitLookup0Base
import Submission.PureSixActionNumbers0
import Submission.PureSixGoodLookup
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option Elab.async false
def Certificate (j c : ℕ) : Prop :=
  PureSixActions0.actionKey (groupOfCode c) j = representativeKey (representativeOfCode c)
instance (j c : ℕ) : Decidable (Certificate j c) := inferInstanceAs (Decidable (_ = _))
def GoodCertificate (j c : ℕ) : Prop :=
  representativeOfCode c ∈ PureSixGoodLookup.representatives → PureSixGoodLookup.Good j
instance (j c : ℕ) : Decidable (GoodCertificate j c) := by
  unfold GoodCertificate
  infer_instance
end Erdos184Work.PureSixOrbitLookup0

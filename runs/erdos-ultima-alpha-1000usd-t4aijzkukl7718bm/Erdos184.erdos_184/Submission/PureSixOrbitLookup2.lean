import Submission.PureSixOrbitLookup2Check0000
import Submission.PureSixOrbitLookup2Check0001

namespace Erdos184Work.PureSixOrbitLookup2
open FiniteCaseLookup
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_table : Table.Every Certificate table :=
  ⟨certificate_block0,certificate_block1⟩
lemma lookup_certificate {j c : ℕ} (h : table.lookup j = some c) : Certificate j c :=
  Table.lookup_every Certificate table certificate_table j h
#print axioms lookup_certificate
end Erdos184Work.PureSixOrbitLookup2

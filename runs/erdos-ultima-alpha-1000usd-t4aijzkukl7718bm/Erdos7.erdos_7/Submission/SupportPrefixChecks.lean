import Submission.SupportPrefixCheck0
import Submission.SupportPrefixCheck1
import Submission.SupportPrefixCheck2
import Submission.SupportPrefixCheck3
import Submission.SupportPrefixCheck4
import Submission.SupportPrefixCheck5
import Submission.SupportPrefixCheck6
import Submission.SupportPrefixCheck7
import Submission.SupportPrefixCheck8
import Submission.SupportPrefixCheck9
import Submission.SupportPrefixCheck10
import Submission.SupportPrefixCheck11
import Submission.SupportPrefixCheck12
import Submission.SupportPrefixCheck13
import Submission.SupportPrefixCheck14
import Submission.SupportPrefixCheck15
import Submission.SupportPrefixCheck16
import Submission.SupportPrefixCheck17
import Submission.SupportPrefixCheck18
import Submission.SupportPrefixCheck19
import Submission.SupportPrefixCheck20
import Submission.SupportPrefixCheck21
import Submission.SupportPrefixCheck22
import Submission.SupportPrefixCheck23
import Submission.SupportPrefixCheck24
import Submission.SupportPrefixCheck25
import Submission.SupportPrefixCheck26
import Submission.SupportPrefixCheck27
import Submission.SupportPrefixCheck28
import Submission.SupportPrefixCheck29
import Submission.SupportPrefixCheck30
import Submission.SupportPrefixCheck31
import Submission.SupportPrefixCheck32
import Submission.SupportPrefixCheck33
import Submission.SupportPrefixCheck34
import Submission.SupportPrefixCheck35
import Submission.SupportPrefixCheck36
import Submission.SupportPrefixCheck37
import Submission.SupportPrefixCheck38
import Submission.SupportPrefixCheck39
import Submission.SupportPrefixCheck40
import Submission.SupportPrefixCheck41

/-! Assembly of the checked integer rows. This does not by itself prove the
law interpretation or the unrestricted covering conjecture. -/
namespace Erdos7SupportPrefixChecks
open Erdos7SupportPrefixData
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem all_lower_rows : ∀ i : Fin 167, ∀ j : Fin 180, lowerRow i j := by
  intro i j
  fin_cases i
  · exact lower_block0 ⟨0,by decide⟩ j
  · exact lower_block0 ⟨1,by decide⟩ j
  · exact lower_block0 ⟨2,by decide⟩ j
  · exact lower_block0 ⟨3,by decide⟩ j
  · exact lower_block1 ⟨0,by decide⟩ j
  · exact lower_block1 ⟨1,by decide⟩ j
  · exact lower_block1 ⟨2,by decide⟩ j
  · exact lower_block1 ⟨3,by decide⟩ j
  · exact lower_block2 ⟨0,by decide⟩ j
  · exact lower_block2 ⟨1,by decide⟩ j
  · exact lower_block2 ⟨2,by decide⟩ j
  · exact lower_block2 ⟨3,by decide⟩ j
  · exact lower_block3 ⟨0,by decide⟩ j
  · exact lower_block3 ⟨1,by decide⟩ j
  · exact lower_block3 ⟨2,by decide⟩ j
  · exact lower_block3 ⟨3,by decide⟩ j
  · exact lower_block4 ⟨0,by decide⟩ j
  · exact lower_block4 ⟨1,by decide⟩ j
  · exact lower_block4 ⟨2,by decide⟩ j
  · exact lower_block4 ⟨3,by decide⟩ j
  · exact lower_block5 ⟨0,by decide⟩ j
  · exact lower_block5 ⟨1,by decide⟩ j
  · exact lower_block5 ⟨2,by decide⟩ j
  · exact lower_block5 ⟨3,by decide⟩ j
  · exact lower_block6 ⟨0,by decide⟩ j
  · exact lower_block6 ⟨1,by decide⟩ j
  · exact lower_block6 ⟨2,by decide⟩ j
  · exact lower_block6 ⟨3,by decide⟩ j
  · exact lower_block7 ⟨0,by decide⟩ j
  · exact lower_block7 ⟨1,by decide⟩ j
  · exact lower_block7 ⟨2,by decide⟩ j
  · exact lower_block7 ⟨3,by decide⟩ j
  · exact lower_block8 ⟨0,by decide⟩ j
  · exact lower_block8 ⟨1,by decide⟩ j
  · exact lower_block8 ⟨2,by decide⟩ j
  · exact lower_block8 ⟨3,by decide⟩ j
  · exact lower_block9 ⟨0,by decide⟩ j
  · exact lower_block9 ⟨1,by decide⟩ j
  · exact lower_block9 ⟨2,by decide⟩ j
  · exact lower_block9 ⟨3,by decide⟩ j
  · exact lower_block10 ⟨0,by decide⟩ j
  · exact lower_block10 ⟨1,by decide⟩ j
  · exact lower_block10 ⟨2,by decide⟩ j
  · exact lower_block10 ⟨3,by decide⟩ j
  · exact lower_block11 ⟨0,by decide⟩ j
  · exact lower_block11 ⟨1,by decide⟩ j
  · exact lower_block11 ⟨2,by decide⟩ j
  · exact lower_block11 ⟨3,by decide⟩ j
  · exact lower_block12 ⟨0,by decide⟩ j
  · exact lower_block12 ⟨1,by decide⟩ j
  · exact lower_block12 ⟨2,by decide⟩ j
  · exact lower_block12 ⟨3,by decide⟩ j
  · exact lower_block13 ⟨0,by decide⟩ j
  · exact lower_block13 ⟨1,by decide⟩ j
  · exact lower_block13 ⟨2,by decide⟩ j
  · exact lower_block13 ⟨3,by decide⟩ j
  · exact lower_block14 ⟨0,by decide⟩ j
  · exact lower_block14 ⟨1,by decide⟩ j
  · exact lower_block14 ⟨2,by decide⟩ j
  · exact lower_block14 ⟨3,by decide⟩ j
  · exact lower_block15 ⟨0,by decide⟩ j
  · exact lower_block15 ⟨1,by decide⟩ j
  · exact lower_block15 ⟨2,by decide⟩ j
  · exact lower_block15 ⟨3,by decide⟩ j
  · exact lower_block16 ⟨0,by decide⟩ j
  · exact lower_block16 ⟨1,by decide⟩ j
  · exact lower_block16 ⟨2,by decide⟩ j
  · exact lower_block16 ⟨3,by decide⟩ j
  · exact lower_block17 ⟨0,by decide⟩ j
  · exact lower_block17 ⟨1,by decide⟩ j
  · exact lower_block17 ⟨2,by decide⟩ j
  · exact lower_block17 ⟨3,by decide⟩ j
  · exact lower_block18 ⟨0,by decide⟩ j
  · exact lower_block18 ⟨1,by decide⟩ j
  · exact lower_block18 ⟨2,by decide⟩ j
  · exact lower_block18 ⟨3,by decide⟩ j
  · exact lower_block19 ⟨0,by decide⟩ j
  · exact lower_block19 ⟨1,by decide⟩ j
  · exact lower_block19 ⟨2,by decide⟩ j
  · exact lower_block19 ⟨3,by decide⟩ j
  · exact lower_block20 ⟨0,by decide⟩ j
  · exact lower_block20 ⟨1,by decide⟩ j
  · exact lower_block20 ⟨2,by decide⟩ j
  · exact lower_block20 ⟨3,by decide⟩ j
  · exact lower_block21 ⟨0,by decide⟩ j
  · exact lower_block21 ⟨1,by decide⟩ j
  · exact lower_block21 ⟨2,by decide⟩ j
  · exact lower_block21 ⟨3,by decide⟩ j
  · exact lower_block22 ⟨0,by decide⟩ j
  · exact lower_block22 ⟨1,by decide⟩ j
  · exact lower_block22 ⟨2,by decide⟩ j
  · exact lower_block22 ⟨3,by decide⟩ j
  · exact lower_block23 ⟨0,by decide⟩ j
  · exact lower_block23 ⟨1,by decide⟩ j
  · exact lower_block23 ⟨2,by decide⟩ j
  · exact lower_block23 ⟨3,by decide⟩ j
  · exact lower_block24 ⟨0,by decide⟩ j
  · exact lower_block24 ⟨1,by decide⟩ j
  · exact lower_block24 ⟨2,by decide⟩ j
  · exact lower_block24 ⟨3,by decide⟩ j
  · exact lower_block25 ⟨0,by decide⟩ j
  · exact lower_block25 ⟨1,by decide⟩ j
  · exact lower_block25 ⟨2,by decide⟩ j
  · exact lower_block25 ⟨3,by decide⟩ j
  · exact lower_block26 ⟨0,by decide⟩ j
  · exact lower_block26 ⟨1,by decide⟩ j
  · exact lower_block26 ⟨2,by decide⟩ j
  · exact lower_block26 ⟨3,by decide⟩ j
  · exact lower_block27 ⟨0,by decide⟩ j
  · exact lower_block27 ⟨1,by decide⟩ j
  · exact lower_block27 ⟨2,by decide⟩ j
  · exact lower_block27 ⟨3,by decide⟩ j
  · exact lower_block28 ⟨0,by decide⟩ j
  · exact lower_block28 ⟨1,by decide⟩ j
  · exact lower_block28 ⟨2,by decide⟩ j
  · exact lower_block28 ⟨3,by decide⟩ j
  · exact lower_block29 ⟨0,by decide⟩ j
  · exact lower_block29 ⟨1,by decide⟩ j
  · exact lower_block29 ⟨2,by decide⟩ j
  · exact lower_block29 ⟨3,by decide⟩ j
  · exact lower_block30 ⟨0,by decide⟩ j
  · exact lower_block30 ⟨1,by decide⟩ j
  · exact lower_block30 ⟨2,by decide⟩ j
  · exact lower_block30 ⟨3,by decide⟩ j
  · exact lower_block31 ⟨0,by decide⟩ j
  · exact lower_block31 ⟨1,by decide⟩ j
  · exact lower_block31 ⟨2,by decide⟩ j
  · exact lower_block31 ⟨3,by decide⟩ j
  · exact lower_block32 ⟨0,by decide⟩ j
  · exact lower_block32 ⟨1,by decide⟩ j
  · exact lower_block32 ⟨2,by decide⟩ j
  · exact lower_block32 ⟨3,by decide⟩ j
  · exact lower_block33 ⟨0,by decide⟩ j
  · exact lower_block33 ⟨1,by decide⟩ j
  · exact lower_block33 ⟨2,by decide⟩ j
  · exact lower_block33 ⟨3,by decide⟩ j
  · exact lower_block34 ⟨0,by decide⟩ j
  · exact lower_block34 ⟨1,by decide⟩ j
  · exact lower_block34 ⟨2,by decide⟩ j
  · exact lower_block34 ⟨3,by decide⟩ j
  · exact lower_block35 ⟨0,by decide⟩ j
  · exact lower_block35 ⟨1,by decide⟩ j
  · exact lower_block35 ⟨2,by decide⟩ j
  · exact lower_block35 ⟨3,by decide⟩ j
  · exact lower_block36 ⟨0,by decide⟩ j
  · exact lower_block36 ⟨1,by decide⟩ j
  · exact lower_block36 ⟨2,by decide⟩ j
  · exact lower_block36 ⟨3,by decide⟩ j
  · exact lower_block37 ⟨0,by decide⟩ j
  · exact lower_block37 ⟨1,by decide⟩ j
  · exact lower_block37 ⟨2,by decide⟩ j
  · exact lower_block37 ⟨3,by decide⟩ j
  · exact lower_block38 ⟨0,by decide⟩ j
  · exact lower_block38 ⟨1,by decide⟩ j
  · exact lower_block38 ⟨2,by decide⟩ j
  · exact lower_block38 ⟨3,by decide⟩ j
  · exact lower_block39 ⟨0,by decide⟩ j
  · exact lower_block39 ⟨1,by decide⟩ j
  · exact lower_block39 ⟨2,by decide⟩ j
  · exact lower_block39 ⟨3,by decide⟩ j
  · exact lower_block40 ⟨0,by decide⟩ j
  · exact lower_block40 ⟨1,by decide⟩ j
  · exact lower_block40 ⟨2,by decide⟩ j
  · exact lower_block40 ⟨3,by decide⟩ j
  · exact lower_block41 ⟨0,by decide⟩ j
  · exact lower_block41 ⟨1,by decide⟩ j
  · exact lower_block41 ⟨2,by decide⟩ j
theorem all_moment_rows : ∀ i : Fin 167, ∀ j : Fin 10, momentRow i j := by
  intro i j
  fin_cases i
  · exact moment_block0 ⟨0,by decide⟩ j
  · exact moment_block0 ⟨1,by decide⟩ j
  · exact moment_block0 ⟨2,by decide⟩ j
  · exact moment_block0 ⟨3,by decide⟩ j
  · exact moment_block1 ⟨0,by decide⟩ j
  · exact moment_block1 ⟨1,by decide⟩ j
  · exact moment_block1 ⟨2,by decide⟩ j
  · exact moment_block1 ⟨3,by decide⟩ j
  · exact moment_block2 ⟨0,by decide⟩ j
  · exact moment_block2 ⟨1,by decide⟩ j
  · exact moment_block2 ⟨2,by decide⟩ j
  · exact moment_block2 ⟨3,by decide⟩ j
  · exact moment_block3 ⟨0,by decide⟩ j
  · exact moment_block3 ⟨1,by decide⟩ j
  · exact moment_block3 ⟨2,by decide⟩ j
  · exact moment_block3 ⟨3,by decide⟩ j
  · exact moment_block4 ⟨0,by decide⟩ j
  · exact moment_block4 ⟨1,by decide⟩ j
  · exact moment_block4 ⟨2,by decide⟩ j
  · exact moment_block4 ⟨3,by decide⟩ j
  · exact moment_block5 ⟨0,by decide⟩ j
  · exact moment_block5 ⟨1,by decide⟩ j
  · exact moment_block5 ⟨2,by decide⟩ j
  · exact moment_block5 ⟨3,by decide⟩ j
  · exact moment_block6 ⟨0,by decide⟩ j
  · exact moment_block6 ⟨1,by decide⟩ j
  · exact moment_block6 ⟨2,by decide⟩ j
  · exact moment_block6 ⟨3,by decide⟩ j
  · exact moment_block7 ⟨0,by decide⟩ j
  · exact moment_block7 ⟨1,by decide⟩ j
  · exact moment_block7 ⟨2,by decide⟩ j
  · exact moment_block7 ⟨3,by decide⟩ j
  · exact moment_block8 ⟨0,by decide⟩ j
  · exact moment_block8 ⟨1,by decide⟩ j
  · exact moment_block8 ⟨2,by decide⟩ j
  · exact moment_block8 ⟨3,by decide⟩ j
  · exact moment_block9 ⟨0,by decide⟩ j
  · exact moment_block9 ⟨1,by decide⟩ j
  · exact moment_block9 ⟨2,by decide⟩ j
  · exact moment_block9 ⟨3,by decide⟩ j
  · exact moment_block10 ⟨0,by decide⟩ j
  · exact moment_block10 ⟨1,by decide⟩ j
  · exact moment_block10 ⟨2,by decide⟩ j
  · exact moment_block10 ⟨3,by decide⟩ j
  · exact moment_block11 ⟨0,by decide⟩ j
  · exact moment_block11 ⟨1,by decide⟩ j
  · exact moment_block11 ⟨2,by decide⟩ j
  · exact moment_block11 ⟨3,by decide⟩ j
  · exact moment_block12 ⟨0,by decide⟩ j
  · exact moment_block12 ⟨1,by decide⟩ j
  · exact moment_block12 ⟨2,by decide⟩ j
  · exact moment_block12 ⟨3,by decide⟩ j
  · exact moment_block13 ⟨0,by decide⟩ j
  · exact moment_block13 ⟨1,by decide⟩ j
  · exact moment_block13 ⟨2,by decide⟩ j
  · exact moment_block13 ⟨3,by decide⟩ j
  · exact moment_block14 ⟨0,by decide⟩ j
  · exact moment_block14 ⟨1,by decide⟩ j
  · exact moment_block14 ⟨2,by decide⟩ j
  · exact moment_block14 ⟨3,by decide⟩ j
  · exact moment_block15 ⟨0,by decide⟩ j
  · exact moment_block15 ⟨1,by decide⟩ j
  · exact moment_block15 ⟨2,by decide⟩ j
  · exact moment_block15 ⟨3,by decide⟩ j
  · exact moment_block16 ⟨0,by decide⟩ j
  · exact moment_block16 ⟨1,by decide⟩ j
  · exact moment_block16 ⟨2,by decide⟩ j
  · exact moment_block16 ⟨3,by decide⟩ j
  · exact moment_block17 ⟨0,by decide⟩ j
  · exact moment_block17 ⟨1,by decide⟩ j
  · exact moment_block17 ⟨2,by decide⟩ j
  · exact moment_block17 ⟨3,by decide⟩ j
  · exact moment_block18 ⟨0,by decide⟩ j
  · exact moment_block18 ⟨1,by decide⟩ j
  · exact moment_block18 ⟨2,by decide⟩ j
  · exact moment_block18 ⟨3,by decide⟩ j
  · exact moment_block19 ⟨0,by decide⟩ j
  · exact moment_block19 ⟨1,by decide⟩ j
  · exact moment_block19 ⟨2,by decide⟩ j
  · exact moment_block19 ⟨3,by decide⟩ j
  · exact moment_block20 ⟨0,by decide⟩ j
  · exact moment_block20 ⟨1,by decide⟩ j
  · exact moment_block20 ⟨2,by decide⟩ j
  · exact moment_block20 ⟨3,by decide⟩ j
  · exact moment_block21 ⟨0,by decide⟩ j
  · exact moment_block21 ⟨1,by decide⟩ j
  · exact moment_block21 ⟨2,by decide⟩ j
  · exact moment_block21 ⟨3,by decide⟩ j
  · exact moment_block22 ⟨0,by decide⟩ j
  · exact moment_block22 ⟨1,by decide⟩ j
  · exact moment_block22 ⟨2,by decide⟩ j
  · exact moment_block22 ⟨3,by decide⟩ j
  · exact moment_block23 ⟨0,by decide⟩ j
  · exact moment_block23 ⟨1,by decide⟩ j
  · exact moment_block23 ⟨2,by decide⟩ j
  · exact moment_block23 ⟨3,by decide⟩ j
  · exact moment_block24 ⟨0,by decide⟩ j
  · exact moment_block24 ⟨1,by decide⟩ j
  · exact moment_block24 ⟨2,by decide⟩ j
  · exact moment_block24 ⟨3,by decide⟩ j
  · exact moment_block25 ⟨0,by decide⟩ j
  · exact moment_block25 ⟨1,by decide⟩ j
  · exact moment_block25 ⟨2,by decide⟩ j
  · exact moment_block25 ⟨3,by decide⟩ j
  · exact moment_block26 ⟨0,by decide⟩ j
  · exact moment_block26 ⟨1,by decide⟩ j
  · exact moment_block26 ⟨2,by decide⟩ j
  · exact moment_block26 ⟨3,by decide⟩ j
  · exact moment_block27 ⟨0,by decide⟩ j
  · exact moment_block27 ⟨1,by decide⟩ j
  · exact moment_block27 ⟨2,by decide⟩ j
  · exact moment_block27 ⟨3,by decide⟩ j
  · exact moment_block28 ⟨0,by decide⟩ j
  · exact moment_block28 ⟨1,by decide⟩ j
  · exact moment_block28 ⟨2,by decide⟩ j
  · exact moment_block28 ⟨3,by decide⟩ j
  · exact moment_block29 ⟨0,by decide⟩ j
  · exact moment_block29 ⟨1,by decide⟩ j
  · exact moment_block29 ⟨2,by decide⟩ j
  · exact moment_block29 ⟨3,by decide⟩ j
  · exact moment_block30 ⟨0,by decide⟩ j
  · exact moment_block30 ⟨1,by decide⟩ j
  · exact moment_block30 ⟨2,by decide⟩ j
  · exact moment_block30 ⟨3,by decide⟩ j
  · exact moment_block31 ⟨0,by decide⟩ j
  · exact moment_block31 ⟨1,by decide⟩ j
  · exact moment_block31 ⟨2,by decide⟩ j
  · exact moment_block31 ⟨3,by decide⟩ j
  · exact moment_block32 ⟨0,by decide⟩ j
  · exact moment_block32 ⟨1,by decide⟩ j
  · exact moment_block32 ⟨2,by decide⟩ j
  · exact moment_block32 ⟨3,by decide⟩ j
  · exact moment_block33 ⟨0,by decide⟩ j
  · exact moment_block33 ⟨1,by decide⟩ j
  · exact moment_block33 ⟨2,by decide⟩ j
  · exact moment_block33 ⟨3,by decide⟩ j
  · exact moment_block34 ⟨0,by decide⟩ j
  · exact moment_block34 ⟨1,by decide⟩ j
  · exact moment_block34 ⟨2,by decide⟩ j
  · exact moment_block34 ⟨3,by decide⟩ j
  · exact moment_block35 ⟨0,by decide⟩ j
  · exact moment_block35 ⟨1,by decide⟩ j
  · exact moment_block35 ⟨2,by decide⟩ j
  · exact moment_block35 ⟨3,by decide⟩ j
  · exact moment_block36 ⟨0,by decide⟩ j
  · exact moment_block36 ⟨1,by decide⟩ j
  · exact moment_block36 ⟨2,by decide⟩ j
  · exact moment_block36 ⟨3,by decide⟩ j
  · exact moment_block37 ⟨0,by decide⟩ j
  · exact moment_block37 ⟨1,by decide⟩ j
  · exact moment_block37 ⟨2,by decide⟩ j
  · exact moment_block37 ⟨3,by decide⟩ j
  · exact moment_block38 ⟨0,by decide⟩ j
  · exact moment_block38 ⟨1,by decide⟩ j
  · exact moment_block38 ⟨2,by decide⟩ j
  · exact moment_block38 ⟨3,by decide⟩ j
  · exact moment_block39 ⟨0,by decide⟩ j
  · exact moment_block39 ⟨1,by decide⟩ j
  · exact moment_block39 ⟨2,by decide⟩ j
  · exact moment_block39 ⟨3,by decide⟩ j
  · exact moment_block40 ⟨0,by decide⟩ j
  · exact moment_block40 ⟨1,by decide⟩ j
  · exact moment_block40 ⟨2,by decide⟩ j
  · exact moment_block40 ⟨3,by decide⟩ j
  · exact moment_block41 ⟨0,by decide⟩ j
  · exact moment_block41 ⟨1,by decide⟩ j
  · exact moment_block41 ⟨2,by decide⟩ j
theorem all_loss_rows : ∀ i : Fin 167, lossRow i := by
  intro i
  fin_cases i
  · exact loss_block0 ⟨0,by decide⟩
  · exact loss_block0 ⟨1,by decide⟩
  · exact loss_block0 ⟨2,by decide⟩
  · exact loss_block0 ⟨3,by decide⟩
  · exact loss_block1 ⟨0,by decide⟩
  · exact loss_block1 ⟨1,by decide⟩
  · exact loss_block1 ⟨2,by decide⟩
  · exact loss_block1 ⟨3,by decide⟩
  · exact loss_block2 ⟨0,by decide⟩
  · exact loss_block2 ⟨1,by decide⟩
  · exact loss_block2 ⟨2,by decide⟩
  · exact loss_block2 ⟨3,by decide⟩
  · exact loss_block3 ⟨0,by decide⟩
  · exact loss_block3 ⟨1,by decide⟩
  · exact loss_block3 ⟨2,by decide⟩
  · exact loss_block3 ⟨3,by decide⟩
  · exact loss_block4 ⟨0,by decide⟩
  · exact loss_block4 ⟨1,by decide⟩
  · exact loss_block4 ⟨2,by decide⟩
  · exact loss_block4 ⟨3,by decide⟩
  · exact loss_block5 ⟨0,by decide⟩
  · exact loss_block5 ⟨1,by decide⟩
  · exact loss_block5 ⟨2,by decide⟩
  · exact loss_block5 ⟨3,by decide⟩
  · exact loss_block6 ⟨0,by decide⟩
  · exact loss_block6 ⟨1,by decide⟩
  · exact loss_block6 ⟨2,by decide⟩
  · exact loss_block6 ⟨3,by decide⟩
  · exact loss_block7 ⟨0,by decide⟩
  · exact loss_block7 ⟨1,by decide⟩
  · exact loss_block7 ⟨2,by decide⟩
  · exact loss_block7 ⟨3,by decide⟩
  · exact loss_block8 ⟨0,by decide⟩
  · exact loss_block8 ⟨1,by decide⟩
  · exact loss_block8 ⟨2,by decide⟩
  · exact loss_block8 ⟨3,by decide⟩
  · exact loss_block9 ⟨0,by decide⟩
  · exact loss_block9 ⟨1,by decide⟩
  · exact loss_block9 ⟨2,by decide⟩
  · exact loss_block9 ⟨3,by decide⟩
  · exact loss_block10 ⟨0,by decide⟩
  · exact loss_block10 ⟨1,by decide⟩
  · exact loss_block10 ⟨2,by decide⟩
  · exact loss_block10 ⟨3,by decide⟩
  · exact loss_block11 ⟨0,by decide⟩
  · exact loss_block11 ⟨1,by decide⟩
  · exact loss_block11 ⟨2,by decide⟩
  · exact loss_block11 ⟨3,by decide⟩
  · exact loss_block12 ⟨0,by decide⟩
  · exact loss_block12 ⟨1,by decide⟩
  · exact loss_block12 ⟨2,by decide⟩
  · exact loss_block12 ⟨3,by decide⟩
  · exact loss_block13 ⟨0,by decide⟩
  · exact loss_block13 ⟨1,by decide⟩
  · exact loss_block13 ⟨2,by decide⟩
  · exact loss_block13 ⟨3,by decide⟩
  · exact loss_block14 ⟨0,by decide⟩
  · exact loss_block14 ⟨1,by decide⟩
  · exact loss_block14 ⟨2,by decide⟩
  · exact loss_block14 ⟨3,by decide⟩
  · exact loss_block15 ⟨0,by decide⟩
  · exact loss_block15 ⟨1,by decide⟩
  · exact loss_block15 ⟨2,by decide⟩
  · exact loss_block15 ⟨3,by decide⟩
  · exact loss_block16 ⟨0,by decide⟩
  · exact loss_block16 ⟨1,by decide⟩
  · exact loss_block16 ⟨2,by decide⟩
  · exact loss_block16 ⟨3,by decide⟩
  · exact loss_block17 ⟨0,by decide⟩
  · exact loss_block17 ⟨1,by decide⟩
  · exact loss_block17 ⟨2,by decide⟩
  · exact loss_block17 ⟨3,by decide⟩
  · exact loss_block18 ⟨0,by decide⟩
  · exact loss_block18 ⟨1,by decide⟩
  · exact loss_block18 ⟨2,by decide⟩
  · exact loss_block18 ⟨3,by decide⟩
  · exact loss_block19 ⟨0,by decide⟩
  · exact loss_block19 ⟨1,by decide⟩
  · exact loss_block19 ⟨2,by decide⟩
  · exact loss_block19 ⟨3,by decide⟩
  · exact loss_block20 ⟨0,by decide⟩
  · exact loss_block20 ⟨1,by decide⟩
  · exact loss_block20 ⟨2,by decide⟩
  · exact loss_block20 ⟨3,by decide⟩
  · exact loss_block21 ⟨0,by decide⟩
  · exact loss_block21 ⟨1,by decide⟩
  · exact loss_block21 ⟨2,by decide⟩
  · exact loss_block21 ⟨3,by decide⟩
  · exact loss_block22 ⟨0,by decide⟩
  · exact loss_block22 ⟨1,by decide⟩
  · exact loss_block22 ⟨2,by decide⟩
  · exact loss_block22 ⟨3,by decide⟩
  · exact loss_block23 ⟨0,by decide⟩
  · exact loss_block23 ⟨1,by decide⟩
  · exact loss_block23 ⟨2,by decide⟩
  · exact loss_block23 ⟨3,by decide⟩
  · exact loss_block24 ⟨0,by decide⟩
  · exact loss_block24 ⟨1,by decide⟩
  · exact loss_block24 ⟨2,by decide⟩
  · exact loss_block24 ⟨3,by decide⟩
  · exact loss_block25 ⟨0,by decide⟩
  · exact loss_block25 ⟨1,by decide⟩
  · exact loss_block25 ⟨2,by decide⟩
  · exact loss_block25 ⟨3,by decide⟩
  · exact loss_block26 ⟨0,by decide⟩
  · exact loss_block26 ⟨1,by decide⟩
  · exact loss_block26 ⟨2,by decide⟩
  · exact loss_block26 ⟨3,by decide⟩
  · exact loss_block27 ⟨0,by decide⟩
  · exact loss_block27 ⟨1,by decide⟩
  · exact loss_block27 ⟨2,by decide⟩
  · exact loss_block27 ⟨3,by decide⟩
  · exact loss_block28 ⟨0,by decide⟩
  · exact loss_block28 ⟨1,by decide⟩
  · exact loss_block28 ⟨2,by decide⟩
  · exact loss_block28 ⟨3,by decide⟩
  · exact loss_block29 ⟨0,by decide⟩
  · exact loss_block29 ⟨1,by decide⟩
  · exact loss_block29 ⟨2,by decide⟩
  · exact loss_block29 ⟨3,by decide⟩
  · exact loss_block30 ⟨0,by decide⟩
  · exact loss_block30 ⟨1,by decide⟩
  · exact loss_block30 ⟨2,by decide⟩
  · exact loss_block30 ⟨3,by decide⟩
  · exact loss_block31 ⟨0,by decide⟩
  · exact loss_block31 ⟨1,by decide⟩
  · exact loss_block31 ⟨2,by decide⟩
  · exact loss_block31 ⟨3,by decide⟩
  · exact loss_block32 ⟨0,by decide⟩
  · exact loss_block32 ⟨1,by decide⟩
  · exact loss_block32 ⟨2,by decide⟩
  · exact loss_block32 ⟨3,by decide⟩
  · exact loss_block33 ⟨0,by decide⟩
  · exact loss_block33 ⟨1,by decide⟩
  · exact loss_block33 ⟨2,by decide⟩
  · exact loss_block33 ⟨3,by decide⟩
  · exact loss_block34 ⟨0,by decide⟩
  · exact loss_block34 ⟨1,by decide⟩
  · exact loss_block34 ⟨2,by decide⟩
  · exact loss_block34 ⟨3,by decide⟩
  · exact loss_block35 ⟨0,by decide⟩
  · exact loss_block35 ⟨1,by decide⟩
  · exact loss_block35 ⟨2,by decide⟩
  · exact loss_block35 ⟨3,by decide⟩
  · exact loss_block36 ⟨0,by decide⟩
  · exact loss_block36 ⟨1,by decide⟩
  · exact loss_block36 ⟨2,by decide⟩
  · exact loss_block36 ⟨3,by decide⟩
  · exact loss_block37 ⟨0,by decide⟩
  · exact loss_block37 ⟨1,by decide⟩
  · exact loss_block37 ⟨2,by decide⟩
  · exact loss_block37 ⟨3,by decide⟩
  · exact loss_block38 ⟨0,by decide⟩
  · exact loss_block38 ⟨1,by decide⟩
  · exact loss_block38 ⟨2,by decide⟩
  · exact loss_block38 ⟨3,by decide⟩
  · exact loss_block39 ⟨0,by decide⟩
  · exact loss_block39 ⟨1,by decide⟩
  · exact loss_block39 ⟨2,by decide⟩
  · exact loss_block39 ⟨3,by decide⟩
  · exact loss_block40 ⟨0,by decide⟩
  · exact loss_block40 ⟨1,by decide⟩
  · exact loss_block40 ⟨2,by decide⟩
  · exact loss_block40 ⟨3,by decide⟩
  · exact loss_block41 ⟨0,by decide⟩
  · exact loss_block41 ⟨1,by decide⟩
  · exact loss_block41 ⟨2,by decide⟩

theorem final_margin :
    (∑ i ∈ Finset.range stageCount,getNat costs i)*25*243*momentScale*cutoff^2+
      (∑ j ∈ Finset.range 10,getNat potentialCoeffs j*getNat (moments[stageCount]?.getD #[]) j)*25*costScale <
        24*costScale*243*momentScale*cutoff^2 := by decide +kernel
#print axioms all_lower_rows
#print axioms all_moment_rows
#print axioms all_loss_rows
#print axioms final_margin
end Erdos7SupportPrefixChecks

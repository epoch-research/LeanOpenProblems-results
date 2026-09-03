import Submission.QuadrilateralSevenCheck0
import Submission.QuadrilateralSevenCheck1
import Submission.QuadrilateralSevenCheck2
import Submission.QuadrilateralSevenCheck3
import Submission.QuadrilateralSevenCheck4
import Submission.QuadrilateralSevenCheck5
import Submission.QuadrilateralSevenCheck6
import Submission.QuadrilateralSevenCheck7
import Submission.QuadrilateralSevenCheck8
import Submission.QuadrilateralSevenCheck9
import Submission.QuadrilateralSevenCheck10
import Submission.QuadrilateralSevenCheck11
import Submission.QuadrilateralSevenCheck12
import Submission.QuadrilateralSevenCheck13
import Submission.QuadrilateralSevenCheck14
import Submission.QuadrilateralSevenCheck15
import Submission.QuadrilateralSevenCheck16
import Submission.QuadrilateralSevenCheck17
import Submission.QuadrilateralSevenCheck18
import Submission.QuadrilateralSevenCheck19
import Submission.QuadrilateralSevenCheck20
import Submission.QuadrilateralSevenCheck21
import Submission.QuadrilateralSevenCheck22
import Submission.QuadrilateralSevenCheck23
import Submission.QuadrilateralSevenCheck24
import Submission.QuadrilateralSevenCheck25
import Submission.QuadrilateralSevenCheck26
import Submission.QuadrilateralSevenCheck27
import Submission.QuadrilateralSevenCheck28
import Submission.QuadrilateralSevenCheck29
import Submission.QuadrilateralSevenCheck30
import Submission.QuadrilateralSevenCheck31

/-! Full single-root normalized classification at order seven. -/
namespace Erdos184.QuadrilateralOutsideData
set_option maxRecDepth 100000
lemma range_checked_7 : checkRange 7 15 0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_0, seven_block_1⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_2, seven_block_3⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_4, seven_block_5⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_6, seven_block_7⟩⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_8, seven_block_9⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_10, seven_block_11⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_12, seven_block_13⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_14, seven_block_15⟩⟩⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_16, seven_block_17⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_18, seven_block_19⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_20, seven_block_21⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_22, seven_block_23⟩⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_24, seven_block_25⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_26, seven_block_27⟩⟩, Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨seven_block_28, seven_block_29⟩, Bool.and_eq_true_iff.mpr ⟨seven_block_30, seven_block_31⟩⟩⟩⟩⟩

lemma checked_7_single_root (code : Fin 32768) :
    eligible 7 code.val = true → code.val ∈ patterns 7 := by
  simpa only [Nat.zero_add] using
    checkRange_sound 7 15 0 range_checked_7 code.val code.isLt
end Erdos184.QuadrilateralOutsideData

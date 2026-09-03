import Submission.PureSevenGeneratorsBase
import Submission.PureSevenProjectionNumbers
import Submission.PureSixActionNumbers0

/-! Rowwise commutation of the five seven-color generators with omission of color six. -/
namespace Erdos184Work.PureSevenGeneratorProjectionNumbers
open PureSevenProjectionNumbers
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def sixGenerator : Fin 5 → Fin 720 := ![120,24,6,2,1]

lemma color_compatible : ∀ (g : Fin 5) (i : Fin 6),
    PureSevenGenerators.colorMap g i.castSucc =
      (PureSixActions0.colorMap (sixGenerator g) i).castSucc := by decide +kernel

lemma row_compatible : ∀ (g : Fin 5) (i : Fin 6) (q : Fin 60),
    (projectRow (PureSixActions0.colorMap (sixGenerator g) i)
      (PureSevenGenerators.rowImage g i.castSucc q)).val =
    PureSixActions0.data (sixGenerator g) i (projectRow i q).val % 12 := by decide +kernel

lemma six_choices : ∀ i : Fin 6, PureSixRowModel0.choices i = 12 := by decide +kernel

#print axioms color_compatible
#print axioms row_compatible
end Erdos184Work.PureSevenGeneratorProjectionNumbers

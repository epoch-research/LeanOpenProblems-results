import Submission.PureSevenGenerators
import Submission.PureSevenGeneratorProjectionNumbers
import Submission.PureSixActions0

/-! The five generator actions commute with deletion of color six. -/
namespace Erdos184Work.PureSevenGeneratorProjection
open PureSevenProjectionNumbers PureSevenGeneratorProjectionNumbers
set_option maxHeartbeats 1500000

lemma generator_project (g : Fin 5) (q : PureSevenRowModel.Rows) :
    project6 ((PureSevenGenerators.action g).apply q) =
      (PureSixActions0.action (sixGenerator g)).apply (project6 q) := by
  funext j
  apply Fin.ext
  obtain ⟨i,rfl⟩ := (PureSixActions0.action (sixGenerator g)).color.surjective j
  rw [CyclicRowActions.Action.apply_color]
  have hc : (PureSixActions0.colorMap (sixGenerator g) i).castSucc =
      (PureSevenGenerators.action g).color i.castSucc := (color_compatible g i).symm
  calc
    (project6 ((PureSevenGenerators.action g).apply q)
        ((PureSixActions0.action (sixGenerator g)).color i)).val =
      (projectRow (PureSixActions0.colorMap (sixGenerator g) i)
        ((PureSevenGenerators.action g).apply q
          (PureSixActions0.colorMap (sixGenerator g) i).castSucc)).val :=
      project6_row _ _
    _ = (projectRow (PureSixActions0.colorMap (sixGenerator g) i)
        (PureSevenGenerators.rowImage g i.castSucc (q i.castSucc))).val := by
      rw [hc,CyclicRowActions.Action.apply_color]
      rfl
    _ = PureSixActions0.data (sixGenerator g) i (projectRow i (q i.castSucc)).val % 12 :=
      row_compatible g i (q i.castSucc)
    _ = ((PureSixActions0.action (sixGenerator g)).row i (project6 q i)).val := by
      change _ = PureSixActions0.data (sixGenerator g) i (project6 q i).val %
        PureSixRowModel0.choices (PureSixActions0.colorMap (sixGenerator g) i)
      rw [project6_row,six_choices]

#print axioms generator_project
end Erdos184Work.PureSevenGeneratorProjection

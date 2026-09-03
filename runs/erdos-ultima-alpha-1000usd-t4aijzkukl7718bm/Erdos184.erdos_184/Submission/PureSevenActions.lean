import Submission.PureSevenActionsCheck00
import Submission.PureSevenActionsCheck01
import Submission.PureSevenActionsCheck02
import Submission.PureSevenActionsCheck03
import Submission.PureSevenActionsCheck04
import Submission.PureSevenActionsCheck05
import Submission.PureSevenActionsCheck06
import Submission.PureSevenActionsCheck07
import Submission.PureSevenActionsCheck08
import Submission.PureSevenActionsCheck09
import Submission.PureSevenActionsCheck10
import Submission.PureSevenActionsCheck11
import Submission.PureSevenActionsCheck12
import Submission.PureSevenActionsCheck13
import Submission.PureSevenActionsCheck14
import Submission.PureSevenActionsCheck15
import Submission.PureSevenActionsCheck16
import Submission.PureSevenActionsCheck17
import Submission.PureSevenActionsCheck18
import Submission.PureSevenActionsCheck19
import Submission.PureSevenActionsCheck20
import Submission.PureSevenActionsCheck21
import Submission.PureSevenActionsCheck22
import Submission.PureSevenActionsCheck23
import Submission.PureSevenActionsCheck24
import Submission.PureSevenActionsCheck25
import Submission.PureSevenActionsCheck26
import Submission.PureSevenActionsCheck27
import Submission.PureSevenActionsCheck28
import Submission.PureSevenActionsCheck29
import Submission.PureSevenActionsCheck30
import Submission.PureSevenActionsCheck31
import Submission.PureSevenActionsCheck32
import Submission.PureSevenActionsCheck33
import Submission.PureSevenActionsCheck34
import Submission.PureSevenActionsCheck35
import Submission.PureSevenActionsCheck36
import Submission.PureSevenActionsCheck37
import Submission.PureSevenActionsCheck38
import Submission.PureSevenActionsCheck39
import Submission.PureSevenActionsCheck40
import Submission.PureSevenActionsCheck41
import Submission.PureSevenActionsCheck42
import Submission.PureSevenActionsCheck43
import Submission.PureSevenActionsCheck44
import Submission.PureSevenActionsCheck45
import Submission.PureSevenActionsCheck46
import Submission.PureSevenActionsCheck47
import Submission.PureSevenActionsCheck48
import Submission.PureSevenActionsCheck49
import Submission.PureSevenActionsCheck50
import Submission.PureSevenActionsCheck51
import Submission.PureSevenActionsCheck52
import Submission.PureSevenActionsCheck53
import Submission.PureSevenActionsCheck54
import Submission.PureSevenActionsCheck55
import Submission.PureSevenActionsCheck56
import Submission.PureSevenActionsCheck57
import Submission.PureSevenActionsCheck58
import Submission.PureSevenActionsCheck59
namespace Erdos184Work.PureSevenActions
open CyclicRowActions PureSevenGeneratorProjectionNumbers PureSevenProjectionNumbers PureSevenGeneratorProjection
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false
lemma matches_all : FiniteIntervals.Covers MatchesAt 0 720 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval0 (FiniteIntervals.merge matches_interval1 matches_interval2)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval3 matches_interval4) (FiniteIntervals.merge matches_interval5 matches_interval6))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval7 matches_interval8) (FiniteIntervals.merge matches_interval9 matches_interval10)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval11 matches_interval12) (FiniteIntervals.merge matches_interval13 matches_interval14)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval15 (FiniteIntervals.merge matches_interval16 matches_interval17)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval18 matches_interval19) (FiniteIntervals.merge matches_interval20 matches_interval21))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval22 matches_interval23) (FiniteIntervals.merge matches_interval24 matches_interval25)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval26 matches_interval27) (FiniteIntervals.merge matches_interval28 matches_interval29))))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval30 (FiniteIntervals.merge matches_interval31 matches_interval32)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval33 matches_interval34) (FiniteIntervals.merge matches_interval35 matches_interval36))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval37 matches_interval38) (FiniteIntervals.merge matches_interval39 matches_interval40)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval41 matches_interval42) (FiniteIntervals.merge matches_interval43 matches_interval44)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval45 (FiniteIntervals.merge matches_interval46 matches_interval47)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval48 matches_interval49) (FiniteIntervals.merge matches_interval50 matches_interval51))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge matches_interval52 matches_interval53) (FiniteIntervals.merge matches_interval54 matches_interval55)) (FiniteIntervals.merge (FiniteIntervals.merge matches_interval56 matches_interval57) (FiniteIntervals.merge matches_interval58 matches_interval59))))))
lemma matches_group (g : Fin 720) : Matches g := matches_all g.val (Nat.zero_le _) g.isLt g.isLt
lemma sixAction_apply (g : Fin 720) (q : PureSixRowModel0.Rows) :
    (sixAction g).apply q = (PureSixActions0.action g).apply q :=
  Action.apply_eq_of_rows _ _ (matches_group g).1 (matches_group g).2 q
lemma sequence_projection (gs : List (Fin 5)) (q : PureSevenRowModel.Rows) :
    project6 ((Action.sequence PureSevenGenerators.action gs).apply q) =
      (Action.sequence (fun h => PureSixActions0.action (sixGenerator h)) gs).apply (project6 q) := by
  induction gs generalizing q with
  | nil => rw [Action.sequence_apply_nil,Action.sequence_apply_nil]
  | cons g gs ih =>
    rw [Action.sequence_apply_cons,Action.sequence_apply_cons,ih,generator_project]
lemma action_projection (g : Fin 720) (q : PureSevenRowModel.Rows) :
    project6 ((action g).apply q) = (PureSixActions0.action g).apply (project6 q) :=
  (sequence_projection (word g) q).trans (sixAction_apply g _)
#print axioms action_projection
end Erdos184Work.PureSevenActions

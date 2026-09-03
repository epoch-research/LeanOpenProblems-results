import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_612 : Matches 612 := by decide +kernel
lemma match_part612 : FiniteIntervals.Covers MatchesAt 612 613 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 612 1
  intro i
  fin_cases i
  intro h
  exact matches_612
lemma matches_613 : Matches 613 := by decide +kernel
lemma match_part613 : FiniteIntervals.Covers MatchesAt 613 614 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 613 1
  intro i
  fin_cases i
  intro h
  exact matches_613
lemma matches_614 : Matches 614 := by decide +kernel
lemma match_part614 : FiniteIntervals.Covers MatchesAt 614 615 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 614 1
  intro i
  fin_cases i
  intro h
  exact matches_614
lemma matches_615 : Matches 615 := by decide +kernel
lemma match_part615 : FiniteIntervals.Covers MatchesAt 615 616 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 615 1
  intro i
  fin_cases i
  intro h
  exact matches_615
lemma matches_616 : Matches 616 := by decide +kernel
lemma match_part616 : FiniteIntervals.Covers MatchesAt 616 617 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 616 1
  intro i
  fin_cases i
  intro h
  exact matches_616
lemma matches_617 : Matches 617 := by decide +kernel
lemma match_part617 : FiniteIntervals.Covers MatchesAt 617 618 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 617 1
  intro i
  fin_cases i
  intro h
  exact matches_617
lemma matches_618 : Matches 618 := by decide +kernel
lemma match_part618 : FiniteIntervals.Covers MatchesAt 618 619 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 618 1
  intro i
  fin_cases i
  intro h
  exact matches_618
lemma matches_619 : Matches 619 := by decide +kernel
lemma match_part619 : FiniteIntervals.Covers MatchesAt 619 620 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 619 1
  intro i
  fin_cases i
  intro h
  exact matches_619
lemma matches_620 : Matches 620 := by decide +kernel
lemma match_part620 : FiniteIntervals.Covers MatchesAt 620 621 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 620 1
  intro i
  fin_cases i
  intro h
  exact matches_620
lemma matches_621 : Matches 621 := by decide +kernel
lemma match_part621 : FiniteIntervals.Covers MatchesAt 621 622 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 621 1
  intro i
  fin_cases i
  intro h
  exact matches_621
lemma matches_622 : Matches 622 := by decide +kernel
lemma match_part622 : FiniteIntervals.Covers MatchesAt 622 623 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 622 1
  intro i
  fin_cases i
  intro h
  exact matches_622
lemma matches_623 : Matches 623 := by decide +kernel
lemma match_part623 : FiniteIntervals.Covers MatchesAt 623 624 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 623 1
  intro i
  fin_cases i
  intro h
  exact matches_623
lemma matches_interval51 : FiniteIntervals.Covers MatchesAt 612 624 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part612 (FiniteIntervals.merge match_part613 match_part614)) (FiniteIntervals.merge match_part615 (FiniteIntervals.merge match_part616 match_part617))) (FiniteIntervals.merge (FiniteIntervals.merge match_part618 (FiniteIntervals.merge match_part619 match_part620)) (FiniteIntervals.merge match_part621 (FiniteIntervals.merge match_part622 match_part623))))
#print axioms matches_interval51
end Erdos184Work.PureSevenActions

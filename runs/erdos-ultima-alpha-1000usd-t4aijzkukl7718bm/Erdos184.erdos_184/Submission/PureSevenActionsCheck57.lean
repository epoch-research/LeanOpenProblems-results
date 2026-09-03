import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_684 : Matches 684 := by decide +kernel
lemma match_part684 : FiniteIntervals.Covers MatchesAt 684 685 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 684 1
  intro i
  fin_cases i
  intro h
  exact matches_684
lemma matches_685 : Matches 685 := by decide +kernel
lemma match_part685 : FiniteIntervals.Covers MatchesAt 685 686 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 685 1
  intro i
  fin_cases i
  intro h
  exact matches_685
lemma matches_686 : Matches 686 := by decide +kernel
lemma match_part686 : FiniteIntervals.Covers MatchesAt 686 687 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 686 1
  intro i
  fin_cases i
  intro h
  exact matches_686
lemma matches_687 : Matches 687 := by decide +kernel
lemma match_part687 : FiniteIntervals.Covers MatchesAt 687 688 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 687 1
  intro i
  fin_cases i
  intro h
  exact matches_687
lemma matches_688 : Matches 688 := by decide +kernel
lemma match_part688 : FiniteIntervals.Covers MatchesAt 688 689 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 688 1
  intro i
  fin_cases i
  intro h
  exact matches_688
lemma matches_689 : Matches 689 := by decide +kernel
lemma match_part689 : FiniteIntervals.Covers MatchesAt 689 690 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 689 1
  intro i
  fin_cases i
  intro h
  exact matches_689
lemma matches_690 : Matches 690 := by decide +kernel
lemma match_part690 : FiniteIntervals.Covers MatchesAt 690 691 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 690 1
  intro i
  fin_cases i
  intro h
  exact matches_690
lemma matches_691 : Matches 691 := by decide +kernel
lemma match_part691 : FiniteIntervals.Covers MatchesAt 691 692 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 691 1
  intro i
  fin_cases i
  intro h
  exact matches_691
lemma matches_692 : Matches 692 := by decide +kernel
lemma match_part692 : FiniteIntervals.Covers MatchesAt 692 693 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 692 1
  intro i
  fin_cases i
  intro h
  exact matches_692
lemma matches_693 : Matches 693 := by decide +kernel
lemma match_part693 : FiniteIntervals.Covers MatchesAt 693 694 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 693 1
  intro i
  fin_cases i
  intro h
  exact matches_693
lemma matches_694 : Matches 694 := by decide +kernel
lemma match_part694 : FiniteIntervals.Covers MatchesAt 694 695 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 694 1
  intro i
  fin_cases i
  intro h
  exact matches_694
lemma matches_695 : Matches 695 := by decide +kernel
lemma match_part695 : FiniteIntervals.Covers MatchesAt 695 696 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 695 1
  intro i
  fin_cases i
  intro h
  exact matches_695
lemma matches_interval57 : FiniteIntervals.Covers MatchesAt 684 696 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part684 (FiniteIntervals.merge match_part685 match_part686)) (FiniteIntervals.merge match_part687 (FiniteIntervals.merge match_part688 match_part689))) (FiniteIntervals.merge (FiniteIntervals.merge match_part690 (FiniteIntervals.merge match_part691 match_part692)) (FiniteIntervals.merge match_part693 (FiniteIntervals.merge match_part694 match_part695))))
#print axioms matches_interval57
end Erdos184Work.PureSevenActions

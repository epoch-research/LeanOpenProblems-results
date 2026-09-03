import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_696 : Matches 696 := by decide +kernel
lemma match_part696 : FiniteIntervals.Covers MatchesAt 696 697 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 696 1
  intro i
  fin_cases i
  intro h
  exact matches_696
lemma matches_697 : Matches 697 := by decide +kernel
lemma match_part697 : FiniteIntervals.Covers MatchesAt 697 698 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 697 1
  intro i
  fin_cases i
  intro h
  exact matches_697
lemma matches_698 : Matches 698 := by decide +kernel
lemma match_part698 : FiniteIntervals.Covers MatchesAt 698 699 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 698 1
  intro i
  fin_cases i
  intro h
  exact matches_698
lemma matches_699 : Matches 699 := by decide +kernel
lemma match_part699 : FiniteIntervals.Covers MatchesAt 699 700 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 699 1
  intro i
  fin_cases i
  intro h
  exact matches_699
lemma matches_700 : Matches 700 := by decide +kernel
lemma match_part700 : FiniteIntervals.Covers MatchesAt 700 701 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 700 1
  intro i
  fin_cases i
  intro h
  exact matches_700
lemma matches_701 : Matches 701 := by decide +kernel
lemma match_part701 : FiniteIntervals.Covers MatchesAt 701 702 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 701 1
  intro i
  fin_cases i
  intro h
  exact matches_701
lemma matches_702 : Matches 702 := by decide +kernel
lemma match_part702 : FiniteIntervals.Covers MatchesAt 702 703 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 702 1
  intro i
  fin_cases i
  intro h
  exact matches_702
lemma matches_703 : Matches 703 := by decide +kernel
lemma match_part703 : FiniteIntervals.Covers MatchesAt 703 704 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 703 1
  intro i
  fin_cases i
  intro h
  exact matches_703
lemma matches_704 : Matches 704 := by decide +kernel
lemma match_part704 : FiniteIntervals.Covers MatchesAt 704 705 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 704 1
  intro i
  fin_cases i
  intro h
  exact matches_704
lemma matches_705 : Matches 705 := by decide +kernel
lemma match_part705 : FiniteIntervals.Covers MatchesAt 705 706 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 705 1
  intro i
  fin_cases i
  intro h
  exact matches_705
lemma matches_706 : Matches 706 := by decide +kernel
lemma match_part706 : FiniteIntervals.Covers MatchesAt 706 707 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 706 1
  intro i
  fin_cases i
  intro h
  exact matches_706
lemma matches_707 : Matches 707 := by decide +kernel
lemma match_part707 : FiniteIntervals.Covers MatchesAt 707 708 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 707 1
  intro i
  fin_cases i
  intro h
  exact matches_707
lemma matches_interval58 : FiniteIntervals.Covers MatchesAt 696 708 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part696 (FiniteIntervals.merge match_part697 match_part698)) (FiniteIntervals.merge match_part699 (FiniteIntervals.merge match_part700 match_part701))) (FiniteIntervals.merge (FiniteIntervals.merge match_part702 (FiniteIntervals.merge match_part703 match_part704)) (FiniteIntervals.merge match_part705 (FiniteIntervals.merge match_part706 match_part707))))
#print axioms matches_interval58
end Erdos184Work.PureSevenActions

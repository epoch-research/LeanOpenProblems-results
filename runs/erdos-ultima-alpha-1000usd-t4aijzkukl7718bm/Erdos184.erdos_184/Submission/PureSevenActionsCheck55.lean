import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_660 : Matches 660 := by decide +kernel
lemma match_part660 : FiniteIntervals.Covers MatchesAt 660 661 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 660 1
  intro i
  fin_cases i
  intro h
  exact matches_660
lemma matches_661 : Matches 661 := by decide +kernel
lemma match_part661 : FiniteIntervals.Covers MatchesAt 661 662 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 661 1
  intro i
  fin_cases i
  intro h
  exact matches_661
lemma matches_662 : Matches 662 := by decide +kernel
lemma match_part662 : FiniteIntervals.Covers MatchesAt 662 663 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 662 1
  intro i
  fin_cases i
  intro h
  exact matches_662
lemma matches_663 : Matches 663 := by decide +kernel
lemma match_part663 : FiniteIntervals.Covers MatchesAt 663 664 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 663 1
  intro i
  fin_cases i
  intro h
  exact matches_663
lemma matches_664 : Matches 664 := by decide +kernel
lemma match_part664 : FiniteIntervals.Covers MatchesAt 664 665 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 664 1
  intro i
  fin_cases i
  intro h
  exact matches_664
lemma matches_665 : Matches 665 := by decide +kernel
lemma match_part665 : FiniteIntervals.Covers MatchesAt 665 666 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 665 1
  intro i
  fin_cases i
  intro h
  exact matches_665
lemma matches_666 : Matches 666 := by decide +kernel
lemma match_part666 : FiniteIntervals.Covers MatchesAt 666 667 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 666 1
  intro i
  fin_cases i
  intro h
  exact matches_666
lemma matches_667 : Matches 667 := by decide +kernel
lemma match_part667 : FiniteIntervals.Covers MatchesAt 667 668 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 667 1
  intro i
  fin_cases i
  intro h
  exact matches_667
lemma matches_668 : Matches 668 := by decide +kernel
lemma match_part668 : FiniteIntervals.Covers MatchesAt 668 669 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 668 1
  intro i
  fin_cases i
  intro h
  exact matches_668
lemma matches_669 : Matches 669 := by decide +kernel
lemma match_part669 : FiniteIntervals.Covers MatchesAt 669 670 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 669 1
  intro i
  fin_cases i
  intro h
  exact matches_669
lemma matches_670 : Matches 670 := by decide +kernel
lemma match_part670 : FiniteIntervals.Covers MatchesAt 670 671 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 670 1
  intro i
  fin_cases i
  intro h
  exact matches_670
lemma matches_671 : Matches 671 := by decide +kernel
lemma match_part671 : FiniteIntervals.Covers MatchesAt 671 672 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 671 1
  intro i
  fin_cases i
  intro h
  exact matches_671
lemma matches_interval55 : FiniteIntervals.Covers MatchesAt 660 672 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part660 (FiniteIntervals.merge match_part661 match_part662)) (FiniteIntervals.merge match_part663 (FiniteIntervals.merge match_part664 match_part665))) (FiniteIntervals.merge (FiniteIntervals.merge match_part666 (FiniteIntervals.merge match_part667 match_part668)) (FiniteIntervals.merge match_part669 (FiniteIntervals.merge match_part670 match_part671))))
#print axioms matches_interval55
end Erdos184Work.PureSevenActions

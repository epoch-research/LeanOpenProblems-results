import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_564 : Matches 564 := by decide +kernel
lemma match_part564 : FiniteIntervals.Covers MatchesAt 564 565 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 564 1
  intro i
  fin_cases i
  intro h
  exact matches_564
lemma matches_565 : Matches 565 := by decide +kernel
lemma match_part565 : FiniteIntervals.Covers MatchesAt 565 566 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 565 1
  intro i
  fin_cases i
  intro h
  exact matches_565
lemma matches_566 : Matches 566 := by decide +kernel
lemma match_part566 : FiniteIntervals.Covers MatchesAt 566 567 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 566 1
  intro i
  fin_cases i
  intro h
  exact matches_566
lemma matches_567 : Matches 567 := by decide +kernel
lemma match_part567 : FiniteIntervals.Covers MatchesAt 567 568 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 567 1
  intro i
  fin_cases i
  intro h
  exact matches_567
lemma matches_568 : Matches 568 := by decide +kernel
lemma match_part568 : FiniteIntervals.Covers MatchesAt 568 569 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 568 1
  intro i
  fin_cases i
  intro h
  exact matches_568
lemma matches_569 : Matches 569 := by decide +kernel
lemma match_part569 : FiniteIntervals.Covers MatchesAt 569 570 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 569 1
  intro i
  fin_cases i
  intro h
  exact matches_569
lemma matches_570 : Matches 570 := by decide +kernel
lemma match_part570 : FiniteIntervals.Covers MatchesAt 570 571 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 570 1
  intro i
  fin_cases i
  intro h
  exact matches_570
lemma matches_571 : Matches 571 := by decide +kernel
lemma match_part571 : FiniteIntervals.Covers MatchesAt 571 572 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 571 1
  intro i
  fin_cases i
  intro h
  exact matches_571
lemma matches_572 : Matches 572 := by decide +kernel
lemma match_part572 : FiniteIntervals.Covers MatchesAt 572 573 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 572 1
  intro i
  fin_cases i
  intro h
  exact matches_572
lemma matches_573 : Matches 573 := by decide +kernel
lemma match_part573 : FiniteIntervals.Covers MatchesAt 573 574 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 573 1
  intro i
  fin_cases i
  intro h
  exact matches_573
lemma matches_574 : Matches 574 := by decide +kernel
lemma match_part574 : FiniteIntervals.Covers MatchesAt 574 575 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 574 1
  intro i
  fin_cases i
  intro h
  exact matches_574
lemma matches_575 : Matches 575 := by decide +kernel
lemma match_part575 : FiniteIntervals.Covers MatchesAt 575 576 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 575 1
  intro i
  fin_cases i
  intro h
  exact matches_575
lemma matches_interval47 : FiniteIntervals.Covers MatchesAt 564 576 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part564 (FiniteIntervals.merge match_part565 match_part566)) (FiniteIntervals.merge match_part567 (FiniteIntervals.merge match_part568 match_part569))) (FiniteIntervals.merge (FiniteIntervals.merge match_part570 (FiniteIntervals.merge match_part571 match_part572)) (FiniteIntervals.merge match_part573 (FiniteIntervals.merge match_part574 match_part575))))
#print axioms matches_interval47
end Erdos184Work.PureSevenActions

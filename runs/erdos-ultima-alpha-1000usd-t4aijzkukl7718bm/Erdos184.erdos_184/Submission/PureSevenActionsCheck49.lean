import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_588 : Matches 588 := by decide +kernel
lemma match_part588 : FiniteIntervals.Covers MatchesAt 588 589 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 588 1
  intro i
  fin_cases i
  intro h
  exact matches_588
lemma matches_589 : Matches 589 := by decide +kernel
lemma match_part589 : FiniteIntervals.Covers MatchesAt 589 590 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 589 1
  intro i
  fin_cases i
  intro h
  exact matches_589
lemma matches_590 : Matches 590 := by decide +kernel
lemma match_part590 : FiniteIntervals.Covers MatchesAt 590 591 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 590 1
  intro i
  fin_cases i
  intro h
  exact matches_590
lemma matches_591 : Matches 591 := by decide +kernel
lemma match_part591 : FiniteIntervals.Covers MatchesAt 591 592 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 591 1
  intro i
  fin_cases i
  intro h
  exact matches_591
lemma matches_592 : Matches 592 := by decide +kernel
lemma match_part592 : FiniteIntervals.Covers MatchesAt 592 593 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 592 1
  intro i
  fin_cases i
  intro h
  exact matches_592
lemma matches_593 : Matches 593 := by decide +kernel
lemma match_part593 : FiniteIntervals.Covers MatchesAt 593 594 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 593 1
  intro i
  fin_cases i
  intro h
  exact matches_593
lemma matches_594 : Matches 594 := by decide +kernel
lemma match_part594 : FiniteIntervals.Covers MatchesAt 594 595 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 594 1
  intro i
  fin_cases i
  intro h
  exact matches_594
lemma matches_595 : Matches 595 := by decide +kernel
lemma match_part595 : FiniteIntervals.Covers MatchesAt 595 596 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 595 1
  intro i
  fin_cases i
  intro h
  exact matches_595
lemma matches_596 : Matches 596 := by decide +kernel
lemma match_part596 : FiniteIntervals.Covers MatchesAt 596 597 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 596 1
  intro i
  fin_cases i
  intro h
  exact matches_596
lemma matches_597 : Matches 597 := by decide +kernel
lemma match_part597 : FiniteIntervals.Covers MatchesAt 597 598 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 597 1
  intro i
  fin_cases i
  intro h
  exact matches_597
lemma matches_598 : Matches 598 := by decide +kernel
lemma match_part598 : FiniteIntervals.Covers MatchesAt 598 599 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 598 1
  intro i
  fin_cases i
  intro h
  exact matches_598
lemma matches_599 : Matches 599 := by decide +kernel
lemma match_part599 : FiniteIntervals.Covers MatchesAt 599 600 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 599 1
  intro i
  fin_cases i
  intro h
  exact matches_599
lemma matches_interval49 : FiniteIntervals.Covers MatchesAt 588 600 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part588 (FiniteIntervals.merge match_part589 match_part590)) (FiniteIntervals.merge match_part591 (FiniteIntervals.merge match_part592 match_part593))) (FiniteIntervals.merge (FiniteIntervals.merge match_part594 (FiniteIntervals.merge match_part595 match_part596)) (FiniteIntervals.merge match_part597 (FiniteIntervals.merge match_part598 match_part599))))
#print axioms matches_interval49
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_600 : Matches 600 := by decide +kernel
lemma match_part600 : FiniteIntervals.Covers MatchesAt 600 601 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 600 1
  intro i
  fin_cases i
  intro h
  exact matches_600
lemma matches_601 : Matches 601 := by decide +kernel
lemma match_part601 : FiniteIntervals.Covers MatchesAt 601 602 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 601 1
  intro i
  fin_cases i
  intro h
  exact matches_601
lemma matches_602 : Matches 602 := by decide +kernel
lemma match_part602 : FiniteIntervals.Covers MatchesAt 602 603 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 602 1
  intro i
  fin_cases i
  intro h
  exact matches_602
lemma matches_603 : Matches 603 := by decide +kernel
lemma match_part603 : FiniteIntervals.Covers MatchesAt 603 604 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 603 1
  intro i
  fin_cases i
  intro h
  exact matches_603
lemma matches_604 : Matches 604 := by decide +kernel
lemma match_part604 : FiniteIntervals.Covers MatchesAt 604 605 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 604 1
  intro i
  fin_cases i
  intro h
  exact matches_604
lemma matches_605 : Matches 605 := by decide +kernel
lemma match_part605 : FiniteIntervals.Covers MatchesAt 605 606 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 605 1
  intro i
  fin_cases i
  intro h
  exact matches_605
lemma matches_606 : Matches 606 := by decide +kernel
lemma match_part606 : FiniteIntervals.Covers MatchesAt 606 607 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 606 1
  intro i
  fin_cases i
  intro h
  exact matches_606
lemma matches_607 : Matches 607 := by decide +kernel
lemma match_part607 : FiniteIntervals.Covers MatchesAt 607 608 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 607 1
  intro i
  fin_cases i
  intro h
  exact matches_607
lemma matches_608 : Matches 608 := by decide +kernel
lemma match_part608 : FiniteIntervals.Covers MatchesAt 608 609 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 608 1
  intro i
  fin_cases i
  intro h
  exact matches_608
lemma matches_609 : Matches 609 := by decide +kernel
lemma match_part609 : FiniteIntervals.Covers MatchesAt 609 610 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 609 1
  intro i
  fin_cases i
  intro h
  exact matches_609
lemma matches_610 : Matches 610 := by decide +kernel
lemma match_part610 : FiniteIntervals.Covers MatchesAt 610 611 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 610 1
  intro i
  fin_cases i
  intro h
  exact matches_610
lemma matches_611 : Matches 611 := by decide +kernel
lemma match_part611 : FiniteIntervals.Covers MatchesAt 611 612 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 611 1
  intro i
  fin_cases i
  intro h
  exact matches_611
lemma matches_interval50 : FiniteIntervals.Covers MatchesAt 600 612 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part600 (FiniteIntervals.merge match_part601 match_part602)) (FiniteIntervals.merge match_part603 (FiniteIntervals.merge match_part604 match_part605))) (FiniteIntervals.merge (FiniteIntervals.merge match_part606 (FiniteIntervals.merge match_part607 match_part608)) (FiniteIntervals.merge match_part609 (FiniteIntervals.merge match_part610 match_part611))))
#print axioms matches_interval50
end Erdos184Work.PureSevenActions

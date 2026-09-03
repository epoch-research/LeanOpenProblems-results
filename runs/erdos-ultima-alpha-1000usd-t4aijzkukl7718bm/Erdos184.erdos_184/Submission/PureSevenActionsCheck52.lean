import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_624 : Matches 624 := by decide +kernel
lemma match_part624 : FiniteIntervals.Covers MatchesAt 624 625 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 624 1
  intro i
  fin_cases i
  intro h
  exact matches_624
lemma matches_625 : Matches 625 := by decide +kernel
lemma match_part625 : FiniteIntervals.Covers MatchesAt 625 626 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 625 1
  intro i
  fin_cases i
  intro h
  exact matches_625
lemma matches_626 : Matches 626 := by decide +kernel
lemma match_part626 : FiniteIntervals.Covers MatchesAt 626 627 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 626 1
  intro i
  fin_cases i
  intro h
  exact matches_626
lemma matches_627 : Matches 627 := by decide +kernel
lemma match_part627 : FiniteIntervals.Covers MatchesAt 627 628 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 627 1
  intro i
  fin_cases i
  intro h
  exact matches_627
lemma matches_628 : Matches 628 := by decide +kernel
lemma match_part628 : FiniteIntervals.Covers MatchesAt 628 629 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 628 1
  intro i
  fin_cases i
  intro h
  exact matches_628
lemma matches_629 : Matches 629 := by decide +kernel
lemma match_part629 : FiniteIntervals.Covers MatchesAt 629 630 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 629 1
  intro i
  fin_cases i
  intro h
  exact matches_629
lemma matches_630 : Matches 630 := by decide +kernel
lemma match_part630 : FiniteIntervals.Covers MatchesAt 630 631 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 630 1
  intro i
  fin_cases i
  intro h
  exact matches_630
lemma matches_631 : Matches 631 := by decide +kernel
lemma match_part631 : FiniteIntervals.Covers MatchesAt 631 632 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 631 1
  intro i
  fin_cases i
  intro h
  exact matches_631
lemma matches_632 : Matches 632 := by decide +kernel
lemma match_part632 : FiniteIntervals.Covers MatchesAt 632 633 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 632 1
  intro i
  fin_cases i
  intro h
  exact matches_632
lemma matches_633 : Matches 633 := by decide +kernel
lemma match_part633 : FiniteIntervals.Covers MatchesAt 633 634 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 633 1
  intro i
  fin_cases i
  intro h
  exact matches_633
lemma matches_634 : Matches 634 := by decide +kernel
lemma match_part634 : FiniteIntervals.Covers MatchesAt 634 635 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 634 1
  intro i
  fin_cases i
  intro h
  exact matches_634
lemma matches_635 : Matches 635 := by decide +kernel
lemma match_part635 : FiniteIntervals.Covers MatchesAt 635 636 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 635 1
  intro i
  fin_cases i
  intro h
  exact matches_635
lemma matches_interval52 : FiniteIntervals.Covers MatchesAt 624 636 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part624 (FiniteIntervals.merge match_part625 match_part626)) (FiniteIntervals.merge match_part627 (FiniteIntervals.merge match_part628 match_part629))) (FiniteIntervals.merge (FiniteIntervals.merge match_part630 (FiniteIntervals.merge match_part631 match_part632)) (FiniteIntervals.merge match_part633 (FiniteIntervals.merge match_part634 match_part635))))
#print axioms matches_interval52
end Erdos184Work.PureSevenActions

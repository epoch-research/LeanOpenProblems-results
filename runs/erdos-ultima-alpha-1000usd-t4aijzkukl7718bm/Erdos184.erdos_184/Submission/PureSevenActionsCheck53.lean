import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_636 : Matches 636 := by decide +kernel
lemma match_part636 : FiniteIntervals.Covers MatchesAt 636 637 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 636 1
  intro i
  fin_cases i
  intro h
  exact matches_636
lemma matches_637 : Matches 637 := by decide +kernel
lemma match_part637 : FiniteIntervals.Covers MatchesAt 637 638 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 637 1
  intro i
  fin_cases i
  intro h
  exact matches_637
lemma matches_638 : Matches 638 := by decide +kernel
lemma match_part638 : FiniteIntervals.Covers MatchesAt 638 639 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 638 1
  intro i
  fin_cases i
  intro h
  exact matches_638
lemma matches_639 : Matches 639 := by decide +kernel
lemma match_part639 : FiniteIntervals.Covers MatchesAt 639 640 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 639 1
  intro i
  fin_cases i
  intro h
  exact matches_639
lemma matches_640 : Matches 640 := by decide +kernel
lemma match_part640 : FiniteIntervals.Covers MatchesAt 640 641 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 640 1
  intro i
  fin_cases i
  intro h
  exact matches_640
lemma matches_641 : Matches 641 := by decide +kernel
lemma match_part641 : FiniteIntervals.Covers MatchesAt 641 642 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 641 1
  intro i
  fin_cases i
  intro h
  exact matches_641
lemma matches_642 : Matches 642 := by decide +kernel
lemma match_part642 : FiniteIntervals.Covers MatchesAt 642 643 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 642 1
  intro i
  fin_cases i
  intro h
  exact matches_642
lemma matches_643 : Matches 643 := by decide +kernel
lemma match_part643 : FiniteIntervals.Covers MatchesAt 643 644 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 643 1
  intro i
  fin_cases i
  intro h
  exact matches_643
lemma matches_644 : Matches 644 := by decide +kernel
lemma match_part644 : FiniteIntervals.Covers MatchesAt 644 645 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 644 1
  intro i
  fin_cases i
  intro h
  exact matches_644
lemma matches_645 : Matches 645 := by decide +kernel
lemma match_part645 : FiniteIntervals.Covers MatchesAt 645 646 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 645 1
  intro i
  fin_cases i
  intro h
  exact matches_645
lemma matches_646 : Matches 646 := by decide +kernel
lemma match_part646 : FiniteIntervals.Covers MatchesAt 646 647 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 646 1
  intro i
  fin_cases i
  intro h
  exact matches_646
lemma matches_647 : Matches 647 := by decide +kernel
lemma match_part647 : FiniteIntervals.Covers MatchesAt 647 648 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 647 1
  intro i
  fin_cases i
  intro h
  exact matches_647
lemma matches_interval53 : FiniteIntervals.Covers MatchesAt 636 648 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part636 (FiniteIntervals.merge match_part637 match_part638)) (FiniteIntervals.merge match_part639 (FiniteIntervals.merge match_part640 match_part641))) (FiniteIntervals.merge (FiniteIntervals.merge match_part642 (FiniteIntervals.merge match_part643 match_part644)) (FiniteIntervals.merge match_part645 (FiniteIntervals.merge match_part646 match_part647))))
#print axioms matches_interval53
end Erdos184Work.PureSevenActions

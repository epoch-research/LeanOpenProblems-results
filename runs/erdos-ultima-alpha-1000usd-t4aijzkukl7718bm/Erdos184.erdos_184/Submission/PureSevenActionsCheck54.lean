import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_648 : Matches 648 := by decide +kernel
lemma match_part648 : FiniteIntervals.Covers MatchesAt 648 649 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 648 1
  intro i
  fin_cases i
  intro h
  exact matches_648
lemma matches_649 : Matches 649 := by decide +kernel
lemma match_part649 : FiniteIntervals.Covers MatchesAt 649 650 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 649 1
  intro i
  fin_cases i
  intro h
  exact matches_649
lemma matches_650 : Matches 650 := by decide +kernel
lemma match_part650 : FiniteIntervals.Covers MatchesAt 650 651 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 650 1
  intro i
  fin_cases i
  intro h
  exact matches_650
lemma matches_651 : Matches 651 := by decide +kernel
lemma match_part651 : FiniteIntervals.Covers MatchesAt 651 652 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 651 1
  intro i
  fin_cases i
  intro h
  exact matches_651
lemma matches_652 : Matches 652 := by decide +kernel
lemma match_part652 : FiniteIntervals.Covers MatchesAt 652 653 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 652 1
  intro i
  fin_cases i
  intro h
  exact matches_652
lemma matches_653 : Matches 653 := by decide +kernel
lemma match_part653 : FiniteIntervals.Covers MatchesAt 653 654 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 653 1
  intro i
  fin_cases i
  intro h
  exact matches_653
lemma matches_654 : Matches 654 := by decide +kernel
lemma match_part654 : FiniteIntervals.Covers MatchesAt 654 655 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 654 1
  intro i
  fin_cases i
  intro h
  exact matches_654
lemma matches_655 : Matches 655 := by decide +kernel
lemma match_part655 : FiniteIntervals.Covers MatchesAt 655 656 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 655 1
  intro i
  fin_cases i
  intro h
  exact matches_655
lemma matches_656 : Matches 656 := by decide +kernel
lemma match_part656 : FiniteIntervals.Covers MatchesAt 656 657 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 656 1
  intro i
  fin_cases i
  intro h
  exact matches_656
lemma matches_657 : Matches 657 := by decide +kernel
lemma match_part657 : FiniteIntervals.Covers MatchesAt 657 658 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 657 1
  intro i
  fin_cases i
  intro h
  exact matches_657
lemma matches_658 : Matches 658 := by decide +kernel
lemma match_part658 : FiniteIntervals.Covers MatchesAt 658 659 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 658 1
  intro i
  fin_cases i
  intro h
  exact matches_658
lemma matches_659 : Matches 659 := by decide +kernel
lemma match_part659 : FiniteIntervals.Covers MatchesAt 659 660 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 659 1
  intro i
  fin_cases i
  intro h
  exact matches_659
lemma matches_interval54 : FiniteIntervals.Covers MatchesAt 648 660 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part648 (FiniteIntervals.merge match_part649 match_part650)) (FiniteIntervals.merge match_part651 (FiniteIntervals.merge match_part652 match_part653))) (FiniteIntervals.merge (FiniteIntervals.merge match_part654 (FiniteIntervals.merge match_part655 match_part656)) (FiniteIntervals.merge match_part657 (FiniteIntervals.merge match_part658 match_part659))))
#print axioms matches_interval54
end Erdos184Work.PureSevenActions

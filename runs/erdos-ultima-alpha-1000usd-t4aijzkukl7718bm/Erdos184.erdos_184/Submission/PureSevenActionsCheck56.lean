import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_672 : Matches 672 := by decide +kernel
lemma match_part672 : FiniteIntervals.Covers MatchesAt 672 673 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 672 1
  intro i
  fin_cases i
  intro h
  exact matches_672
lemma matches_673 : Matches 673 := by decide +kernel
lemma match_part673 : FiniteIntervals.Covers MatchesAt 673 674 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 673 1
  intro i
  fin_cases i
  intro h
  exact matches_673
lemma matches_674 : Matches 674 := by decide +kernel
lemma match_part674 : FiniteIntervals.Covers MatchesAt 674 675 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 674 1
  intro i
  fin_cases i
  intro h
  exact matches_674
lemma matches_675 : Matches 675 := by decide +kernel
lemma match_part675 : FiniteIntervals.Covers MatchesAt 675 676 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 675 1
  intro i
  fin_cases i
  intro h
  exact matches_675
lemma matches_676 : Matches 676 := by decide +kernel
lemma match_part676 : FiniteIntervals.Covers MatchesAt 676 677 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 676 1
  intro i
  fin_cases i
  intro h
  exact matches_676
lemma matches_677 : Matches 677 := by decide +kernel
lemma match_part677 : FiniteIntervals.Covers MatchesAt 677 678 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 677 1
  intro i
  fin_cases i
  intro h
  exact matches_677
lemma matches_678 : Matches 678 := by decide +kernel
lemma match_part678 : FiniteIntervals.Covers MatchesAt 678 679 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 678 1
  intro i
  fin_cases i
  intro h
  exact matches_678
lemma matches_679 : Matches 679 := by decide +kernel
lemma match_part679 : FiniteIntervals.Covers MatchesAt 679 680 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 679 1
  intro i
  fin_cases i
  intro h
  exact matches_679
lemma matches_680 : Matches 680 := by decide +kernel
lemma match_part680 : FiniteIntervals.Covers MatchesAt 680 681 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 680 1
  intro i
  fin_cases i
  intro h
  exact matches_680
lemma matches_681 : Matches 681 := by decide +kernel
lemma match_part681 : FiniteIntervals.Covers MatchesAt 681 682 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 681 1
  intro i
  fin_cases i
  intro h
  exact matches_681
lemma matches_682 : Matches 682 := by decide +kernel
lemma match_part682 : FiniteIntervals.Covers MatchesAt 682 683 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 682 1
  intro i
  fin_cases i
  intro h
  exact matches_682
lemma matches_683 : Matches 683 := by decide +kernel
lemma match_part683 : FiniteIntervals.Covers MatchesAt 683 684 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 683 1
  intro i
  fin_cases i
  intro h
  exact matches_683
lemma matches_interval56 : FiniteIntervals.Covers MatchesAt 672 684 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part672 (FiniteIntervals.merge match_part673 match_part674)) (FiniteIntervals.merge match_part675 (FiniteIntervals.merge match_part676 match_part677))) (FiniteIntervals.merge (FiniteIntervals.merge match_part678 (FiniteIntervals.merge match_part679 match_part680)) (FiniteIntervals.merge match_part681 (FiniteIntervals.merge match_part682 match_part683))))
#print axioms matches_interval56
end Erdos184Work.PureSevenActions

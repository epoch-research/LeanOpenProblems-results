import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_708 : Matches 708 := by decide +kernel
lemma match_part708 : FiniteIntervals.Covers MatchesAt 708 709 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 708 1
  intro i
  fin_cases i
  intro h
  exact matches_708
lemma matches_709 : Matches 709 := by decide +kernel
lemma match_part709 : FiniteIntervals.Covers MatchesAt 709 710 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 709 1
  intro i
  fin_cases i
  intro h
  exact matches_709
lemma matches_710 : Matches 710 := by decide +kernel
lemma match_part710 : FiniteIntervals.Covers MatchesAt 710 711 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 710 1
  intro i
  fin_cases i
  intro h
  exact matches_710
lemma matches_711 : Matches 711 := by decide +kernel
lemma match_part711 : FiniteIntervals.Covers MatchesAt 711 712 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 711 1
  intro i
  fin_cases i
  intro h
  exact matches_711
lemma matches_712 : Matches 712 := by decide +kernel
lemma match_part712 : FiniteIntervals.Covers MatchesAt 712 713 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 712 1
  intro i
  fin_cases i
  intro h
  exact matches_712
lemma matches_713 : Matches 713 := by decide +kernel
lemma match_part713 : FiniteIntervals.Covers MatchesAt 713 714 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 713 1
  intro i
  fin_cases i
  intro h
  exact matches_713
lemma matches_714 : Matches 714 := by decide +kernel
lemma match_part714 : FiniteIntervals.Covers MatchesAt 714 715 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 714 1
  intro i
  fin_cases i
  intro h
  exact matches_714
lemma matches_715 : Matches 715 := by decide +kernel
lemma match_part715 : FiniteIntervals.Covers MatchesAt 715 716 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 715 1
  intro i
  fin_cases i
  intro h
  exact matches_715
lemma matches_716 : Matches 716 := by decide +kernel
lemma match_part716 : FiniteIntervals.Covers MatchesAt 716 717 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 716 1
  intro i
  fin_cases i
  intro h
  exact matches_716
lemma matches_717 : Matches 717 := by decide +kernel
lemma match_part717 : FiniteIntervals.Covers MatchesAt 717 718 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 717 1
  intro i
  fin_cases i
  intro h
  exact matches_717
lemma matches_718 : Matches 718 := by decide +kernel
lemma match_part718 : FiniteIntervals.Covers MatchesAt 718 719 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 718 1
  intro i
  fin_cases i
  intro h
  exact matches_718
lemma matches_719 : Matches 719 := by decide +kernel
lemma match_part719 : FiniteIntervals.Covers MatchesAt 719 720 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 719 1
  intro i
  fin_cases i
  intro h
  exact matches_719
lemma matches_interval59 : FiniteIntervals.Covers MatchesAt 708 720 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part708 (FiniteIntervals.merge match_part709 match_part710)) (FiniteIntervals.merge match_part711 (FiniteIntervals.merge match_part712 match_part713))) (FiniteIntervals.merge (FiniteIntervals.merge match_part714 (FiniteIntervals.merge match_part715 match_part716)) (FiniteIntervals.merge match_part717 (FiniteIntervals.merge match_part718 match_part719))))
#print axioms matches_interval59
end Erdos184Work.PureSevenActions

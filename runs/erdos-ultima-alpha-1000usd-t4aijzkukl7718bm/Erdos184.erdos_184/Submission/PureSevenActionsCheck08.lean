import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_96 : Matches 96 := by decide +kernel
lemma match_part96 : FiniteIntervals.Covers MatchesAt 96 97 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 96 1
  intro i
  fin_cases i
  intro h
  exact matches_96
lemma matches_97 : Matches 97 := by decide +kernel
lemma match_part97 : FiniteIntervals.Covers MatchesAt 97 98 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 97 1
  intro i
  fin_cases i
  intro h
  exact matches_97
lemma matches_98 : Matches 98 := by decide +kernel
lemma match_part98 : FiniteIntervals.Covers MatchesAt 98 99 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 98 1
  intro i
  fin_cases i
  intro h
  exact matches_98
lemma matches_99 : Matches 99 := by decide +kernel
lemma match_part99 : FiniteIntervals.Covers MatchesAt 99 100 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 99 1
  intro i
  fin_cases i
  intro h
  exact matches_99
lemma matches_100 : Matches 100 := by decide +kernel
lemma match_part100 : FiniteIntervals.Covers MatchesAt 100 101 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 100 1
  intro i
  fin_cases i
  intro h
  exact matches_100
lemma matches_101 : Matches 101 := by decide +kernel
lemma match_part101 : FiniteIntervals.Covers MatchesAt 101 102 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 101 1
  intro i
  fin_cases i
  intro h
  exact matches_101
lemma matches_102 : Matches 102 := by decide +kernel
lemma match_part102 : FiniteIntervals.Covers MatchesAt 102 103 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 102 1
  intro i
  fin_cases i
  intro h
  exact matches_102
lemma matches_103 : Matches 103 := by decide +kernel
lemma match_part103 : FiniteIntervals.Covers MatchesAt 103 104 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 103 1
  intro i
  fin_cases i
  intro h
  exact matches_103
lemma matches_104 : Matches 104 := by decide +kernel
lemma match_part104 : FiniteIntervals.Covers MatchesAt 104 105 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 104 1
  intro i
  fin_cases i
  intro h
  exact matches_104
lemma matches_105 : Matches 105 := by decide +kernel
lemma match_part105 : FiniteIntervals.Covers MatchesAt 105 106 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 105 1
  intro i
  fin_cases i
  intro h
  exact matches_105
lemma matches_106 : Matches 106 := by decide +kernel
lemma match_part106 : FiniteIntervals.Covers MatchesAt 106 107 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 106 1
  intro i
  fin_cases i
  intro h
  exact matches_106
lemma matches_107 : Matches 107 := by decide +kernel
lemma match_part107 : FiniteIntervals.Covers MatchesAt 107 108 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 107 1
  intro i
  fin_cases i
  intro h
  exact matches_107
lemma matches_interval8 : FiniteIntervals.Covers MatchesAt 96 108 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part96 (FiniteIntervals.merge match_part97 match_part98)) (FiniteIntervals.merge match_part99 (FiniteIntervals.merge match_part100 match_part101))) (FiniteIntervals.merge (FiniteIntervals.merge match_part102 (FiniteIntervals.merge match_part103 match_part104)) (FiniteIntervals.merge match_part105 (FiniteIntervals.merge match_part106 match_part107))))
#print axioms matches_interval8
end Erdos184Work.PureSevenActions

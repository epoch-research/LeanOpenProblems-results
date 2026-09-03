import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_84 : Matches 84 := by decide +kernel
lemma match_part84 : FiniteIntervals.Covers MatchesAt 84 85 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 84 1
  intro i
  fin_cases i
  intro h
  exact matches_84
lemma matches_85 : Matches 85 := by decide +kernel
lemma match_part85 : FiniteIntervals.Covers MatchesAt 85 86 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 85 1
  intro i
  fin_cases i
  intro h
  exact matches_85
lemma matches_86 : Matches 86 := by decide +kernel
lemma match_part86 : FiniteIntervals.Covers MatchesAt 86 87 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 86 1
  intro i
  fin_cases i
  intro h
  exact matches_86
lemma matches_87 : Matches 87 := by decide +kernel
lemma match_part87 : FiniteIntervals.Covers MatchesAt 87 88 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 87 1
  intro i
  fin_cases i
  intro h
  exact matches_87
lemma matches_88 : Matches 88 := by decide +kernel
lemma match_part88 : FiniteIntervals.Covers MatchesAt 88 89 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 88 1
  intro i
  fin_cases i
  intro h
  exact matches_88
lemma matches_89 : Matches 89 := by decide +kernel
lemma match_part89 : FiniteIntervals.Covers MatchesAt 89 90 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 89 1
  intro i
  fin_cases i
  intro h
  exact matches_89
lemma matches_90 : Matches 90 := by decide +kernel
lemma match_part90 : FiniteIntervals.Covers MatchesAt 90 91 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 90 1
  intro i
  fin_cases i
  intro h
  exact matches_90
lemma matches_91 : Matches 91 := by decide +kernel
lemma match_part91 : FiniteIntervals.Covers MatchesAt 91 92 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 91 1
  intro i
  fin_cases i
  intro h
  exact matches_91
lemma matches_92 : Matches 92 := by decide +kernel
lemma match_part92 : FiniteIntervals.Covers MatchesAt 92 93 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 92 1
  intro i
  fin_cases i
  intro h
  exact matches_92
lemma matches_93 : Matches 93 := by decide +kernel
lemma match_part93 : FiniteIntervals.Covers MatchesAt 93 94 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 93 1
  intro i
  fin_cases i
  intro h
  exact matches_93
lemma matches_94 : Matches 94 := by decide +kernel
lemma match_part94 : FiniteIntervals.Covers MatchesAt 94 95 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 94 1
  intro i
  fin_cases i
  intro h
  exact matches_94
lemma matches_95 : Matches 95 := by decide +kernel
lemma match_part95 : FiniteIntervals.Covers MatchesAt 95 96 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 95 1
  intro i
  fin_cases i
  intro h
  exact matches_95
lemma matches_interval7 : FiniteIntervals.Covers MatchesAt 84 96 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part84 (FiniteIntervals.merge match_part85 match_part86)) (FiniteIntervals.merge match_part87 (FiniteIntervals.merge match_part88 match_part89))) (FiniteIntervals.merge (FiniteIntervals.merge match_part90 (FiniteIntervals.merge match_part91 match_part92)) (FiniteIntervals.merge match_part93 (FiniteIntervals.merge match_part94 match_part95))))
#print axioms matches_interval7
end Erdos184Work.PureSevenActions

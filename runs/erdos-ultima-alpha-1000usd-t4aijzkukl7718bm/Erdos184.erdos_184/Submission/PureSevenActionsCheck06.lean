import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_72 : Matches 72 := by decide +kernel
lemma match_part72 : FiniteIntervals.Covers MatchesAt 72 73 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 72 1
  intro i
  fin_cases i
  intro h
  exact matches_72
lemma matches_73 : Matches 73 := by decide +kernel
lemma match_part73 : FiniteIntervals.Covers MatchesAt 73 74 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 73 1
  intro i
  fin_cases i
  intro h
  exact matches_73
lemma matches_74 : Matches 74 := by decide +kernel
lemma match_part74 : FiniteIntervals.Covers MatchesAt 74 75 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 74 1
  intro i
  fin_cases i
  intro h
  exact matches_74
lemma matches_75 : Matches 75 := by decide +kernel
lemma match_part75 : FiniteIntervals.Covers MatchesAt 75 76 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 75 1
  intro i
  fin_cases i
  intro h
  exact matches_75
lemma matches_76 : Matches 76 := by decide +kernel
lemma match_part76 : FiniteIntervals.Covers MatchesAt 76 77 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 76 1
  intro i
  fin_cases i
  intro h
  exact matches_76
lemma matches_77 : Matches 77 := by decide +kernel
lemma match_part77 : FiniteIntervals.Covers MatchesAt 77 78 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 77 1
  intro i
  fin_cases i
  intro h
  exact matches_77
lemma matches_78 : Matches 78 := by decide +kernel
lemma match_part78 : FiniteIntervals.Covers MatchesAt 78 79 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 78 1
  intro i
  fin_cases i
  intro h
  exact matches_78
lemma matches_79 : Matches 79 := by decide +kernel
lemma match_part79 : FiniteIntervals.Covers MatchesAt 79 80 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 79 1
  intro i
  fin_cases i
  intro h
  exact matches_79
lemma matches_80 : Matches 80 := by decide +kernel
lemma match_part80 : FiniteIntervals.Covers MatchesAt 80 81 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 80 1
  intro i
  fin_cases i
  intro h
  exact matches_80
lemma matches_81 : Matches 81 := by decide +kernel
lemma match_part81 : FiniteIntervals.Covers MatchesAt 81 82 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 81 1
  intro i
  fin_cases i
  intro h
  exact matches_81
lemma matches_82 : Matches 82 := by decide +kernel
lemma match_part82 : FiniteIntervals.Covers MatchesAt 82 83 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 82 1
  intro i
  fin_cases i
  intro h
  exact matches_82
lemma matches_83 : Matches 83 := by decide +kernel
lemma match_part83 : FiniteIntervals.Covers MatchesAt 83 84 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 83 1
  intro i
  fin_cases i
  intro h
  exact matches_83
lemma matches_interval6 : FiniteIntervals.Covers MatchesAt 72 84 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part72 (FiniteIntervals.merge match_part73 match_part74)) (FiniteIntervals.merge match_part75 (FiniteIntervals.merge match_part76 match_part77))) (FiniteIntervals.merge (FiniteIntervals.merge match_part78 (FiniteIntervals.merge match_part79 match_part80)) (FiniteIntervals.merge match_part81 (FiniteIntervals.merge match_part82 match_part83))))
#print axioms matches_interval6
end Erdos184Work.PureSevenActions

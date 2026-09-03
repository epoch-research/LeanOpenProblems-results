import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_60 : Matches 60 := by decide +kernel
lemma match_part60 : FiniteIntervals.Covers MatchesAt 60 61 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 60 1
  intro i
  fin_cases i
  intro h
  exact matches_60
lemma matches_61 : Matches 61 := by decide +kernel
lemma match_part61 : FiniteIntervals.Covers MatchesAt 61 62 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 61 1
  intro i
  fin_cases i
  intro h
  exact matches_61
lemma matches_62 : Matches 62 := by decide +kernel
lemma match_part62 : FiniteIntervals.Covers MatchesAt 62 63 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 62 1
  intro i
  fin_cases i
  intro h
  exact matches_62
lemma matches_63 : Matches 63 := by decide +kernel
lemma match_part63 : FiniteIntervals.Covers MatchesAt 63 64 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 63 1
  intro i
  fin_cases i
  intro h
  exact matches_63
lemma matches_64 : Matches 64 := by decide +kernel
lemma match_part64 : FiniteIntervals.Covers MatchesAt 64 65 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 64 1
  intro i
  fin_cases i
  intro h
  exact matches_64
lemma matches_65 : Matches 65 := by decide +kernel
lemma match_part65 : FiniteIntervals.Covers MatchesAt 65 66 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 65 1
  intro i
  fin_cases i
  intro h
  exact matches_65
lemma matches_66 : Matches 66 := by decide +kernel
lemma match_part66 : FiniteIntervals.Covers MatchesAt 66 67 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 66 1
  intro i
  fin_cases i
  intro h
  exact matches_66
lemma matches_67 : Matches 67 := by decide +kernel
lemma match_part67 : FiniteIntervals.Covers MatchesAt 67 68 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 67 1
  intro i
  fin_cases i
  intro h
  exact matches_67
lemma matches_68 : Matches 68 := by decide +kernel
lemma match_part68 : FiniteIntervals.Covers MatchesAt 68 69 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 68 1
  intro i
  fin_cases i
  intro h
  exact matches_68
lemma matches_69 : Matches 69 := by decide +kernel
lemma match_part69 : FiniteIntervals.Covers MatchesAt 69 70 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 69 1
  intro i
  fin_cases i
  intro h
  exact matches_69
lemma matches_70 : Matches 70 := by decide +kernel
lemma match_part70 : FiniteIntervals.Covers MatchesAt 70 71 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 70 1
  intro i
  fin_cases i
  intro h
  exact matches_70
lemma matches_71 : Matches 71 := by decide +kernel
lemma match_part71 : FiniteIntervals.Covers MatchesAt 71 72 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 71 1
  intro i
  fin_cases i
  intro h
  exact matches_71
lemma matches_interval5 : FiniteIntervals.Covers MatchesAt 60 72 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part60 (FiniteIntervals.merge match_part61 match_part62)) (FiniteIntervals.merge match_part63 (FiniteIntervals.merge match_part64 match_part65))) (FiniteIntervals.merge (FiniteIntervals.merge match_part66 (FiniteIntervals.merge match_part67 match_part68)) (FiniteIntervals.merge match_part69 (FiniteIntervals.merge match_part70 match_part71))))
#print axioms matches_interval5
end Erdos184Work.PureSevenActions

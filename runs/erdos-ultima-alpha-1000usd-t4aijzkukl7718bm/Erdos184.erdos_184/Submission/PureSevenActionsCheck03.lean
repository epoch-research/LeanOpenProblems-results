import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_36 : Matches 36 := by decide +kernel
lemma match_part36 : FiniteIntervals.Covers MatchesAt 36 37 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 36 1
  intro i
  fin_cases i
  intro h
  exact matches_36
lemma matches_37 : Matches 37 := by decide +kernel
lemma match_part37 : FiniteIntervals.Covers MatchesAt 37 38 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 37 1
  intro i
  fin_cases i
  intro h
  exact matches_37
lemma matches_38 : Matches 38 := by decide +kernel
lemma match_part38 : FiniteIntervals.Covers MatchesAt 38 39 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 38 1
  intro i
  fin_cases i
  intro h
  exact matches_38
lemma matches_39 : Matches 39 := by decide +kernel
lemma match_part39 : FiniteIntervals.Covers MatchesAt 39 40 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 39 1
  intro i
  fin_cases i
  intro h
  exact matches_39
lemma matches_40 : Matches 40 := by decide +kernel
lemma match_part40 : FiniteIntervals.Covers MatchesAt 40 41 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 40 1
  intro i
  fin_cases i
  intro h
  exact matches_40
lemma matches_41 : Matches 41 := by decide +kernel
lemma match_part41 : FiniteIntervals.Covers MatchesAt 41 42 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 41 1
  intro i
  fin_cases i
  intro h
  exact matches_41
lemma matches_42 : Matches 42 := by decide +kernel
lemma match_part42 : FiniteIntervals.Covers MatchesAt 42 43 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 42 1
  intro i
  fin_cases i
  intro h
  exact matches_42
lemma matches_43 : Matches 43 := by decide +kernel
lemma match_part43 : FiniteIntervals.Covers MatchesAt 43 44 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 43 1
  intro i
  fin_cases i
  intro h
  exact matches_43
lemma matches_44 : Matches 44 := by decide +kernel
lemma match_part44 : FiniteIntervals.Covers MatchesAt 44 45 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 44 1
  intro i
  fin_cases i
  intro h
  exact matches_44
lemma matches_45 : Matches 45 := by decide +kernel
lemma match_part45 : FiniteIntervals.Covers MatchesAt 45 46 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 45 1
  intro i
  fin_cases i
  intro h
  exact matches_45
lemma matches_46 : Matches 46 := by decide +kernel
lemma match_part46 : FiniteIntervals.Covers MatchesAt 46 47 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 46 1
  intro i
  fin_cases i
  intro h
  exact matches_46
lemma matches_47 : Matches 47 := by decide +kernel
lemma match_part47 : FiniteIntervals.Covers MatchesAt 47 48 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 47 1
  intro i
  fin_cases i
  intro h
  exact matches_47
lemma matches_interval3 : FiniteIntervals.Covers MatchesAt 36 48 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part36 (FiniteIntervals.merge match_part37 match_part38)) (FiniteIntervals.merge match_part39 (FiniteIntervals.merge match_part40 match_part41))) (FiniteIntervals.merge (FiniteIntervals.merge match_part42 (FiniteIntervals.merge match_part43 match_part44)) (FiniteIntervals.merge match_part45 (FiniteIntervals.merge match_part46 match_part47))))
#print axioms matches_interval3
end Erdos184Work.PureSevenActions

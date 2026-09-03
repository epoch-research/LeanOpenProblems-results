import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_0 : Matches 0 := by decide +kernel
lemma match_part0 : FiniteIntervals.Covers MatchesAt 0 1 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 0 1
  intro i
  fin_cases i
  intro h
  exact matches_0
lemma matches_1 : Matches 1 := by decide +kernel
lemma match_part1 : FiniteIntervals.Covers MatchesAt 1 2 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 1 1
  intro i
  fin_cases i
  intro h
  exact matches_1
lemma matches_2 : Matches 2 := by decide +kernel
lemma match_part2 : FiniteIntervals.Covers MatchesAt 2 3 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 2 1
  intro i
  fin_cases i
  intro h
  exact matches_2
lemma matches_3 : Matches 3 := by decide +kernel
lemma match_part3 : FiniteIntervals.Covers MatchesAt 3 4 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 3 1
  intro i
  fin_cases i
  intro h
  exact matches_3
lemma matches_4 : Matches 4 := by decide +kernel
lemma match_part4 : FiniteIntervals.Covers MatchesAt 4 5 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 4 1
  intro i
  fin_cases i
  intro h
  exact matches_4
lemma matches_5 : Matches 5 := by decide +kernel
lemma match_part5 : FiniteIntervals.Covers MatchesAt 5 6 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 5 1
  intro i
  fin_cases i
  intro h
  exact matches_5
lemma matches_6 : Matches 6 := by decide +kernel
lemma match_part6 : FiniteIntervals.Covers MatchesAt 6 7 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 6 1
  intro i
  fin_cases i
  intro h
  exact matches_6
lemma matches_7 : Matches 7 := by decide +kernel
lemma match_part7 : FiniteIntervals.Covers MatchesAt 7 8 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 7 1
  intro i
  fin_cases i
  intro h
  exact matches_7
lemma matches_8 : Matches 8 := by decide +kernel
lemma match_part8 : FiniteIntervals.Covers MatchesAt 8 9 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 8 1
  intro i
  fin_cases i
  intro h
  exact matches_8
lemma matches_9 : Matches 9 := by decide +kernel
lemma match_part9 : FiniteIntervals.Covers MatchesAt 9 10 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 9 1
  intro i
  fin_cases i
  intro h
  exact matches_9
lemma matches_10 : Matches 10 := by decide +kernel
lemma match_part10 : FiniteIntervals.Covers MatchesAt 10 11 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 10 1
  intro i
  fin_cases i
  intro h
  exact matches_10
lemma matches_11 : Matches 11 := by decide +kernel
lemma match_part11 : FiniteIntervals.Covers MatchesAt 11 12 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 11 1
  intro i
  fin_cases i
  intro h
  exact matches_11
lemma matches_interval0 : FiniteIntervals.Covers MatchesAt 0 12 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part0 (FiniteIntervals.merge match_part1 match_part2)) (FiniteIntervals.merge match_part3 (FiniteIntervals.merge match_part4 match_part5))) (FiniteIntervals.merge (FiniteIntervals.merge match_part6 (FiniteIntervals.merge match_part7 match_part8)) (FiniteIntervals.merge match_part9 (FiniteIntervals.merge match_part10 match_part11))))
#print axioms matches_interval0
end Erdos184Work.PureSevenActions

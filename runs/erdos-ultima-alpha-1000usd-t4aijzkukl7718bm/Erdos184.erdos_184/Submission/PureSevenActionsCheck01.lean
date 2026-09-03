import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_12 : Matches 12 := by decide +kernel
lemma match_part12 : FiniteIntervals.Covers MatchesAt 12 13 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 12 1
  intro i
  fin_cases i
  intro h
  exact matches_12
lemma matches_13 : Matches 13 := by decide +kernel
lemma match_part13 : FiniteIntervals.Covers MatchesAt 13 14 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 13 1
  intro i
  fin_cases i
  intro h
  exact matches_13
lemma matches_14 : Matches 14 := by decide +kernel
lemma match_part14 : FiniteIntervals.Covers MatchesAt 14 15 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 14 1
  intro i
  fin_cases i
  intro h
  exact matches_14
lemma matches_15 : Matches 15 := by decide +kernel
lemma match_part15 : FiniteIntervals.Covers MatchesAt 15 16 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 15 1
  intro i
  fin_cases i
  intro h
  exact matches_15
lemma matches_16 : Matches 16 := by decide +kernel
lemma match_part16 : FiniteIntervals.Covers MatchesAt 16 17 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 16 1
  intro i
  fin_cases i
  intro h
  exact matches_16
lemma matches_17 : Matches 17 := by decide +kernel
lemma match_part17 : FiniteIntervals.Covers MatchesAt 17 18 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 17 1
  intro i
  fin_cases i
  intro h
  exact matches_17
lemma matches_18 : Matches 18 := by decide +kernel
lemma match_part18 : FiniteIntervals.Covers MatchesAt 18 19 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 18 1
  intro i
  fin_cases i
  intro h
  exact matches_18
lemma matches_19 : Matches 19 := by decide +kernel
lemma match_part19 : FiniteIntervals.Covers MatchesAt 19 20 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 19 1
  intro i
  fin_cases i
  intro h
  exact matches_19
lemma matches_20 : Matches 20 := by decide +kernel
lemma match_part20 : FiniteIntervals.Covers MatchesAt 20 21 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 20 1
  intro i
  fin_cases i
  intro h
  exact matches_20
lemma matches_21 : Matches 21 := by decide +kernel
lemma match_part21 : FiniteIntervals.Covers MatchesAt 21 22 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 21 1
  intro i
  fin_cases i
  intro h
  exact matches_21
lemma matches_22 : Matches 22 := by decide +kernel
lemma match_part22 : FiniteIntervals.Covers MatchesAt 22 23 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 22 1
  intro i
  fin_cases i
  intro h
  exact matches_22
lemma matches_23 : Matches 23 := by decide +kernel
lemma match_part23 : FiniteIntervals.Covers MatchesAt 23 24 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 23 1
  intro i
  fin_cases i
  intro h
  exact matches_23
lemma matches_interval1 : FiniteIntervals.Covers MatchesAt 12 24 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part12 (FiniteIntervals.merge match_part13 match_part14)) (FiniteIntervals.merge match_part15 (FiniteIntervals.merge match_part16 match_part17))) (FiniteIntervals.merge (FiniteIntervals.merge match_part18 (FiniteIntervals.merge match_part19 match_part20)) (FiniteIntervals.merge match_part21 (FiniteIntervals.merge match_part22 match_part23))))
#print axioms matches_interval1
end Erdos184Work.PureSevenActions

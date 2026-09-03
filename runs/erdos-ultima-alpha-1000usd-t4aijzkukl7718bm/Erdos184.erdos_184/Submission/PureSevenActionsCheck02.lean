import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_24 : Matches 24 := by decide +kernel
lemma match_part24 : FiniteIntervals.Covers MatchesAt 24 25 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 24 1
  intro i
  fin_cases i
  intro h
  exact matches_24
lemma matches_25 : Matches 25 := by decide +kernel
lemma match_part25 : FiniteIntervals.Covers MatchesAt 25 26 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 25 1
  intro i
  fin_cases i
  intro h
  exact matches_25
lemma matches_26 : Matches 26 := by decide +kernel
lemma match_part26 : FiniteIntervals.Covers MatchesAt 26 27 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 26 1
  intro i
  fin_cases i
  intro h
  exact matches_26
lemma matches_27 : Matches 27 := by decide +kernel
lemma match_part27 : FiniteIntervals.Covers MatchesAt 27 28 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 27 1
  intro i
  fin_cases i
  intro h
  exact matches_27
lemma matches_28 : Matches 28 := by decide +kernel
lemma match_part28 : FiniteIntervals.Covers MatchesAt 28 29 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 28 1
  intro i
  fin_cases i
  intro h
  exact matches_28
lemma matches_29 : Matches 29 := by decide +kernel
lemma match_part29 : FiniteIntervals.Covers MatchesAt 29 30 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 29 1
  intro i
  fin_cases i
  intro h
  exact matches_29
lemma matches_30 : Matches 30 := by decide +kernel
lemma match_part30 : FiniteIntervals.Covers MatchesAt 30 31 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 30 1
  intro i
  fin_cases i
  intro h
  exact matches_30
lemma matches_31 : Matches 31 := by decide +kernel
lemma match_part31 : FiniteIntervals.Covers MatchesAt 31 32 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 31 1
  intro i
  fin_cases i
  intro h
  exact matches_31
lemma matches_32 : Matches 32 := by decide +kernel
lemma match_part32 : FiniteIntervals.Covers MatchesAt 32 33 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 32 1
  intro i
  fin_cases i
  intro h
  exact matches_32
lemma matches_33 : Matches 33 := by decide +kernel
lemma match_part33 : FiniteIntervals.Covers MatchesAt 33 34 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 33 1
  intro i
  fin_cases i
  intro h
  exact matches_33
lemma matches_34 : Matches 34 := by decide +kernel
lemma match_part34 : FiniteIntervals.Covers MatchesAt 34 35 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 34 1
  intro i
  fin_cases i
  intro h
  exact matches_34
lemma matches_35 : Matches 35 := by decide +kernel
lemma match_part35 : FiniteIntervals.Covers MatchesAt 35 36 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 35 1
  intro i
  fin_cases i
  intro h
  exact matches_35
lemma matches_interval2 : FiniteIntervals.Covers MatchesAt 24 36 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part24 (FiniteIntervals.merge match_part25 match_part26)) (FiniteIntervals.merge match_part27 (FiniteIntervals.merge match_part28 match_part29))) (FiniteIntervals.merge (FiniteIntervals.merge match_part30 (FiniteIntervals.merge match_part31 match_part32)) (FiniteIntervals.merge match_part33 (FiniteIntervals.merge match_part34 match_part35))))
#print axioms matches_interval2
end Erdos184Work.PureSevenActions

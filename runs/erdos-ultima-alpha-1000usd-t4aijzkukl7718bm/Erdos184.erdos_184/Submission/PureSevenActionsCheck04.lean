import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_48 : Matches 48 := by decide +kernel
lemma match_part48 : FiniteIntervals.Covers MatchesAt 48 49 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 48 1
  intro i
  fin_cases i
  intro h
  exact matches_48
lemma matches_49 : Matches 49 := by decide +kernel
lemma match_part49 : FiniteIntervals.Covers MatchesAt 49 50 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 49 1
  intro i
  fin_cases i
  intro h
  exact matches_49
lemma matches_50 : Matches 50 := by decide +kernel
lemma match_part50 : FiniteIntervals.Covers MatchesAt 50 51 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 50 1
  intro i
  fin_cases i
  intro h
  exact matches_50
lemma matches_51 : Matches 51 := by decide +kernel
lemma match_part51 : FiniteIntervals.Covers MatchesAt 51 52 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 51 1
  intro i
  fin_cases i
  intro h
  exact matches_51
lemma matches_52 : Matches 52 := by decide +kernel
lemma match_part52 : FiniteIntervals.Covers MatchesAt 52 53 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 52 1
  intro i
  fin_cases i
  intro h
  exact matches_52
lemma matches_53 : Matches 53 := by decide +kernel
lemma match_part53 : FiniteIntervals.Covers MatchesAt 53 54 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 53 1
  intro i
  fin_cases i
  intro h
  exact matches_53
lemma matches_54 : Matches 54 := by decide +kernel
lemma match_part54 : FiniteIntervals.Covers MatchesAt 54 55 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 54 1
  intro i
  fin_cases i
  intro h
  exact matches_54
lemma matches_55 : Matches 55 := by decide +kernel
lemma match_part55 : FiniteIntervals.Covers MatchesAt 55 56 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 55 1
  intro i
  fin_cases i
  intro h
  exact matches_55
lemma matches_56 : Matches 56 := by decide +kernel
lemma match_part56 : FiniteIntervals.Covers MatchesAt 56 57 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 56 1
  intro i
  fin_cases i
  intro h
  exact matches_56
lemma matches_57 : Matches 57 := by decide +kernel
lemma match_part57 : FiniteIntervals.Covers MatchesAt 57 58 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 57 1
  intro i
  fin_cases i
  intro h
  exact matches_57
lemma matches_58 : Matches 58 := by decide +kernel
lemma match_part58 : FiniteIntervals.Covers MatchesAt 58 59 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 58 1
  intro i
  fin_cases i
  intro h
  exact matches_58
lemma matches_59 : Matches 59 := by decide +kernel
lemma match_part59 : FiniteIntervals.Covers MatchesAt 59 60 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 59 1
  intro i
  fin_cases i
  intro h
  exact matches_59
lemma matches_interval4 : FiniteIntervals.Covers MatchesAt 48 60 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part48 (FiniteIntervals.merge match_part49 match_part50)) (FiniteIntervals.merge match_part51 (FiniteIntervals.merge match_part52 match_part53))) (FiniteIntervals.merge (FiniteIntervals.merge match_part54 (FiniteIntervals.merge match_part55 match_part56)) (FiniteIntervals.merge match_part57 (FiniteIntervals.merge match_part58 match_part59))))
#print axioms matches_interval4
end Erdos184Work.PureSevenActions

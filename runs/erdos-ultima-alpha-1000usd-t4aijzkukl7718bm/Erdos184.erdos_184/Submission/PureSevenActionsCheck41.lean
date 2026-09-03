import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_492 : Matches 492 := by decide +kernel
lemma match_part492 : FiniteIntervals.Covers MatchesAt 492 493 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 492 1
  intro i
  fin_cases i
  intro h
  exact matches_492
lemma matches_493 : Matches 493 := by decide +kernel
lemma match_part493 : FiniteIntervals.Covers MatchesAt 493 494 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 493 1
  intro i
  fin_cases i
  intro h
  exact matches_493
lemma matches_494 : Matches 494 := by decide +kernel
lemma match_part494 : FiniteIntervals.Covers MatchesAt 494 495 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 494 1
  intro i
  fin_cases i
  intro h
  exact matches_494
lemma matches_495 : Matches 495 := by decide +kernel
lemma match_part495 : FiniteIntervals.Covers MatchesAt 495 496 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 495 1
  intro i
  fin_cases i
  intro h
  exact matches_495
lemma matches_496 : Matches 496 := by decide +kernel
lemma match_part496 : FiniteIntervals.Covers MatchesAt 496 497 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 496 1
  intro i
  fin_cases i
  intro h
  exact matches_496
lemma matches_497 : Matches 497 := by decide +kernel
lemma match_part497 : FiniteIntervals.Covers MatchesAt 497 498 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 497 1
  intro i
  fin_cases i
  intro h
  exact matches_497
lemma matches_498 : Matches 498 := by decide +kernel
lemma match_part498 : FiniteIntervals.Covers MatchesAt 498 499 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 498 1
  intro i
  fin_cases i
  intro h
  exact matches_498
lemma matches_499 : Matches 499 := by decide +kernel
lemma match_part499 : FiniteIntervals.Covers MatchesAt 499 500 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 499 1
  intro i
  fin_cases i
  intro h
  exact matches_499
lemma matches_500 : Matches 500 := by decide +kernel
lemma match_part500 : FiniteIntervals.Covers MatchesAt 500 501 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 500 1
  intro i
  fin_cases i
  intro h
  exact matches_500
lemma matches_501 : Matches 501 := by decide +kernel
lemma match_part501 : FiniteIntervals.Covers MatchesAt 501 502 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 501 1
  intro i
  fin_cases i
  intro h
  exact matches_501
lemma matches_502 : Matches 502 := by decide +kernel
lemma match_part502 : FiniteIntervals.Covers MatchesAt 502 503 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 502 1
  intro i
  fin_cases i
  intro h
  exact matches_502
lemma matches_503 : Matches 503 := by decide +kernel
lemma match_part503 : FiniteIntervals.Covers MatchesAt 503 504 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 503 1
  intro i
  fin_cases i
  intro h
  exact matches_503
lemma matches_interval41 : FiniteIntervals.Covers MatchesAt 492 504 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part492 (FiniteIntervals.merge match_part493 match_part494)) (FiniteIntervals.merge match_part495 (FiniteIntervals.merge match_part496 match_part497))) (FiniteIntervals.merge (FiniteIntervals.merge match_part498 (FiniteIntervals.merge match_part499 match_part500)) (FiniteIntervals.merge match_part501 (FiniteIntervals.merge match_part502 match_part503))))
#print axioms matches_interval41
end Erdos184Work.PureSevenActions

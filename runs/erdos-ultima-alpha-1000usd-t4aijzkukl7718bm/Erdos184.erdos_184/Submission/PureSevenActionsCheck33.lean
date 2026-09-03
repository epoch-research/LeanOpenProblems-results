import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_396 : Matches 396 := by decide +kernel
lemma match_part396 : FiniteIntervals.Covers MatchesAt 396 397 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 396 1
  intro i
  fin_cases i
  intro h
  exact matches_396
lemma matches_397 : Matches 397 := by decide +kernel
lemma match_part397 : FiniteIntervals.Covers MatchesAt 397 398 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 397 1
  intro i
  fin_cases i
  intro h
  exact matches_397
lemma matches_398 : Matches 398 := by decide +kernel
lemma match_part398 : FiniteIntervals.Covers MatchesAt 398 399 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 398 1
  intro i
  fin_cases i
  intro h
  exact matches_398
lemma matches_399 : Matches 399 := by decide +kernel
lemma match_part399 : FiniteIntervals.Covers MatchesAt 399 400 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 399 1
  intro i
  fin_cases i
  intro h
  exact matches_399
lemma matches_400 : Matches 400 := by decide +kernel
lemma match_part400 : FiniteIntervals.Covers MatchesAt 400 401 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 400 1
  intro i
  fin_cases i
  intro h
  exact matches_400
lemma matches_401 : Matches 401 := by decide +kernel
lemma match_part401 : FiniteIntervals.Covers MatchesAt 401 402 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 401 1
  intro i
  fin_cases i
  intro h
  exact matches_401
lemma matches_402 : Matches 402 := by decide +kernel
lemma match_part402 : FiniteIntervals.Covers MatchesAt 402 403 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 402 1
  intro i
  fin_cases i
  intro h
  exact matches_402
lemma matches_403 : Matches 403 := by decide +kernel
lemma match_part403 : FiniteIntervals.Covers MatchesAt 403 404 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 403 1
  intro i
  fin_cases i
  intro h
  exact matches_403
lemma matches_404 : Matches 404 := by decide +kernel
lemma match_part404 : FiniteIntervals.Covers MatchesAt 404 405 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 404 1
  intro i
  fin_cases i
  intro h
  exact matches_404
lemma matches_405 : Matches 405 := by decide +kernel
lemma match_part405 : FiniteIntervals.Covers MatchesAt 405 406 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 405 1
  intro i
  fin_cases i
  intro h
  exact matches_405
lemma matches_406 : Matches 406 := by decide +kernel
lemma match_part406 : FiniteIntervals.Covers MatchesAt 406 407 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 406 1
  intro i
  fin_cases i
  intro h
  exact matches_406
lemma matches_407 : Matches 407 := by decide +kernel
lemma match_part407 : FiniteIntervals.Covers MatchesAt 407 408 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 407 1
  intro i
  fin_cases i
  intro h
  exact matches_407
lemma matches_interval33 : FiniteIntervals.Covers MatchesAt 396 408 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part396 (FiniteIntervals.merge match_part397 match_part398)) (FiniteIntervals.merge match_part399 (FiniteIntervals.merge match_part400 match_part401))) (FiniteIntervals.merge (FiniteIntervals.merge match_part402 (FiniteIntervals.merge match_part403 match_part404)) (FiniteIntervals.merge match_part405 (FiniteIntervals.merge match_part406 match_part407))))
#print axioms matches_interval33
end Erdos184Work.PureSevenActions

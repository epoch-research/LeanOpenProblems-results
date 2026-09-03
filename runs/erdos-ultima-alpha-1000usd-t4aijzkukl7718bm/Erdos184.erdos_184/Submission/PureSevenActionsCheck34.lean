import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_408 : Matches 408 := by decide +kernel
lemma match_part408 : FiniteIntervals.Covers MatchesAt 408 409 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 408 1
  intro i
  fin_cases i
  intro h
  exact matches_408
lemma matches_409 : Matches 409 := by decide +kernel
lemma match_part409 : FiniteIntervals.Covers MatchesAt 409 410 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 409 1
  intro i
  fin_cases i
  intro h
  exact matches_409
lemma matches_410 : Matches 410 := by decide +kernel
lemma match_part410 : FiniteIntervals.Covers MatchesAt 410 411 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 410 1
  intro i
  fin_cases i
  intro h
  exact matches_410
lemma matches_411 : Matches 411 := by decide +kernel
lemma match_part411 : FiniteIntervals.Covers MatchesAt 411 412 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 411 1
  intro i
  fin_cases i
  intro h
  exact matches_411
lemma matches_412 : Matches 412 := by decide +kernel
lemma match_part412 : FiniteIntervals.Covers MatchesAt 412 413 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 412 1
  intro i
  fin_cases i
  intro h
  exact matches_412
lemma matches_413 : Matches 413 := by decide +kernel
lemma match_part413 : FiniteIntervals.Covers MatchesAt 413 414 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 413 1
  intro i
  fin_cases i
  intro h
  exact matches_413
lemma matches_414 : Matches 414 := by decide +kernel
lemma match_part414 : FiniteIntervals.Covers MatchesAt 414 415 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 414 1
  intro i
  fin_cases i
  intro h
  exact matches_414
lemma matches_415 : Matches 415 := by decide +kernel
lemma match_part415 : FiniteIntervals.Covers MatchesAt 415 416 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 415 1
  intro i
  fin_cases i
  intro h
  exact matches_415
lemma matches_416 : Matches 416 := by decide +kernel
lemma match_part416 : FiniteIntervals.Covers MatchesAt 416 417 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 416 1
  intro i
  fin_cases i
  intro h
  exact matches_416
lemma matches_417 : Matches 417 := by decide +kernel
lemma match_part417 : FiniteIntervals.Covers MatchesAt 417 418 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 417 1
  intro i
  fin_cases i
  intro h
  exact matches_417
lemma matches_418 : Matches 418 := by decide +kernel
lemma match_part418 : FiniteIntervals.Covers MatchesAt 418 419 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 418 1
  intro i
  fin_cases i
  intro h
  exact matches_418
lemma matches_419 : Matches 419 := by decide +kernel
lemma match_part419 : FiniteIntervals.Covers MatchesAt 419 420 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 419 1
  intro i
  fin_cases i
  intro h
  exact matches_419
lemma matches_interval34 : FiniteIntervals.Covers MatchesAt 408 420 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part408 (FiniteIntervals.merge match_part409 match_part410)) (FiniteIntervals.merge match_part411 (FiniteIntervals.merge match_part412 match_part413))) (FiniteIntervals.merge (FiniteIntervals.merge match_part414 (FiniteIntervals.merge match_part415 match_part416)) (FiniteIntervals.merge match_part417 (FiniteIntervals.merge match_part418 match_part419))))
#print axioms matches_interval34
end Erdos184Work.PureSevenActions

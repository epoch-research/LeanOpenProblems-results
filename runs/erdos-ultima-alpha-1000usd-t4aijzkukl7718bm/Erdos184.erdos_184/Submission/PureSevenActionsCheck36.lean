import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_432 : Matches 432 := by decide +kernel
lemma match_part432 : FiniteIntervals.Covers MatchesAt 432 433 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 432 1
  intro i
  fin_cases i
  intro h
  exact matches_432
lemma matches_433 : Matches 433 := by decide +kernel
lemma match_part433 : FiniteIntervals.Covers MatchesAt 433 434 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 433 1
  intro i
  fin_cases i
  intro h
  exact matches_433
lemma matches_434 : Matches 434 := by decide +kernel
lemma match_part434 : FiniteIntervals.Covers MatchesAt 434 435 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 434 1
  intro i
  fin_cases i
  intro h
  exact matches_434
lemma matches_435 : Matches 435 := by decide +kernel
lemma match_part435 : FiniteIntervals.Covers MatchesAt 435 436 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 435 1
  intro i
  fin_cases i
  intro h
  exact matches_435
lemma matches_436 : Matches 436 := by decide +kernel
lemma match_part436 : FiniteIntervals.Covers MatchesAt 436 437 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 436 1
  intro i
  fin_cases i
  intro h
  exact matches_436
lemma matches_437 : Matches 437 := by decide +kernel
lemma match_part437 : FiniteIntervals.Covers MatchesAt 437 438 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 437 1
  intro i
  fin_cases i
  intro h
  exact matches_437
lemma matches_438 : Matches 438 := by decide +kernel
lemma match_part438 : FiniteIntervals.Covers MatchesAt 438 439 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 438 1
  intro i
  fin_cases i
  intro h
  exact matches_438
lemma matches_439 : Matches 439 := by decide +kernel
lemma match_part439 : FiniteIntervals.Covers MatchesAt 439 440 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 439 1
  intro i
  fin_cases i
  intro h
  exact matches_439
lemma matches_440 : Matches 440 := by decide +kernel
lemma match_part440 : FiniteIntervals.Covers MatchesAt 440 441 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 440 1
  intro i
  fin_cases i
  intro h
  exact matches_440
lemma matches_441 : Matches 441 := by decide +kernel
lemma match_part441 : FiniteIntervals.Covers MatchesAt 441 442 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 441 1
  intro i
  fin_cases i
  intro h
  exact matches_441
lemma matches_442 : Matches 442 := by decide +kernel
lemma match_part442 : FiniteIntervals.Covers MatchesAt 442 443 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 442 1
  intro i
  fin_cases i
  intro h
  exact matches_442
lemma matches_443 : Matches 443 := by decide +kernel
lemma match_part443 : FiniteIntervals.Covers MatchesAt 443 444 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 443 1
  intro i
  fin_cases i
  intro h
  exact matches_443
lemma matches_interval36 : FiniteIntervals.Covers MatchesAt 432 444 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part432 (FiniteIntervals.merge match_part433 match_part434)) (FiniteIntervals.merge match_part435 (FiniteIntervals.merge match_part436 match_part437))) (FiniteIntervals.merge (FiniteIntervals.merge match_part438 (FiniteIntervals.merge match_part439 match_part440)) (FiniteIntervals.merge match_part441 (FiniteIntervals.merge match_part442 match_part443))))
#print axioms matches_interval36
end Erdos184Work.PureSevenActions

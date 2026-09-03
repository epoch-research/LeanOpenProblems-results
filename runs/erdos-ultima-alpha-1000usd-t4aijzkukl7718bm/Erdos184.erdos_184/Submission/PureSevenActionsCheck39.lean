import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_468 : Matches 468 := by decide +kernel
lemma match_part468 : FiniteIntervals.Covers MatchesAt 468 469 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 468 1
  intro i
  fin_cases i
  intro h
  exact matches_468
lemma matches_469 : Matches 469 := by decide +kernel
lemma match_part469 : FiniteIntervals.Covers MatchesAt 469 470 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 469 1
  intro i
  fin_cases i
  intro h
  exact matches_469
lemma matches_470 : Matches 470 := by decide +kernel
lemma match_part470 : FiniteIntervals.Covers MatchesAt 470 471 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 470 1
  intro i
  fin_cases i
  intro h
  exact matches_470
lemma matches_471 : Matches 471 := by decide +kernel
lemma match_part471 : FiniteIntervals.Covers MatchesAt 471 472 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 471 1
  intro i
  fin_cases i
  intro h
  exact matches_471
lemma matches_472 : Matches 472 := by decide +kernel
lemma match_part472 : FiniteIntervals.Covers MatchesAt 472 473 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 472 1
  intro i
  fin_cases i
  intro h
  exact matches_472
lemma matches_473 : Matches 473 := by decide +kernel
lemma match_part473 : FiniteIntervals.Covers MatchesAt 473 474 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 473 1
  intro i
  fin_cases i
  intro h
  exact matches_473
lemma matches_474 : Matches 474 := by decide +kernel
lemma match_part474 : FiniteIntervals.Covers MatchesAt 474 475 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 474 1
  intro i
  fin_cases i
  intro h
  exact matches_474
lemma matches_475 : Matches 475 := by decide +kernel
lemma match_part475 : FiniteIntervals.Covers MatchesAt 475 476 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 475 1
  intro i
  fin_cases i
  intro h
  exact matches_475
lemma matches_476 : Matches 476 := by decide +kernel
lemma match_part476 : FiniteIntervals.Covers MatchesAt 476 477 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 476 1
  intro i
  fin_cases i
  intro h
  exact matches_476
lemma matches_477 : Matches 477 := by decide +kernel
lemma match_part477 : FiniteIntervals.Covers MatchesAt 477 478 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 477 1
  intro i
  fin_cases i
  intro h
  exact matches_477
lemma matches_478 : Matches 478 := by decide +kernel
lemma match_part478 : FiniteIntervals.Covers MatchesAt 478 479 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 478 1
  intro i
  fin_cases i
  intro h
  exact matches_478
lemma matches_479 : Matches 479 := by decide +kernel
lemma match_part479 : FiniteIntervals.Covers MatchesAt 479 480 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 479 1
  intro i
  fin_cases i
  intro h
  exact matches_479
lemma matches_interval39 : FiniteIntervals.Covers MatchesAt 468 480 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part468 (FiniteIntervals.merge match_part469 match_part470)) (FiniteIntervals.merge match_part471 (FiniteIntervals.merge match_part472 match_part473))) (FiniteIntervals.merge (FiniteIntervals.merge match_part474 (FiniteIntervals.merge match_part475 match_part476)) (FiniteIntervals.merge match_part477 (FiniteIntervals.merge match_part478 match_part479))))
#print axioms matches_interval39
end Erdos184Work.PureSevenActions

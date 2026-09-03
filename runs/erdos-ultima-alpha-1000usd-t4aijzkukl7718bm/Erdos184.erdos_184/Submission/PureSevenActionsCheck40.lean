import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_480 : Matches 480 := by decide +kernel
lemma match_part480 : FiniteIntervals.Covers MatchesAt 480 481 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 480 1
  intro i
  fin_cases i
  intro h
  exact matches_480
lemma matches_481 : Matches 481 := by decide +kernel
lemma match_part481 : FiniteIntervals.Covers MatchesAt 481 482 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 481 1
  intro i
  fin_cases i
  intro h
  exact matches_481
lemma matches_482 : Matches 482 := by decide +kernel
lemma match_part482 : FiniteIntervals.Covers MatchesAt 482 483 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 482 1
  intro i
  fin_cases i
  intro h
  exact matches_482
lemma matches_483 : Matches 483 := by decide +kernel
lemma match_part483 : FiniteIntervals.Covers MatchesAt 483 484 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 483 1
  intro i
  fin_cases i
  intro h
  exact matches_483
lemma matches_484 : Matches 484 := by decide +kernel
lemma match_part484 : FiniteIntervals.Covers MatchesAt 484 485 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 484 1
  intro i
  fin_cases i
  intro h
  exact matches_484
lemma matches_485 : Matches 485 := by decide +kernel
lemma match_part485 : FiniteIntervals.Covers MatchesAt 485 486 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 485 1
  intro i
  fin_cases i
  intro h
  exact matches_485
lemma matches_486 : Matches 486 := by decide +kernel
lemma match_part486 : FiniteIntervals.Covers MatchesAt 486 487 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 486 1
  intro i
  fin_cases i
  intro h
  exact matches_486
lemma matches_487 : Matches 487 := by decide +kernel
lemma match_part487 : FiniteIntervals.Covers MatchesAt 487 488 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 487 1
  intro i
  fin_cases i
  intro h
  exact matches_487
lemma matches_488 : Matches 488 := by decide +kernel
lemma match_part488 : FiniteIntervals.Covers MatchesAt 488 489 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 488 1
  intro i
  fin_cases i
  intro h
  exact matches_488
lemma matches_489 : Matches 489 := by decide +kernel
lemma match_part489 : FiniteIntervals.Covers MatchesAt 489 490 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 489 1
  intro i
  fin_cases i
  intro h
  exact matches_489
lemma matches_490 : Matches 490 := by decide +kernel
lemma match_part490 : FiniteIntervals.Covers MatchesAt 490 491 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 490 1
  intro i
  fin_cases i
  intro h
  exact matches_490
lemma matches_491 : Matches 491 := by decide +kernel
lemma match_part491 : FiniteIntervals.Covers MatchesAt 491 492 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 491 1
  intro i
  fin_cases i
  intro h
  exact matches_491
lemma matches_interval40 : FiniteIntervals.Covers MatchesAt 480 492 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part480 (FiniteIntervals.merge match_part481 match_part482)) (FiniteIntervals.merge match_part483 (FiniteIntervals.merge match_part484 match_part485))) (FiniteIntervals.merge (FiniteIntervals.merge match_part486 (FiniteIntervals.merge match_part487 match_part488)) (FiniteIntervals.merge match_part489 (FiniteIntervals.merge match_part490 match_part491))))
#print axioms matches_interval40
end Erdos184Work.PureSevenActions

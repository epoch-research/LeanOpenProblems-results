import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_444 : Matches 444 := by decide +kernel
lemma match_part444 : FiniteIntervals.Covers MatchesAt 444 445 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 444 1
  intro i
  fin_cases i
  intro h
  exact matches_444
lemma matches_445 : Matches 445 := by decide +kernel
lemma match_part445 : FiniteIntervals.Covers MatchesAt 445 446 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 445 1
  intro i
  fin_cases i
  intro h
  exact matches_445
lemma matches_446 : Matches 446 := by decide +kernel
lemma match_part446 : FiniteIntervals.Covers MatchesAt 446 447 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 446 1
  intro i
  fin_cases i
  intro h
  exact matches_446
lemma matches_447 : Matches 447 := by decide +kernel
lemma match_part447 : FiniteIntervals.Covers MatchesAt 447 448 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 447 1
  intro i
  fin_cases i
  intro h
  exact matches_447
lemma matches_448 : Matches 448 := by decide +kernel
lemma match_part448 : FiniteIntervals.Covers MatchesAt 448 449 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 448 1
  intro i
  fin_cases i
  intro h
  exact matches_448
lemma matches_449 : Matches 449 := by decide +kernel
lemma match_part449 : FiniteIntervals.Covers MatchesAt 449 450 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 449 1
  intro i
  fin_cases i
  intro h
  exact matches_449
lemma matches_450 : Matches 450 := by decide +kernel
lemma match_part450 : FiniteIntervals.Covers MatchesAt 450 451 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 450 1
  intro i
  fin_cases i
  intro h
  exact matches_450
lemma matches_451 : Matches 451 := by decide +kernel
lemma match_part451 : FiniteIntervals.Covers MatchesAt 451 452 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 451 1
  intro i
  fin_cases i
  intro h
  exact matches_451
lemma matches_452 : Matches 452 := by decide +kernel
lemma match_part452 : FiniteIntervals.Covers MatchesAt 452 453 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 452 1
  intro i
  fin_cases i
  intro h
  exact matches_452
lemma matches_453 : Matches 453 := by decide +kernel
lemma match_part453 : FiniteIntervals.Covers MatchesAt 453 454 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 453 1
  intro i
  fin_cases i
  intro h
  exact matches_453
lemma matches_454 : Matches 454 := by decide +kernel
lemma match_part454 : FiniteIntervals.Covers MatchesAt 454 455 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 454 1
  intro i
  fin_cases i
  intro h
  exact matches_454
lemma matches_455 : Matches 455 := by decide +kernel
lemma match_part455 : FiniteIntervals.Covers MatchesAt 455 456 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 455 1
  intro i
  fin_cases i
  intro h
  exact matches_455
lemma matches_interval37 : FiniteIntervals.Covers MatchesAt 444 456 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part444 (FiniteIntervals.merge match_part445 match_part446)) (FiniteIntervals.merge match_part447 (FiniteIntervals.merge match_part448 match_part449))) (FiniteIntervals.merge (FiniteIntervals.merge match_part450 (FiniteIntervals.merge match_part451 match_part452)) (FiniteIntervals.merge match_part453 (FiniteIntervals.merge match_part454 match_part455))))
#print axioms matches_interval37
end Erdos184Work.PureSevenActions

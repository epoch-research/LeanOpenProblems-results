import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_516 : Matches 516 := by decide +kernel
lemma match_part516 : FiniteIntervals.Covers MatchesAt 516 517 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 516 1
  intro i
  fin_cases i
  intro h
  exact matches_516
lemma matches_517 : Matches 517 := by decide +kernel
lemma match_part517 : FiniteIntervals.Covers MatchesAt 517 518 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 517 1
  intro i
  fin_cases i
  intro h
  exact matches_517
lemma matches_518 : Matches 518 := by decide +kernel
lemma match_part518 : FiniteIntervals.Covers MatchesAt 518 519 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 518 1
  intro i
  fin_cases i
  intro h
  exact matches_518
lemma matches_519 : Matches 519 := by decide +kernel
lemma match_part519 : FiniteIntervals.Covers MatchesAt 519 520 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 519 1
  intro i
  fin_cases i
  intro h
  exact matches_519
lemma matches_520 : Matches 520 := by decide +kernel
lemma match_part520 : FiniteIntervals.Covers MatchesAt 520 521 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 520 1
  intro i
  fin_cases i
  intro h
  exact matches_520
lemma matches_521 : Matches 521 := by decide +kernel
lemma match_part521 : FiniteIntervals.Covers MatchesAt 521 522 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 521 1
  intro i
  fin_cases i
  intro h
  exact matches_521
lemma matches_522 : Matches 522 := by decide +kernel
lemma match_part522 : FiniteIntervals.Covers MatchesAt 522 523 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 522 1
  intro i
  fin_cases i
  intro h
  exact matches_522
lemma matches_523 : Matches 523 := by decide +kernel
lemma match_part523 : FiniteIntervals.Covers MatchesAt 523 524 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 523 1
  intro i
  fin_cases i
  intro h
  exact matches_523
lemma matches_524 : Matches 524 := by decide +kernel
lemma match_part524 : FiniteIntervals.Covers MatchesAt 524 525 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 524 1
  intro i
  fin_cases i
  intro h
  exact matches_524
lemma matches_525 : Matches 525 := by decide +kernel
lemma match_part525 : FiniteIntervals.Covers MatchesAt 525 526 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 525 1
  intro i
  fin_cases i
  intro h
  exact matches_525
lemma matches_526 : Matches 526 := by decide +kernel
lemma match_part526 : FiniteIntervals.Covers MatchesAt 526 527 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 526 1
  intro i
  fin_cases i
  intro h
  exact matches_526
lemma matches_527 : Matches 527 := by decide +kernel
lemma match_part527 : FiniteIntervals.Covers MatchesAt 527 528 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 527 1
  intro i
  fin_cases i
  intro h
  exact matches_527
lemma matches_interval43 : FiniteIntervals.Covers MatchesAt 516 528 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part516 (FiniteIntervals.merge match_part517 match_part518)) (FiniteIntervals.merge match_part519 (FiniteIntervals.merge match_part520 match_part521))) (FiniteIntervals.merge (FiniteIntervals.merge match_part522 (FiniteIntervals.merge match_part523 match_part524)) (FiniteIntervals.merge match_part525 (FiniteIntervals.merge match_part526 match_part527))))
#print axioms matches_interval43
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_528 : Matches 528 := by decide +kernel
lemma match_part528 : FiniteIntervals.Covers MatchesAt 528 529 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 528 1
  intro i
  fin_cases i
  intro h
  exact matches_528
lemma matches_529 : Matches 529 := by decide +kernel
lemma match_part529 : FiniteIntervals.Covers MatchesAt 529 530 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 529 1
  intro i
  fin_cases i
  intro h
  exact matches_529
lemma matches_530 : Matches 530 := by decide +kernel
lemma match_part530 : FiniteIntervals.Covers MatchesAt 530 531 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 530 1
  intro i
  fin_cases i
  intro h
  exact matches_530
lemma matches_531 : Matches 531 := by decide +kernel
lemma match_part531 : FiniteIntervals.Covers MatchesAt 531 532 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 531 1
  intro i
  fin_cases i
  intro h
  exact matches_531
lemma matches_532 : Matches 532 := by decide +kernel
lemma match_part532 : FiniteIntervals.Covers MatchesAt 532 533 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 532 1
  intro i
  fin_cases i
  intro h
  exact matches_532
lemma matches_533 : Matches 533 := by decide +kernel
lemma match_part533 : FiniteIntervals.Covers MatchesAt 533 534 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 533 1
  intro i
  fin_cases i
  intro h
  exact matches_533
lemma matches_534 : Matches 534 := by decide +kernel
lemma match_part534 : FiniteIntervals.Covers MatchesAt 534 535 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 534 1
  intro i
  fin_cases i
  intro h
  exact matches_534
lemma matches_535 : Matches 535 := by decide +kernel
lemma match_part535 : FiniteIntervals.Covers MatchesAt 535 536 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 535 1
  intro i
  fin_cases i
  intro h
  exact matches_535
lemma matches_536 : Matches 536 := by decide +kernel
lemma match_part536 : FiniteIntervals.Covers MatchesAt 536 537 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 536 1
  intro i
  fin_cases i
  intro h
  exact matches_536
lemma matches_537 : Matches 537 := by decide +kernel
lemma match_part537 : FiniteIntervals.Covers MatchesAt 537 538 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 537 1
  intro i
  fin_cases i
  intro h
  exact matches_537
lemma matches_538 : Matches 538 := by decide +kernel
lemma match_part538 : FiniteIntervals.Covers MatchesAt 538 539 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 538 1
  intro i
  fin_cases i
  intro h
  exact matches_538
lemma matches_539 : Matches 539 := by decide +kernel
lemma match_part539 : FiniteIntervals.Covers MatchesAt 539 540 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 539 1
  intro i
  fin_cases i
  intro h
  exact matches_539
lemma matches_interval44 : FiniteIntervals.Covers MatchesAt 528 540 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part528 (FiniteIntervals.merge match_part529 match_part530)) (FiniteIntervals.merge match_part531 (FiniteIntervals.merge match_part532 match_part533))) (FiniteIntervals.merge (FiniteIntervals.merge match_part534 (FiniteIntervals.merge match_part535 match_part536)) (FiniteIntervals.merge match_part537 (FiniteIntervals.merge match_part538 match_part539))))
#print axioms matches_interval44
end Erdos184Work.PureSevenActions

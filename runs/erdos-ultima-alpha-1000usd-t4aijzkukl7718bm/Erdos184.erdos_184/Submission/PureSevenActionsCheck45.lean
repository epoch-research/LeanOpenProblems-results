import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_540 : Matches 540 := by decide +kernel
lemma match_part540 : FiniteIntervals.Covers MatchesAt 540 541 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 540 1
  intro i
  fin_cases i
  intro h
  exact matches_540
lemma matches_541 : Matches 541 := by decide +kernel
lemma match_part541 : FiniteIntervals.Covers MatchesAt 541 542 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 541 1
  intro i
  fin_cases i
  intro h
  exact matches_541
lemma matches_542 : Matches 542 := by decide +kernel
lemma match_part542 : FiniteIntervals.Covers MatchesAt 542 543 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 542 1
  intro i
  fin_cases i
  intro h
  exact matches_542
lemma matches_543 : Matches 543 := by decide +kernel
lemma match_part543 : FiniteIntervals.Covers MatchesAt 543 544 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 543 1
  intro i
  fin_cases i
  intro h
  exact matches_543
lemma matches_544 : Matches 544 := by decide +kernel
lemma match_part544 : FiniteIntervals.Covers MatchesAt 544 545 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 544 1
  intro i
  fin_cases i
  intro h
  exact matches_544
lemma matches_545 : Matches 545 := by decide +kernel
lemma match_part545 : FiniteIntervals.Covers MatchesAt 545 546 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 545 1
  intro i
  fin_cases i
  intro h
  exact matches_545
lemma matches_546 : Matches 546 := by decide +kernel
lemma match_part546 : FiniteIntervals.Covers MatchesAt 546 547 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 546 1
  intro i
  fin_cases i
  intro h
  exact matches_546
lemma matches_547 : Matches 547 := by decide +kernel
lemma match_part547 : FiniteIntervals.Covers MatchesAt 547 548 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 547 1
  intro i
  fin_cases i
  intro h
  exact matches_547
lemma matches_548 : Matches 548 := by decide +kernel
lemma match_part548 : FiniteIntervals.Covers MatchesAt 548 549 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 548 1
  intro i
  fin_cases i
  intro h
  exact matches_548
lemma matches_549 : Matches 549 := by decide +kernel
lemma match_part549 : FiniteIntervals.Covers MatchesAt 549 550 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 549 1
  intro i
  fin_cases i
  intro h
  exact matches_549
lemma matches_550 : Matches 550 := by decide +kernel
lemma match_part550 : FiniteIntervals.Covers MatchesAt 550 551 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 550 1
  intro i
  fin_cases i
  intro h
  exact matches_550
lemma matches_551 : Matches 551 := by decide +kernel
lemma match_part551 : FiniteIntervals.Covers MatchesAt 551 552 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 551 1
  intro i
  fin_cases i
  intro h
  exact matches_551
lemma matches_interval45 : FiniteIntervals.Covers MatchesAt 540 552 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part540 (FiniteIntervals.merge match_part541 match_part542)) (FiniteIntervals.merge match_part543 (FiniteIntervals.merge match_part544 match_part545))) (FiniteIntervals.merge (FiniteIntervals.merge match_part546 (FiniteIntervals.merge match_part547 match_part548)) (FiniteIntervals.merge match_part549 (FiniteIntervals.merge match_part550 match_part551))))
#print axioms matches_interval45
end Erdos184Work.PureSevenActions

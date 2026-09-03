import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_576 : Matches 576 := by decide +kernel
lemma match_part576 : FiniteIntervals.Covers MatchesAt 576 577 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 576 1
  intro i
  fin_cases i
  intro h
  exact matches_576
lemma matches_577 : Matches 577 := by decide +kernel
lemma match_part577 : FiniteIntervals.Covers MatchesAt 577 578 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 577 1
  intro i
  fin_cases i
  intro h
  exact matches_577
lemma matches_578 : Matches 578 := by decide +kernel
lemma match_part578 : FiniteIntervals.Covers MatchesAt 578 579 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 578 1
  intro i
  fin_cases i
  intro h
  exact matches_578
lemma matches_579 : Matches 579 := by decide +kernel
lemma match_part579 : FiniteIntervals.Covers MatchesAt 579 580 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 579 1
  intro i
  fin_cases i
  intro h
  exact matches_579
lemma matches_580 : Matches 580 := by decide +kernel
lemma match_part580 : FiniteIntervals.Covers MatchesAt 580 581 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 580 1
  intro i
  fin_cases i
  intro h
  exact matches_580
lemma matches_581 : Matches 581 := by decide +kernel
lemma match_part581 : FiniteIntervals.Covers MatchesAt 581 582 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 581 1
  intro i
  fin_cases i
  intro h
  exact matches_581
lemma matches_582 : Matches 582 := by decide +kernel
lemma match_part582 : FiniteIntervals.Covers MatchesAt 582 583 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 582 1
  intro i
  fin_cases i
  intro h
  exact matches_582
lemma matches_583 : Matches 583 := by decide +kernel
lemma match_part583 : FiniteIntervals.Covers MatchesAt 583 584 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 583 1
  intro i
  fin_cases i
  intro h
  exact matches_583
lemma matches_584 : Matches 584 := by decide +kernel
lemma match_part584 : FiniteIntervals.Covers MatchesAt 584 585 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 584 1
  intro i
  fin_cases i
  intro h
  exact matches_584
lemma matches_585 : Matches 585 := by decide +kernel
lemma match_part585 : FiniteIntervals.Covers MatchesAt 585 586 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 585 1
  intro i
  fin_cases i
  intro h
  exact matches_585
lemma matches_586 : Matches 586 := by decide +kernel
lemma match_part586 : FiniteIntervals.Covers MatchesAt 586 587 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 586 1
  intro i
  fin_cases i
  intro h
  exact matches_586
lemma matches_587 : Matches 587 := by decide +kernel
lemma match_part587 : FiniteIntervals.Covers MatchesAt 587 588 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 587 1
  intro i
  fin_cases i
  intro h
  exact matches_587
lemma matches_interval48 : FiniteIntervals.Covers MatchesAt 576 588 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part576 (FiniteIntervals.merge match_part577 match_part578)) (FiniteIntervals.merge match_part579 (FiniteIntervals.merge match_part580 match_part581))) (FiniteIntervals.merge (FiniteIntervals.merge match_part582 (FiniteIntervals.merge match_part583 match_part584)) (FiniteIntervals.merge match_part585 (FiniteIntervals.merge match_part586 match_part587))))
#print axioms matches_interval48
end Erdos184Work.PureSevenActions

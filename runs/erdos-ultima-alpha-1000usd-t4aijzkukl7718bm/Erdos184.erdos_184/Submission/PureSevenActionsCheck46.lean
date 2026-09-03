import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_552 : Matches 552 := by decide +kernel
lemma match_part552 : FiniteIntervals.Covers MatchesAt 552 553 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 552 1
  intro i
  fin_cases i
  intro h
  exact matches_552
lemma matches_553 : Matches 553 := by decide +kernel
lemma match_part553 : FiniteIntervals.Covers MatchesAt 553 554 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 553 1
  intro i
  fin_cases i
  intro h
  exact matches_553
lemma matches_554 : Matches 554 := by decide +kernel
lemma match_part554 : FiniteIntervals.Covers MatchesAt 554 555 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 554 1
  intro i
  fin_cases i
  intro h
  exact matches_554
lemma matches_555 : Matches 555 := by decide +kernel
lemma match_part555 : FiniteIntervals.Covers MatchesAt 555 556 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 555 1
  intro i
  fin_cases i
  intro h
  exact matches_555
lemma matches_556 : Matches 556 := by decide +kernel
lemma match_part556 : FiniteIntervals.Covers MatchesAt 556 557 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 556 1
  intro i
  fin_cases i
  intro h
  exact matches_556
lemma matches_557 : Matches 557 := by decide +kernel
lemma match_part557 : FiniteIntervals.Covers MatchesAt 557 558 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 557 1
  intro i
  fin_cases i
  intro h
  exact matches_557
lemma matches_558 : Matches 558 := by decide +kernel
lemma match_part558 : FiniteIntervals.Covers MatchesAt 558 559 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 558 1
  intro i
  fin_cases i
  intro h
  exact matches_558
lemma matches_559 : Matches 559 := by decide +kernel
lemma match_part559 : FiniteIntervals.Covers MatchesAt 559 560 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 559 1
  intro i
  fin_cases i
  intro h
  exact matches_559
lemma matches_560 : Matches 560 := by decide +kernel
lemma match_part560 : FiniteIntervals.Covers MatchesAt 560 561 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 560 1
  intro i
  fin_cases i
  intro h
  exact matches_560
lemma matches_561 : Matches 561 := by decide +kernel
lemma match_part561 : FiniteIntervals.Covers MatchesAt 561 562 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 561 1
  intro i
  fin_cases i
  intro h
  exact matches_561
lemma matches_562 : Matches 562 := by decide +kernel
lemma match_part562 : FiniteIntervals.Covers MatchesAt 562 563 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 562 1
  intro i
  fin_cases i
  intro h
  exact matches_562
lemma matches_563 : Matches 563 := by decide +kernel
lemma match_part563 : FiniteIntervals.Covers MatchesAt 563 564 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 563 1
  intro i
  fin_cases i
  intro h
  exact matches_563
lemma matches_interval46 : FiniteIntervals.Covers MatchesAt 552 564 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part552 (FiniteIntervals.merge match_part553 match_part554)) (FiniteIntervals.merge match_part555 (FiniteIntervals.merge match_part556 match_part557))) (FiniteIntervals.merge (FiniteIntervals.merge match_part558 (FiniteIntervals.merge match_part559 match_part560)) (FiniteIntervals.merge match_part561 (FiniteIntervals.merge match_part562 match_part563))))
#print axioms matches_interval46
end Erdos184Work.PureSevenActions

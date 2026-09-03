import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_456 : Matches 456 := by decide +kernel
lemma match_part456 : FiniteIntervals.Covers MatchesAt 456 457 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 456 1
  intro i
  fin_cases i
  intro h
  exact matches_456
lemma matches_457 : Matches 457 := by decide +kernel
lemma match_part457 : FiniteIntervals.Covers MatchesAt 457 458 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 457 1
  intro i
  fin_cases i
  intro h
  exact matches_457
lemma matches_458 : Matches 458 := by decide +kernel
lemma match_part458 : FiniteIntervals.Covers MatchesAt 458 459 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 458 1
  intro i
  fin_cases i
  intro h
  exact matches_458
lemma matches_459 : Matches 459 := by decide +kernel
lemma match_part459 : FiniteIntervals.Covers MatchesAt 459 460 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 459 1
  intro i
  fin_cases i
  intro h
  exact matches_459
lemma matches_460 : Matches 460 := by decide +kernel
lemma match_part460 : FiniteIntervals.Covers MatchesAt 460 461 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 460 1
  intro i
  fin_cases i
  intro h
  exact matches_460
lemma matches_461 : Matches 461 := by decide +kernel
lemma match_part461 : FiniteIntervals.Covers MatchesAt 461 462 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 461 1
  intro i
  fin_cases i
  intro h
  exact matches_461
lemma matches_462 : Matches 462 := by decide +kernel
lemma match_part462 : FiniteIntervals.Covers MatchesAt 462 463 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 462 1
  intro i
  fin_cases i
  intro h
  exact matches_462
lemma matches_463 : Matches 463 := by decide +kernel
lemma match_part463 : FiniteIntervals.Covers MatchesAt 463 464 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 463 1
  intro i
  fin_cases i
  intro h
  exact matches_463
lemma matches_464 : Matches 464 := by decide +kernel
lemma match_part464 : FiniteIntervals.Covers MatchesAt 464 465 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 464 1
  intro i
  fin_cases i
  intro h
  exact matches_464
lemma matches_465 : Matches 465 := by decide +kernel
lemma match_part465 : FiniteIntervals.Covers MatchesAt 465 466 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 465 1
  intro i
  fin_cases i
  intro h
  exact matches_465
lemma matches_466 : Matches 466 := by decide +kernel
lemma match_part466 : FiniteIntervals.Covers MatchesAt 466 467 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 466 1
  intro i
  fin_cases i
  intro h
  exact matches_466
lemma matches_467 : Matches 467 := by decide +kernel
lemma match_part467 : FiniteIntervals.Covers MatchesAt 467 468 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 467 1
  intro i
  fin_cases i
  intro h
  exact matches_467
lemma matches_interval38 : FiniteIntervals.Covers MatchesAt 456 468 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part456 (FiniteIntervals.merge match_part457 match_part458)) (FiniteIntervals.merge match_part459 (FiniteIntervals.merge match_part460 match_part461))) (FiniteIntervals.merge (FiniteIntervals.merge match_part462 (FiniteIntervals.merge match_part463 match_part464)) (FiniteIntervals.merge match_part465 (FiniteIntervals.merge match_part466 match_part467))))
#print axioms matches_interval38
end Erdos184Work.PureSevenActions

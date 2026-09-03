import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_420 : Matches 420 := by decide +kernel
lemma match_part420 : FiniteIntervals.Covers MatchesAt 420 421 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 420 1
  intro i
  fin_cases i
  intro h
  exact matches_420
lemma matches_421 : Matches 421 := by decide +kernel
lemma match_part421 : FiniteIntervals.Covers MatchesAt 421 422 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 421 1
  intro i
  fin_cases i
  intro h
  exact matches_421
lemma matches_422 : Matches 422 := by decide +kernel
lemma match_part422 : FiniteIntervals.Covers MatchesAt 422 423 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 422 1
  intro i
  fin_cases i
  intro h
  exact matches_422
lemma matches_423 : Matches 423 := by decide +kernel
lemma match_part423 : FiniteIntervals.Covers MatchesAt 423 424 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 423 1
  intro i
  fin_cases i
  intro h
  exact matches_423
lemma matches_424 : Matches 424 := by decide +kernel
lemma match_part424 : FiniteIntervals.Covers MatchesAt 424 425 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 424 1
  intro i
  fin_cases i
  intro h
  exact matches_424
lemma matches_425 : Matches 425 := by decide +kernel
lemma match_part425 : FiniteIntervals.Covers MatchesAt 425 426 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 425 1
  intro i
  fin_cases i
  intro h
  exact matches_425
lemma matches_426 : Matches 426 := by decide +kernel
lemma match_part426 : FiniteIntervals.Covers MatchesAt 426 427 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 426 1
  intro i
  fin_cases i
  intro h
  exact matches_426
lemma matches_427 : Matches 427 := by decide +kernel
lemma match_part427 : FiniteIntervals.Covers MatchesAt 427 428 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 427 1
  intro i
  fin_cases i
  intro h
  exact matches_427
lemma matches_428 : Matches 428 := by decide +kernel
lemma match_part428 : FiniteIntervals.Covers MatchesAt 428 429 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 428 1
  intro i
  fin_cases i
  intro h
  exact matches_428
lemma matches_429 : Matches 429 := by decide +kernel
lemma match_part429 : FiniteIntervals.Covers MatchesAt 429 430 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 429 1
  intro i
  fin_cases i
  intro h
  exact matches_429
lemma matches_430 : Matches 430 := by decide +kernel
lemma match_part430 : FiniteIntervals.Covers MatchesAt 430 431 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 430 1
  intro i
  fin_cases i
  intro h
  exact matches_430
lemma matches_431 : Matches 431 := by decide +kernel
lemma match_part431 : FiniteIntervals.Covers MatchesAt 431 432 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 431 1
  intro i
  fin_cases i
  intro h
  exact matches_431
lemma matches_interval35 : FiniteIntervals.Covers MatchesAt 420 432 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part420 (FiniteIntervals.merge match_part421 match_part422)) (FiniteIntervals.merge match_part423 (FiniteIntervals.merge match_part424 match_part425))) (FiniteIntervals.merge (FiniteIntervals.merge match_part426 (FiniteIntervals.merge match_part427 match_part428)) (FiniteIntervals.merge match_part429 (FiniteIntervals.merge match_part430 match_part431))))
#print axioms matches_interval35
end Erdos184Work.PureSevenActions

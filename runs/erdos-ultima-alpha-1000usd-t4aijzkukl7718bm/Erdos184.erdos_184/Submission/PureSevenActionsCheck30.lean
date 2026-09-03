import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_360 : Matches 360 := by decide +kernel
lemma match_part360 : FiniteIntervals.Covers MatchesAt 360 361 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 360 1
  intro i
  fin_cases i
  intro h
  exact matches_360
lemma matches_361 : Matches 361 := by decide +kernel
lemma match_part361 : FiniteIntervals.Covers MatchesAt 361 362 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 361 1
  intro i
  fin_cases i
  intro h
  exact matches_361
lemma matches_362 : Matches 362 := by decide +kernel
lemma match_part362 : FiniteIntervals.Covers MatchesAt 362 363 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 362 1
  intro i
  fin_cases i
  intro h
  exact matches_362
lemma matches_363 : Matches 363 := by decide +kernel
lemma match_part363 : FiniteIntervals.Covers MatchesAt 363 364 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 363 1
  intro i
  fin_cases i
  intro h
  exact matches_363
lemma matches_364 : Matches 364 := by decide +kernel
lemma match_part364 : FiniteIntervals.Covers MatchesAt 364 365 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 364 1
  intro i
  fin_cases i
  intro h
  exact matches_364
lemma matches_365 : Matches 365 := by decide +kernel
lemma match_part365 : FiniteIntervals.Covers MatchesAt 365 366 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 365 1
  intro i
  fin_cases i
  intro h
  exact matches_365
lemma matches_366 : Matches 366 := by decide +kernel
lemma match_part366 : FiniteIntervals.Covers MatchesAt 366 367 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 366 1
  intro i
  fin_cases i
  intro h
  exact matches_366
lemma matches_367 : Matches 367 := by decide +kernel
lemma match_part367 : FiniteIntervals.Covers MatchesAt 367 368 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 367 1
  intro i
  fin_cases i
  intro h
  exact matches_367
lemma matches_368 : Matches 368 := by decide +kernel
lemma match_part368 : FiniteIntervals.Covers MatchesAt 368 369 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 368 1
  intro i
  fin_cases i
  intro h
  exact matches_368
lemma matches_369 : Matches 369 := by decide +kernel
lemma match_part369 : FiniteIntervals.Covers MatchesAt 369 370 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 369 1
  intro i
  fin_cases i
  intro h
  exact matches_369
lemma matches_370 : Matches 370 := by decide +kernel
lemma match_part370 : FiniteIntervals.Covers MatchesAt 370 371 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 370 1
  intro i
  fin_cases i
  intro h
  exact matches_370
lemma matches_371 : Matches 371 := by decide +kernel
lemma match_part371 : FiniteIntervals.Covers MatchesAt 371 372 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 371 1
  intro i
  fin_cases i
  intro h
  exact matches_371
lemma matches_interval30 : FiniteIntervals.Covers MatchesAt 360 372 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part360 (FiniteIntervals.merge match_part361 match_part362)) (FiniteIntervals.merge match_part363 (FiniteIntervals.merge match_part364 match_part365))) (FiniteIntervals.merge (FiniteIntervals.merge match_part366 (FiniteIntervals.merge match_part367 match_part368)) (FiniteIntervals.merge match_part369 (FiniteIntervals.merge match_part370 match_part371))))
#print axioms matches_interval30
end Erdos184Work.PureSevenActions

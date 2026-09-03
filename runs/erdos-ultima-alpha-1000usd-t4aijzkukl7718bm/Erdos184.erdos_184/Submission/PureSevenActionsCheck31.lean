import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_372 : Matches 372 := by decide +kernel
lemma match_part372 : FiniteIntervals.Covers MatchesAt 372 373 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 372 1
  intro i
  fin_cases i
  intro h
  exact matches_372
lemma matches_373 : Matches 373 := by decide +kernel
lemma match_part373 : FiniteIntervals.Covers MatchesAt 373 374 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 373 1
  intro i
  fin_cases i
  intro h
  exact matches_373
lemma matches_374 : Matches 374 := by decide +kernel
lemma match_part374 : FiniteIntervals.Covers MatchesAt 374 375 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 374 1
  intro i
  fin_cases i
  intro h
  exact matches_374
lemma matches_375 : Matches 375 := by decide +kernel
lemma match_part375 : FiniteIntervals.Covers MatchesAt 375 376 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 375 1
  intro i
  fin_cases i
  intro h
  exact matches_375
lemma matches_376 : Matches 376 := by decide +kernel
lemma match_part376 : FiniteIntervals.Covers MatchesAt 376 377 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 376 1
  intro i
  fin_cases i
  intro h
  exact matches_376
lemma matches_377 : Matches 377 := by decide +kernel
lemma match_part377 : FiniteIntervals.Covers MatchesAt 377 378 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 377 1
  intro i
  fin_cases i
  intro h
  exact matches_377
lemma matches_378 : Matches 378 := by decide +kernel
lemma match_part378 : FiniteIntervals.Covers MatchesAt 378 379 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 378 1
  intro i
  fin_cases i
  intro h
  exact matches_378
lemma matches_379 : Matches 379 := by decide +kernel
lemma match_part379 : FiniteIntervals.Covers MatchesAt 379 380 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 379 1
  intro i
  fin_cases i
  intro h
  exact matches_379
lemma matches_380 : Matches 380 := by decide +kernel
lemma match_part380 : FiniteIntervals.Covers MatchesAt 380 381 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 380 1
  intro i
  fin_cases i
  intro h
  exact matches_380
lemma matches_381 : Matches 381 := by decide +kernel
lemma match_part381 : FiniteIntervals.Covers MatchesAt 381 382 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 381 1
  intro i
  fin_cases i
  intro h
  exact matches_381
lemma matches_382 : Matches 382 := by decide +kernel
lemma match_part382 : FiniteIntervals.Covers MatchesAt 382 383 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 382 1
  intro i
  fin_cases i
  intro h
  exact matches_382
lemma matches_383 : Matches 383 := by decide +kernel
lemma match_part383 : FiniteIntervals.Covers MatchesAt 383 384 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 383 1
  intro i
  fin_cases i
  intro h
  exact matches_383
lemma matches_interval31 : FiniteIntervals.Covers MatchesAt 372 384 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part372 (FiniteIntervals.merge match_part373 match_part374)) (FiniteIntervals.merge match_part375 (FiniteIntervals.merge match_part376 match_part377))) (FiniteIntervals.merge (FiniteIntervals.merge match_part378 (FiniteIntervals.merge match_part379 match_part380)) (FiniteIntervals.merge match_part381 (FiniteIntervals.merge match_part382 match_part383))))
#print axioms matches_interval31
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_348 : Matches 348 := by decide +kernel
lemma match_part348 : FiniteIntervals.Covers MatchesAt 348 349 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 348 1
  intro i
  fin_cases i
  intro h
  exact matches_348
lemma matches_349 : Matches 349 := by decide +kernel
lemma match_part349 : FiniteIntervals.Covers MatchesAt 349 350 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 349 1
  intro i
  fin_cases i
  intro h
  exact matches_349
lemma matches_350 : Matches 350 := by decide +kernel
lemma match_part350 : FiniteIntervals.Covers MatchesAt 350 351 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 350 1
  intro i
  fin_cases i
  intro h
  exact matches_350
lemma matches_351 : Matches 351 := by decide +kernel
lemma match_part351 : FiniteIntervals.Covers MatchesAt 351 352 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 351 1
  intro i
  fin_cases i
  intro h
  exact matches_351
lemma matches_352 : Matches 352 := by decide +kernel
lemma match_part352 : FiniteIntervals.Covers MatchesAt 352 353 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 352 1
  intro i
  fin_cases i
  intro h
  exact matches_352
lemma matches_353 : Matches 353 := by decide +kernel
lemma match_part353 : FiniteIntervals.Covers MatchesAt 353 354 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 353 1
  intro i
  fin_cases i
  intro h
  exact matches_353
lemma matches_354 : Matches 354 := by decide +kernel
lemma match_part354 : FiniteIntervals.Covers MatchesAt 354 355 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 354 1
  intro i
  fin_cases i
  intro h
  exact matches_354
lemma matches_355 : Matches 355 := by decide +kernel
lemma match_part355 : FiniteIntervals.Covers MatchesAt 355 356 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 355 1
  intro i
  fin_cases i
  intro h
  exact matches_355
lemma matches_356 : Matches 356 := by decide +kernel
lemma match_part356 : FiniteIntervals.Covers MatchesAt 356 357 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 356 1
  intro i
  fin_cases i
  intro h
  exact matches_356
lemma matches_357 : Matches 357 := by decide +kernel
lemma match_part357 : FiniteIntervals.Covers MatchesAt 357 358 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 357 1
  intro i
  fin_cases i
  intro h
  exact matches_357
lemma matches_358 : Matches 358 := by decide +kernel
lemma match_part358 : FiniteIntervals.Covers MatchesAt 358 359 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 358 1
  intro i
  fin_cases i
  intro h
  exact matches_358
lemma matches_359 : Matches 359 := by decide +kernel
lemma match_part359 : FiniteIntervals.Covers MatchesAt 359 360 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 359 1
  intro i
  fin_cases i
  intro h
  exact matches_359
lemma matches_interval29 : FiniteIntervals.Covers MatchesAt 348 360 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part348 (FiniteIntervals.merge match_part349 match_part350)) (FiniteIntervals.merge match_part351 (FiniteIntervals.merge match_part352 match_part353))) (FiniteIntervals.merge (FiniteIntervals.merge match_part354 (FiniteIntervals.merge match_part355 match_part356)) (FiniteIntervals.merge match_part357 (FiniteIntervals.merge match_part358 match_part359))))
#print axioms matches_interval29
end Erdos184Work.PureSevenActions

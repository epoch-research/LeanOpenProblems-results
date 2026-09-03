import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_336 : Matches 336 := by decide +kernel
lemma match_part336 : FiniteIntervals.Covers MatchesAt 336 337 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 336 1
  intro i
  fin_cases i
  intro h
  exact matches_336
lemma matches_337 : Matches 337 := by decide +kernel
lemma match_part337 : FiniteIntervals.Covers MatchesAt 337 338 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 337 1
  intro i
  fin_cases i
  intro h
  exact matches_337
lemma matches_338 : Matches 338 := by decide +kernel
lemma match_part338 : FiniteIntervals.Covers MatchesAt 338 339 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 338 1
  intro i
  fin_cases i
  intro h
  exact matches_338
lemma matches_339 : Matches 339 := by decide +kernel
lemma match_part339 : FiniteIntervals.Covers MatchesAt 339 340 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 339 1
  intro i
  fin_cases i
  intro h
  exact matches_339
lemma matches_340 : Matches 340 := by decide +kernel
lemma match_part340 : FiniteIntervals.Covers MatchesAt 340 341 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 340 1
  intro i
  fin_cases i
  intro h
  exact matches_340
lemma matches_341 : Matches 341 := by decide +kernel
lemma match_part341 : FiniteIntervals.Covers MatchesAt 341 342 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 341 1
  intro i
  fin_cases i
  intro h
  exact matches_341
lemma matches_342 : Matches 342 := by decide +kernel
lemma match_part342 : FiniteIntervals.Covers MatchesAt 342 343 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 342 1
  intro i
  fin_cases i
  intro h
  exact matches_342
lemma matches_343 : Matches 343 := by decide +kernel
lemma match_part343 : FiniteIntervals.Covers MatchesAt 343 344 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 343 1
  intro i
  fin_cases i
  intro h
  exact matches_343
lemma matches_344 : Matches 344 := by decide +kernel
lemma match_part344 : FiniteIntervals.Covers MatchesAt 344 345 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 344 1
  intro i
  fin_cases i
  intro h
  exact matches_344
lemma matches_345 : Matches 345 := by decide +kernel
lemma match_part345 : FiniteIntervals.Covers MatchesAt 345 346 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 345 1
  intro i
  fin_cases i
  intro h
  exact matches_345
lemma matches_346 : Matches 346 := by decide +kernel
lemma match_part346 : FiniteIntervals.Covers MatchesAt 346 347 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 346 1
  intro i
  fin_cases i
  intro h
  exact matches_346
lemma matches_347 : Matches 347 := by decide +kernel
lemma match_part347 : FiniteIntervals.Covers MatchesAt 347 348 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 347 1
  intro i
  fin_cases i
  intro h
  exact matches_347
lemma matches_interval28 : FiniteIntervals.Covers MatchesAt 336 348 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part336 (FiniteIntervals.merge match_part337 match_part338)) (FiniteIntervals.merge match_part339 (FiniteIntervals.merge match_part340 match_part341))) (FiniteIntervals.merge (FiniteIntervals.merge match_part342 (FiniteIntervals.merge match_part343 match_part344)) (FiniteIntervals.merge match_part345 (FiniteIntervals.merge match_part346 match_part347))))
#print axioms matches_interval28
end Erdos184Work.PureSevenActions

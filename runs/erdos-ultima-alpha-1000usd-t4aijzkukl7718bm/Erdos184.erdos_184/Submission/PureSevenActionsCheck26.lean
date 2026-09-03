import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_312 : Matches 312 := by decide +kernel
lemma match_part312 : FiniteIntervals.Covers MatchesAt 312 313 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 312 1
  intro i
  fin_cases i
  intro h
  exact matches_312
lemma matches_313 : Matches 313 := by decide +kernel
lemma match_part313 : FiniteIntervals.Covers MatchesAt 313 314 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 313 1
  intro i
  fin_cases i
  intro h
  exact matches_313
lemma matches_314 : Matches 314 := by decide +kernel
lemma match_part314 : FiniteIntervals.Covers MatchesAt 314 315 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 314 1
  intro i
  fin_cases i
  intro h
  exact matches_314
lemma matches_315 : Matches 315 := by decide +kernel
lemma match_part315 : FiniteIntervals.Covers MatchesAt 315 316 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 315 1
  intro i
  fin_cases i
  intro h
  exact matches_315
lemma matches_316 : Matches 316 := by decide +kernel
lemma match_part316 : FiniteIntervals.Covers MatchesAt 316 317 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 316 1
  intro i
  fin_cases i
  intro h
  exact matches_316
lemma matches_317 : Matches 317 := by decide +kernel
lemma match_part317 : FiniteIntervals.Covers MatchesAt 317 318 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 317 1
  intro i
  fin_cases i
  intro h
  exact matches_317
lemma matches_318 : Matches 318 := by decide +kernel
lemma match_part318 : FiniteIntervals.Covers MatchesAt 318 319 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 318 1
  intro i
  fin_cases i
  intro h
  exact matches_318
lemma matches_319 : Matches 319 := by decide +kernel
lemma match_part319 : FiniteIntervals.Covers MatchesAt 319 320 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 319 1
  intro i
  fin_cases i
  intro h
  exact matches_319
lemma matches_320 : Matches 320 := by decide +kernel
lemma match_part320 : FiniteIntervals.Covers MatchesAt 320 321 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 320 1
  intro i
  fin_cases i
  intro h
  exact matches_320
lemma matches_321 : Matches 321 := by decide +kernel
lemma match_part321 : FiniteIntervals.Covers MatchesAt 321 322 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 321 1
  intro i
  fin_cases i
  intro h
  exact matches_321
lemma matches_322 : Matches 322 := by decide +kernel
lemma match_part322 : FiniteIntervals.Covers MatchesAt 322 323 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 322 1
  intro i
  fin_cases i
  intro h
  exact matches_322
lemma matches_323 : Matches 323 := by decide +kernel
lemma match_part323 : FiniteIntervals.Covers MatchesAt 323 324 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 323 1
  intro i
  fin_cases i
  intro h
  exact matches_323
lemma matches_interval26 : FiniteIntervals.Covers MatchesAt 312 324 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part312 (FiniteIntervals.merge match_part313 match_part314)) (FiniteIntervals.merge match_part315 (FiniteIntervals.merge match_part316 match_part317))) (FiniteIntervals.merge (FiniteIntervals.merge match_part318 (FiniteIntervals.merge match_part319 match_part320)) (FiniteIntervals.merge match_part321 (FiniteIntervals.merge match_part322 match_part323))))
#print axioms matches_interval26
end Erdos184Work.PureSevenActions

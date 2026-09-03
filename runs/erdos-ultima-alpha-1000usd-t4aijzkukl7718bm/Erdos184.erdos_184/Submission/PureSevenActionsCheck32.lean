import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_384 : Matches 384 := by decide +kernel
lemma match_part384 : FiniteIntervals.Covers MatchesAt 384 385 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 384 1
  intro i
  fin_cases i
  intro h
  exact matches_384
lemma matches_385 : Matches 385 := by decide +kernel
lemma match_part385 : FiniteIntervals.Covers MatchesAt 385 386 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 385 1
  intro i
  fin_cases i
  intro h
  exact matches_385
lemma matches_386 : Matches 386 := by decide +kernel
lemma match_part386 : FiniteIntervals.Covers MatchesAt 386 387 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 386 1
  intro i
  fin_cases i
  intro h
  exact matches_386
lemma matches_387 : Matches 387 := by decide +kernel
lemma match_part387 : FiniteIntervals.Covers MatchesAt 387 388 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 387 1
  intro i
  fin_cases i
  intro h
  exact matches_387
lemma matches_388 : Matches 388 := by decide +kernel
lemma match_part388 : FiniteIntervals.Covers MatchesAt 388 389 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 388 1
  intro i
  fin_cases i
  intro h
  exact matches_388
lemma matches_389 : Matches 389 := by decide +kernel
lemma match_part389 : FiniteIntervals.Covers MatchesAt 389 390 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 389 1
  intro i
  fin_cases i
  intro h
  exact matches_389
lemma matches_390 : Matches 390 := by decide +kernel
lemma match_part390 : FiniteIntervals.Covers MatchesAt 390 391 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 390 1
  intro i
  fin_cases i
  intro h
  exact matches_390
lemma matches_391 : Matches 391 := by decide +kernel
lemma match_part391 : FiniteIntervals.Covers MatchesAt 391 392 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 391 1
  intro i
  fin_cases i
  intro h
  exact matches_391
lemma matches_392 : Matches 392 := by decide +kernel
lemma match_part392 : FiniteIntervals.Covers MatchesAt 392 393 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 392 1
  intro i
  fin_cases i
  intro h
  exact matches_392
lemma matches_393 : Matches 393 := by decide +kernel
lemma match_part393 : FiniteIntervals.Covers MatchesAt 393 394 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 393 1
  intro i
  fin_cases i
  intro h
  exact matches_393
lemma matches_394 : Matches 394 := by decide +kernel
lemma match_part394 : FiniteIntervals.Covers MatchesAt 394 395 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 394 1
  intro i
  fin_cases i
  intro h
  exact matches_394
lemma matches_395 : Matches 395 := by decide +kernel
lemma match_part395 : FiniteIntervals.Covers MatchesAt 395 396 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 395 1
  intro i
  fin_cases i
  intro h
  exact matches_395
lemma matches_interval32 : FiniteIntervals.Covers MatchesAt 384 396 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part384 (FiniteIntervals.merge match_part385 match_part386)) (FiniteIntervals.merge match_part387 (FiniteIntervals.merge match_part388 match_part389))) (FiniteIntervals.merge (FiniteIntervals.merge match_part390 (FiniteIntervals.merge match_part391 match_part392)) (FiniteIntervals.merge match_part393 (FiniteIntervals.merge match_part394 match_part395))))
#print axioms matches_interval32
end Erdos184Work.PureSevenActions

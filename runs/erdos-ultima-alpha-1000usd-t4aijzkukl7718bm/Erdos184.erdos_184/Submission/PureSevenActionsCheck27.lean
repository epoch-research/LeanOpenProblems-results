import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_324 : Matches 324 := by decide +kernel
lemma match_part324 : FiniteIntervals.Covers MatchesAt 324 325 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 324 1
  intro i
  fin_cases i
  intro h
  exact matches_324
lemma matches_325 : Matches 325 := by decide +kernel
lemma match_part325 : FiniteIntervals.Covers MatchesAt 325 326 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 325 1
  intro i
  fin_cases i
  intro h
  exact matches_325
lemma matches_326 : Matches 326 := by decide +kernel
lemma match_part326 : FiniteIntervals.Covers MatchesAt 326 327 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 326 1
  intro i
  fin_cases i
  intro h
  exact matches_326
lemma matches_327 : Matches 327 := by decide +kernel
lemma match_part327 : FiniteIntervals.Covers MatchesAt 327 328 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 327 1
  intro i
  fin_cases i
  intro h
  exact matches_327
lemma matches_328 : Matches 328 := by decide +kernel
lemma match_part328 : FiniteIntervals.Covers MatchesAt 328 329 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 328 1
  intro i
  fin_cases i
  intro h
  exact matches_328
lemma matches_329 : Matches 329 := by decide +kernel
lemma match_part329 : FiniteIntervals.Covers MatchesAt 329 330 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 329 1
  intro i
  fin_cases i
  intro h
  exact matches_329
lemma matches_330 : Matches 330 := by decide +kernel
lemma match_part330 : FiniteIntervals.Covers MatchesAt 330 331 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 330 1
  intro i
  fin_cases i
  intro h
  exact matches_330
lemma matches_331 : Matches 331 := by decide +kernel
lemma match_part331 : FiniteIntervals.Covers MatchesAt 331 332 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 331 1
  intro i
  fin_cases i
  intro h
  exact matches_331
lemma matches_332 : Matches 332 := by decide +kernel
lemma match_part332 : FiniteIntervals.Covers MatchesAt 332 333 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 332 1
  intro i
  fin_cases i
  intro h
  exact matches_332
lemma matches_333 : Matches 333 := by decide +kernel
lemma match_part333 : FiniteIntervals.Covers MatchesAt 333 334 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 333 1
  intro i
  fin_cases i
  intro h
  exact matches_333
lemma matches_334 : Matches 334 := by decide +kernel
lemma match_part334 : FiniteIntervals.Covers MatchesAt 334 335 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 334 1
  intro i
  fin_cases i
  intro h
  exact matches_334
lemma matches_335 : Matches 335 := by decide +kernel
lemma match_part335 : FiniteIntervals.Covers MatchesAt 335 336 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 335 1
  intro i
  fin_cases i
  intro h
  exact matches_335
lemma matches_interval27 : FiniteIntervals.Covers MatchesAt 324 336 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part324 (FiniteIntervals.merge match_part325 match_part326)) (FiniteIntervals.merge match_part327 (FiniteIntervals.merge match_part328 match_part329))) (FiniteIntervals.merge (FiniteIntervals.merge match_part330 (FiniteIntervals.merge match_part331 match_part332)) (FiniteIntervals.merge match_part333 (FiniteIntervals.merge match_part334 match_part335))))
#print axioms matches_interval27
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_276 : Matches 276 := by decide +kernel
lemma match_part276 : FiniteIntervals.Covers MatchesAt 276 277 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 276 1
  intro i
  fin_cases i
  intro h
  exact matches_276
lemma matches_277 : Matches 277 := by decide +kernel
lemma match_part277 : FiniteIntervals.Covers MatchesAt 277 278 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 277 1
  intro i
  fin_cases i
  intro h
  exact matches_277
lemma matches_278 : Matches 278 := by decide +kernel
lemma match_part278 : FiniteIntervals.Covers MatchesAt 278 279 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 278 1
  intro i
  fin_cases i
  intro h
  exact matches_278
lemma matches_279 : Matches 279 := by decide +kernel
lemma match_part279 : FiniteIntervals.Covers MatchesAt 279 280 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 279 1
  intro i
  fin_cases i
  intro h
  exact matches_279
lemma matches_280 : Matches 280 := by decide +kernel
lemma match_part280 : FiniteIntervals.Covers MatchesAt 280 281 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 280 1
  intro i
  fin_cases i
  intro h
  exact matches_280
lemma matches_281 : Matches 281 := by decide +kernel
lemma match_part281 : FiniteIntervals.Covers MatchesAt 281 282 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 281 1
  intro i
  fin_cases i
  intro h
  exact matches_281
lemma matches_282 : Matches 282 := by decide +kernel
lemma match_part282 : FiniteIntervals.Covers MatchesAt 282 283 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 282 1
  intro i
  fin_cases i
  intro h
  exact matches_282
lemma matches_283 : Matches 283 := by decide +kernel
lemma match_part283 : FiniteIntervals.Covers MatchesAt 283 284 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 283 1
  intro i
  fin_cases i
  intro h
  exact matches_283
lemma matches_284 : Matches 284 := by decide +kernel
lemma match_part284 : FiniteIntervals.Covers MatchesAt 284 285 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 284 1
  intro i
  fin_cases i
  intro h
  exact matches_284
lemma matches_285 : Matches 285 := by decide +kernel
lemma match_part285 : FiniteIntervals.Covers MatchesAt 285 286 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 285 1
  intro i
  fin_cases i
  intro h
  exact matches_285
lemma matches_286 : Matches 286 := by decide +kernel
lemma match_part286 : FiniteIntervals.Covers MatchesAt 286 287 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 286 1
  intro i
  fin_cases i
  intro h
  exact matches_286
lemma matches_287 : Matches 287 := by decide +kernel
lemma match_part287 : FiniteIntervals.Covers MatchesAt 287 288 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 287 1
  intro i
  fin_cases i
  intro h
  exact matches_287
lemma matches_interval23 : FiniteIntervals.Covers MatchesAt 276 288 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part276 (FiniteIntervals.merge match_part277 match_part278)) (FiniteIntervals.merge match_part279 (FiniteIntervals.merge match_part280 match_part281))) (FiniteIntervals.merge (FiniteIntervals.merge match_part282 (FiniteIntervals.merge match_part283 match_part284)) (FiniteIntervals.merge match_part285 (FiniteIntervals.merge match_part286 match_part287))))
#print axioms matches_interval23
end Erdos184Work.PureSevenActions

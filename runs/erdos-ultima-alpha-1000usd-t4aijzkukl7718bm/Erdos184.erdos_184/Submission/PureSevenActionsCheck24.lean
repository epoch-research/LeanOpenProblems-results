import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_288 : Matches 288 := by decide +kernel
lemma match_part288 : FiniteIntervals.Covers MatchesAt 288 289 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 288 1
  intro i
  fin_cases i
  intro h
  exact matches_288
lemma matches_289 : Matches 289 := by decide +kernel
lemma match_part289 : FiniteIntervals.Covers MatchesAt 289 290 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 289 1
  intro i
  fin_cases i
  intro h
  exact matches_289
lemma matches_290 : Matches 290 := by decide +kernel
lemma match_part290 : FiniteIntervals.Covers MatchesAt 290 291 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 290 1
  intro i
  fin_cases i
  intro h
  exact matches_290
lemma matches_291 : Matches 291 := by decide +kernel
lemma match_part291 : FiniteIntervals.Covers MatchesAt 291 292 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 291 1
  intro i
  fin_cases i
  intro h
  exact matches_291
lemma matches_292 : Matches 292 := by decide +kernel
lemma match_part292 : FiniteIntervals.Covers MatchesAt 292 293 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 292 1
  intro i
  fin_cases i
  intro h
  exact matches_292
lemma matches_293 : Matches 293 := by decide +kernel
lemma match_part293 : FiniteIntervals.Covers MatchesAt 293 294 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 293 1
  intro i
  fin_cases i
  intro h
  exact matches_293
lemma matches_294 : Matches 294 := by decide +kernel
lemma match_part294 : FiniteIntervals.Covers MatchesAt 294 295 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 294 1
  intro i
  fin_cases i
  intro h
  exact matches_294
lemma matches_295 : Matches 295 := by decide +kernel
lemma match_part295 : FiniteIntervals.Covers MatchesAt 295 296 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 295 1
  intro i
  fin_cases i
  intro h
  exact matches_295
lemma matches_296 : Matches 296 := by decide +kernel
lemma match_part296 : FiniteIntervals.Covers MatchesAt 296 297 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 296 1
  intro i
  fin_cases i
  intro h
  exact matches_296
lemma matches_297 : Matches 297 := by decide +kernel
lemma match_part297 : FiniteIntervals.Covers MatchesAt 297 298 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 297 1
  intro i
  fin_cases i
  intro h
  exact matches_297
lemma matches_298 : Matches 298 := by decide +kernel
lemma match_part298 : FiniteIntervals.Covers MatchesAt 298 299 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 298 1
  intro i
  fin_cases i
  intro h
  exact matches_298
lemma matches_299 : Matches 299 := by decide +kernel
lemma match_part299 : FiniteIntervals.Covers MatchesAt 299 300 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 299 1
  intro i
  fin_cases i
  intro h
  exact matches_299
lemma matches_interval24 : FiniteIntervals.Covers MatchesAt 288 300 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part288 (FiniteIntervals.merge match_part289 match_part290)) (FiniteIntervals.merge match_part291 (FiniteIntervals.merge match_part292 match_part293))) (FiniteIntervals.merge (FiniteIntervals.merge match_part294 (FiniteIntervals.merge match_part295 match_part296)) (FiniteIntervals.merge match_part297 (FiniteIntervals.merge match_part298 match_part299))))
#print axioms matches_interval24
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_300 : Matches 300 := by decide +kernel
lemma match_part300 : FiniteIntervals.Covers MatchesAt 300 301 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 300 1
  intro i
  fin_cases i
  intro h
  exact matches_300
lemma matches_301 : Matches 301 := by decide +kernel
lemma match_part301 : FiniteIntervals.Covers MatchesAt 301 302 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 301 1
  intro i
  fin_cases i
  intro h
  exact matches_301
lemma matches_302 : Matches 302 := by decide +kernel
lemma match_part302 : FiniteIntervals.Covers MatchesAt 302 303 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 302 1
  intro i
  fin_cases i
  intro h
  exact matches_302
lemma matches_303 : Matches 303 := by decide +kernel
lemma match_part303 : FiniteIntervals.Covers MatchesAt 303 304 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 303 1
  intro i
  fin_cases i
  intro h
  exact matches_303
lemma matches_304 : Matches 304 := by decide +kernel
lemma match_part304 : FiniteIntervals.Covers MatchesAt 304 305 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 304 1
  intro i
  fin_cases i
  intro h
  exact matches_304
lemma matches_305 : Matches 305 := by decide +kernel
lemma match_part305 : FiniteIntervals.Covers MatchesAt 305 306 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 305 1
  intro i
  fin_cases i
  intro h
  exact matches_305
lemma matches_306 : Matches 306 := by decide +kernel
lemma match_part306 : FiniteIntervals.Covers MatchesAt 306 307 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 306 1
  intro i
  fin_cases i
  intro h
  exact matches_306
lemma matches_307 : Matches 307 := by decide +kernel
lemma match_part307 : FiniteIntervals.Covers MatchesAt 307 308 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 307 1
  intro i
  fin_cases i
  intro h
  exact matches_307
lemma matches_308 : Matches 308 := by decide +kernel
lemma match_part308 : FiniteIntervals.Covers MatchesAt 308 309 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 308 1
  intro i
  fin_cases i
  intro h
  exact matches_308
lemma matches_309 : Matches 309 := by decide +kernel
lemma match_part309 : FiniteIntervals.Covers MatchesAt 309 310 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 309 1
  intro i
  fin_cases i
  intro h
  exact matches_309
lemma matches_310 : Matches 310 := by decide +kernel
lemma match_part310 : FiniteIntervals.Covers MatchesAt 310 311 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 310 1
  intro i
  fin_cases i
  intro h
  exact matches_310
lemma matches_311 : Matches 311 := by decide +kernel
lemma match_part311 : FiniteIntervals.Covers MatchesAt 311 312 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 311 1
  intro i
  fin_cases i
  intro h
  exact matches_311
lemma matches_interval25 : FiniteIntervals.Covers MatchesAt 300 312 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part300 (FiniteIntervals.merge match_part301 match_part302)) (FiniteIntervals.merge match_part303 (FiniteIntervals.merge match_part304 match_part305))) (FiniteIntervals.merge (FiniteIntervals.merge match_part306 (FiniteIntervals.merge match_part307 match_part308)) (FiniteIntervals.merge match_part309 (FiniteIntervals.merge match_part310 match_part311))))
#print axioms matches_interval25
end Erdos184Work.PureSevenActions

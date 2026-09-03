import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_252 : Matches 252 := by decide +kernel
lemma match_part252 : FiniteIntervals.Covers MatchesAt 252 253 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 252 1
  intro i
  fin_cases i
  intro h
  exact matches_252
lemma matches_253 : Matches 253 := by decide +kernel
lemma match_part253 : FiniteIntervals.Covers MatchesAt 253 254 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 253 1
  intro i
  fin_cases i
  intro h
  exact matches_253
lemma matches_254 : Matches 254 := by decide +kernel
lemma match_part254 : FiniteIntervals.Covers MatchesAt 254 255 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 254 1
  intro i
  fin_cases i
  intro h
  exact matches_254
lemma matches_255 : Matches 255 := by decide +kernel
lemma match_part255 : FiniteIntervals.Covers MatchesAt 255 256 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 255 1
  intro i
  fin_cases i
  intro h
  exact matches_255
lemma matches_256 : Matches 256 := by decide +kernel
lemma match_part256 : FiniteIntervals.Covers MatchesAt 256 257 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 256 1
  intro i
  fin_cases i
  intro h
  exact matches_256
lemma matches_257 : Matches 257 := by decide +kernel
lemma match_part257 : FiniteIntervals.Covers MatchesAt 257 258 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 257 1
  intro i
  fin_cases i
  intro h
  exact matches_257
lemma matches_258 : Matches 258 := by decide +kernel
lemma match_part258 : FiniteIntervals.Covers MatchesAt 258 259 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 258 1
  intro i
  fin_cases i
  intro h
  exact matches_258
lemma matches_259 : Matches 259 := by decide +kernel
lemma match_part259 : FiniteIntervals.Covers MatchesAt 259 260 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 259 1
  intro i
  fin_cases i
  intro h
  exact matches_259
lemma matches_260 : Matches 260 := by decide +kernel
lemma match_part260 : FiniteIntervals.Covers MatchesAt 260 261 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 260 1
  intro i
  fin_cases i
  intro h
  exact matches_260
lemma matches_261 : Matches 261 := by decide +kernel
lemma match_part261 : FiniteIntervals.Covers MatchesAt 261 262 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 261 1
  intro i
  fin_cases i
  intro h
  exact matches_261
lemma matches_262 : Matches 262 := by decide +kernel
lemma match_part262 : FiniteIntervals.Covers MatchesAt 262 263 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 262 1
  intro i
  fin_cases i
  intro h
  exact matches_262
lemma matches_263 : Matches 263 := by decide +kernel
lemma match_part263 : FiniteIntervals.Covers MatchesAt 263 264 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 263 1
  intro i
  fin_cases i
  intro h
  exact matches_263
lemma matches_interval21 : FiniteIntervals.Covers MatchesAt 252 264 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part252 (FiniteIntervals.merge match_part253 match_part254)) (FiniteIntervals.merge match_part255 (FiniteIntervals.merge match_part256 match_part257))) (FiniteIntervals.merge (FiniteIntervals.merge match_part258 (FiniteIntervals.merge match_part259 match_part260)) (FiniteIntervals.merge match_part261 (FiniteIntervals.merge match_part262 match_part263))))
#print axioms matches_interval21
end Erdos184Work.PureSevenActions

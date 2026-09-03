import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_216 : Matches 216 := by decide +kernel
lemma match_part216 : FiniteIntervals.Covers MatchesAt 216 217 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 216 1
  intro i
  fin_cases i
  intro h
  exact matches_216
lemma matches_217 : Matches 217 := by decide +kernel
lemma match_part217 : FiniteIntervals.Covers MatchesAt 217 218 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 217 1
  intro i
  fin_cases i
  intro h
  exact matches_217
lemma matches_218 : Matches 218 := by decide +kernel
lemma match_part218 : FiniteIntervals.Covers MatchesAt 218 219 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 218 1
  intro i
  fin_cases i
  intro h
  exact matches_218
lemma matches_219 : Matches 219 := by decide +kernel
lemma match_part219 : FiniteIntervals.Covers MatchesAt 219 220 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 219 1
  intro i
  fin_cases i
  intro h
  exact matches_219
lemma matches_220 : Matches 220 := by decide +kernel
lemma match_part220 : FiniteIntervals.Covers MatchesAt 220 221 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 220 1
  intro i
  fin_cases i
  intro h
  exact matches_220
lemma matches_221 : Matches 221 := by decide +kernel
lemma match_part221 : FiniteIntervals.Covers MatchesAt 221 222 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 221 1
  intro i
  fin_cases i
  intro h
  exact matches_221
lemma matches_222 : Matches 222 := by decide +kernel
lemma match_part222 : FiniteIntervals.Covers MatchesAt 222 223 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 222 1
  intro i
  fin_cases i
  intro h
  exact matches_222
lemma matches_223 : Matches 223 := by decide +kernel
lemma match_part223 : FiniteIntervals.Covers MatchesAt 223 224 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 223 1
  intro i
  fin_cases i
  intro h
  exact matches_223
lemma matches_224 : Matches 224 := by decide +kernel
lemma match_part224 : FiniteIntervals.Covers MatchesAt 224 225 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 224 1
  intro i
  fin_cases i
  intro h
  exact matches_224
lemma matches_225 : Matches 225 := by decide +kernel
lemma match_part225 : FiniteIntervals.Covers MatchesAt 225 226 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 225 1
  intro i
  fin_cases i
  intro h
  exact matches_225
lemma matches_226 : Matches 226 := by decide +kernel
lemma match_part226 : FiniteIntervals.Covers MatchesAt 226 227 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 226 1
  intro i
  fin_cases i
  intro h
  exact matches_226
lemma matches_227 : Matches 227 := by decide +kernel
lemma match_part227 : FiniteIntervals.Covers MatchesAt 227 228 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 227 1
  intro i
  fin_cases i
  intro h
  exact matches_227
lemma matches_interval18 : FiniteIntervals.Covers MatchesAt 216 228 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part216 (FiniteIntervals.merge match_part217 match_part218)) (FiniteIntervals.merge match_part219 (FiniteIntervals.merge match_part220 match_part221))) (FiniteIntervals.merge (FiniteIntervals.merge match_part222 (FiniteIntervals.merge match_part223 match_part224)) (FiniteIntervals.merge match_part225 (FiniteIntervals.merge match_part226 match_part227))))
#print axioms matches_interval18
end Erdos184Work.PureSevenActions

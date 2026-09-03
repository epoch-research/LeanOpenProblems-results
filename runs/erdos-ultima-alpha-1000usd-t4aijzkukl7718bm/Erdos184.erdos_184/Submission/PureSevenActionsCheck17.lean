import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_204 : Matches 204 := by decide +kernel
lemma match_part204 : FiniteIntervals.Covers MatchesAt 204 205 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 204 1
  intro i
  fin_cases i
  intro h
  exact matches_204
lemma matches_205 : Matches 205 := by decide +kernel
lemma match_part205 : FiniteIntervals.Covers MatchesAt 205 206 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 205 1
  intro i
  fin_cases i
  intro h
  exact matches_205
lemma matches_206 : Matches 206 := by decide +kernel
lemma match_part206 : FiniteIntervals.Covers MatchesAt 206 207 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 206 1
  intro i
  fin_cases i
  intro h
  exact matches_206
lemma matches_207 : Matches 207 := by decide +kernel
lemma match_part207 : FiniteIntervals.Covers MatchesAt 207 208 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 207 1
  intro i
  fin_cases i
  intro h
  exact matches_207
lemma matches_208 : Matches 208 := by decide +kernel
lemma match_part208 : FiniteIntervals.Covers MatchesAt 208 209 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 208 1
  intro i
  fin_cases i
  intro h
  exact matches_208
lemma matches_209 : Matches 209 := by decide +kernel
lemma match_part209 : FiniteIntervals.Covers MatchesAt 209 210 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 209 1
  intro i
  fin_cases i
  intro h
  exact matches_209
lemma matches_210 : Matches 210 := by decide +kernel
lemma match_part210 : FiniteIntervals.Covers MatchesAt 210 211 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 210 1
  intro i
  fin_cases i
  intro h
  exact matches_210
lemma matches_211 : Matches 211 := by decide +kernel
lemma match_part211 : FiniteIntervals.Covers MatchesAt 211 212 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 211 1
  intro i
  fin_cases i
  intro h
  exact matches_211
lemma matches_212 : Matches 212 := by decide +kernel
lemma match_part212 : FiniteIntervals.Covers MatchesAt 212 213 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 212 1
  intro i
  fin_cases i
  intro h
  exact matches_212
lemma matches_213 : Matches 213 := by decide +kernel
lemma match_part213 : FiniteIntervals.Covers MatchesAt 213 214 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 213 1
  intro i
  fin_cases i
  intro h
  exact matches_213
lemma matches_214 : Matches 214 := by decide +kernel
lemma match_part214 : FiniteIntervals.Covers MatchesAt 214 215 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 214 1
  intro i
  fin_cases i
  intro h
  exact matches_214
lemma matches_215 : Matches 215 := by decide +kernel
lemma match_part215 : FiniteIntervals.Covers MatchesAt 215 216 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 215 1
  intro i
  fin_cases i
  intro h
  exact matches_215
lemma matches_interval17 : FiniteIntervals.Covers MatchesAt 204 216 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part204 (FiniteIntervals.merge match_part205 match_part206)) (FiniteIntervals.merge match_part207 (FiniteIntervals.merge match_part208 match_part209))) (FiniteIntervals.merge (FiniteIntervals.merge match_part210 (FiniteIntervals.merge match_part211 match_part212)) (FiniteIntervals.merge match_part213 (FiniteIntervals.merge match_part214 match_part215))))
#print axioms matches_interval17
end Erdos184Work.PureSevenActions

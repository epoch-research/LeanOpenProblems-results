import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_180 : Matches 180 := by decide +kernel
lemma match_part180 : FiniteIntervals.Covers MatchesAt 180 181 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 180 1
  intro i
  fin_cases i
  intro h
  exact matches_180
lemma matches_181 : Matches 181 := by decide +kernel
lemma match_part181 : FiniteIntervals.Covers MatchesAt 181 182 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 181 1
  intro i
  fin_cases i
  intro h
  exact matches_181
lemma matches_182 : Matches 182 := by decide +kernel
lemma match_part182 : FiniteIntervals.Covers MatchesAt 182 183 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 182 1
  intro i
  fin_cases i
  intro h
  exact matches_182
lemma matches_183 : Matches 183 := by decide +kernel
lemma match_part183 : FiniteIntervals.Covers MatchesAt 183 184 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 183 1
  intro i
  fin_cases i
  intro h
  exact matches_183
lemma matches_184 : Matches 184 := by decide +kernel
lemma match_part184 : FiniteIntervals.Covers MatchesAt 184 185 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 184 1
  intro i
  fin_cases i
  intro h
  exact matches_184
lemma matches_185 : Matches 185 := by decide +kernel
lemma match_part185 : FiniteIntervals.Covers MatchesAt 185 186 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 185 1
  intro i
  fin_cases i
  intro h
  exact matches_185
lemma matches_186 : Matches 186 := by decide +kernel
lemma match_part186 : FiniteIntervals.Covers MatchesAt 186 187 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 186 1
  intro i
  fin_cases i
  intro h
  exact matches_186
lemma matches_187 : Matches 187 := by decide +kernel
lemma match_part187 : FiniteIntervals.Covers MatchesAt 187 188 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 187 1
  intro i
  fin_cases i
  intro h
  exact matches_187
lemma matches_188 : Matches 188 := by decide +kernel
lemma match_part188 : FiniteIntervals.Covers MatchesAt 188 189 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 188 1
  intro i
  fin_cases i
  intro h
  exact matches_188
lemma matches_189 : Matches 189 := by decide +kernel
lemma match_part189 : FiniteIntervals.Covers MatchesAt 189 190 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 189 1
  intro i
  fin_cases i
  intro h
  exact matches_189
lemma matches_190 : Matches 190 := by decide +kernel
lemma match_part190 : FiniteIntervals.Covers MatchesAt 190 191 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 190 1
  intro i
  fin_cases i
  intro h
  exact matches_190
lemma matches_191 : Matches 191 := by decide +kernel
lemma match_part191 : FiniteIntervals.Covers MatchesAt 191 192 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 191 1
  intro i
  fin_cases i
  intro h
  exact matches_191
lemma matches_interval15 : FiniteIntervals.Covers MatchesAt 180 192 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part180 (FiniteIntervals.merge match_part181 match_part182)) (FiniteIntervals.merge match_part183 (FiniteIntervals.merge match_part184 match_part185))) (FiniteIntervals.merge (FiniteIntervals.merge match_part186 (FiniteIntervals.merge match_part187 match_part188)) (FiniteIntervals.merge match_part189 (FiniteIntervals.merge match_part190 match_part191))))
#print axioms matches_interval15
end Erdos184Work.PureSevenActions

import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_144 : Matches 144 := by decide +kernel
lemma match_part144 : FiniteIntervals.Covers MatchesAt 144 145 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 144 1
  intro i
  fin_cases i
  intro h
  exact matches_144
lemma matches_145 : Matches 145 := by decide +kernel
lemma match_part145 : FiniteIntervals.Covers MatchesAt 145 146 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 145 1
  intro i
  fin_cases i
  intro h
  exact matches_145
lemma matches_146 : Matches 146 := by decide +kernel
lemma match_part146 : FiniteIntervals.Covers MatchesAt 146 147 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 146 1
  intro i
  fin_cases i
  intro h
  exact matches_146
lemma matches_147 : Matches 147 := by decide +kernel
lemma match_part147 : FiniteIntervals.Covers MatchesAt 147 148 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 147 1
  intro i
  fin_cases i
  intro h
  exact matches_147
lemma matches_148 : Matches 148 := by decide +kernel
lemma match_part148 : FiniteIntervals.Covers MatchesAt 148 149 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 148 1
  intro i
  fin_cases i
  intro h
  exact matches_148
lemma matches_149 : Matches 149 := by decide +kernel
lemma match_part149 : FiniteIntervals.Covers MatchesAt 149 150 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 149 1
  intro i
  fin_cases i
  intro h
  exact matches_149
lemma matches_150 : Matches 150 := by decide +kernel
lemma match_part150 : FiniteIntervals.Covers MatchesAt 150 151 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 150 1
  intro i
  fin_cases i
  intro h
  exact matches_150
lemma matches_151 : Matches 151 := by decide +kernel
lemma match_part151 : FiniteIntervals.Covers MatchesAt 151 152 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 151 1
  intro i
  fin_cases i
  intro h
  exact matches_151
lemma matches_152 : Matches 152 := by decide +kernel
lemma match_part152 : FiniteIntervals.Covers MatchesAt 152 153 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 152 1
  intro i
  fin_cases i
  intro h
  exact matches_152
lemma matches_153 : Matches 153 := by decide +kernel
lemma match_part153 : FiniteIntervals.Covers MatchesAt 153 154 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 153 1
  intro i
  fin_cases i
  intro h
  exact matches_153
lemma matches_154 : Matches 154 := by decide +kernel
lemma match_part154 : FiniteIntervals.Covers MatchesAt 154 155 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 154 1
  intro i
  fin_cases i
  intro h
  exact matches_154
lemma matches_155 : Matches 155 := by decide +kernel
lemma match_part155 : FiniteIntervals.Covers MatchesAt 155 156 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 155 1
  intro i
  fin_cases i
  intro h
  exact matches_155
lemma matches_interval12 : FiniteIntervals.Covers MatchesAt 144 156 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part144 (FiniteIntervals.merge match_part145 match_part146)) (FiniteIntervals.merge match_part147 (FiniteIntervals.merge match_part148 match_part149))) (FiniteIntervals.merge (FiniteIntervals.merge match_part150 (FiniteIntervals.merge match_part151 match_part152)) (FiniteIntervals.merge match_part153 (FiniteIntervals.merge match_part154 match_part155))))
#print axioms matches_interval12
end Erdos184Work.PureSevenActions

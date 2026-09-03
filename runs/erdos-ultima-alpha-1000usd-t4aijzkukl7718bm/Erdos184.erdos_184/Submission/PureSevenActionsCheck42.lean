import Submission.PureSevenActionsBase
namespace Erdos184Work.PureSevenActions
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma matches_504 : Matches 504 := by decide +kernel
lemma match_part504 : FiniteIntervals.Covers MatchesAt 504 505 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 504 1
  intro i
  fin_cases i
  intro h
  exact matches_504
lemma matches_505 : Matches 505 := by decide +kernel
lemma match_part505 : FiniteIntervals.Covers MatchesAt 505 506 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 505 1
  intro i
  fin_cases i
  intro h
  exact matches_505
lemma matches_506 : Matches 506 := by decide +kernel
lemma match_part506 : FiniteIntervals.Covers MatchesAt 506 507 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 506 1
  intro i
  fin_cases i
  intro h
  exact matches_506
lemma matches_507 : Matches 507 := by decide +kernel
lemma match_part507 : FiniteIntervals.Covers MatchesAt 507 508 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 507 1
  intro i
  fin_cases i
  intro h
  exact matches_507
lemma matches_508 : Matches 508 := by decide +kernel
lemma match_part508 : FiniteIntervals.Covers MatchesAt 508 509 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 508 1
  intro i
  fin_cases i
  intro h
  exact matches_508
lemma matches_509 : Matches 509 := by decide +kernel
lemma match_part509 : FiniteIntervals.Covers MatchesAt 509 510 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 509 1
  intro i
  fin_cases i
  intro h
  exact matches_509
lemma matches_510 : Matches 510 := by decide +kernel
lemma match_part510 : FiniteIntervals.Covers MatchesAt 510 511 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 510 1
  intro i
  fin_cases i
  intro h
  exact matches_510
lemma matches_511 : Matches 511 := by decide +kernel
lemma match_part511 : FiniteIntervals.Covers MatchesAt 511 512 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 511 1
  intro i
  fin_cases i
  intro h
  exact matches_511
lemma matches_512 : Matches 512 := by decide +kernel
lemma match_part512 : FiniteIntervals.Covers MatchesAt 512 513 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 512 1
  intro i
  fin_cases i
  intro h
  exact matches_512
lemma matches_513 : Matches 513 := by decide +kernel
lemma match_part513 : FiniteIntervals.Covers MatchesAt 513 514 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 513 1
  intro i
  fin_cases i
  intro h
  exact matches_513
lemma matches_514 : Matches 514 := by decide +kernel
lemma match_part514 : FiniteIntervals.Covers MatchesAt 514 515 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 514 1
  intro i
  fin_cases i
  intro h
  exact matches_514
lemma matches_515 : Matches 515 := by decide +kernel
lemma match_part515 : FiniteIntervals.Covers MatchesAt 515 516 := by
  apply FiniteIntervals.of_fin (P := MatchesAt) 515 1
  intro i
  fin_cases i
  intro h
  exact matches_515
lemma matches_interval42 : FiniteIntervals.Covers MatchesAt 504 516 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge match_part504 (FiniteIntervals.merge match_part505 match_part506)) (FiniteIntervals.merge match_part507 (FiniteIntervals.merge match_part508 match_part509))) (FiniteIntervals.merge (FiniteIntervals.merge match_part510 (FiniteIntervals.merge match_part511 match_part512)) (FiniteIntervals.merge match_part513 (FiniteIntervals.merge match_part514 match_part515))))
#print axioms matches_interval42
end Erdos184Work.PureSevenActions

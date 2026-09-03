import Submission.ChainRingCertificateGroup0_0
import Submission.ChainRingCertificateGroup0_1
import Submission.ChainRingCertificateGroup0_2
import Submission.ChainRingCertificateGroup0_3
import Submission.ChainRingCertificateGroup0_4
import Submission.ChainRingCertificateGroup0_5
import Submission.ChainRingCertificateGroup0_6
import Submission.ChainRingCertificateGroup1_0
import Submission.ChainRingCertificateGroup1_1
import Submission.ChainRingCertificateGroup1_2
import Submission.ChainRingCertificateGroup1_3
import Submission.ChainRingCertificateGroup1_4
import Submission.ChainRingCertificateGroup1_5
import Submission.ChainRingCertificateGroup1_6
import Submission.ChainRingHullReduction

namespace Erdos184Work.ChainRing
set_option maxHeartbeats 1000000
lemma canonical_all_false (a : Fin 3 → Fin 7) : ForestBound (canonical false a) := by
  have ha : a = ![a 0,a 1,a 2] := by funext i; fin_cases i <;> rfl
  rw [ha]
  generalize a 0 = x, a 1 = y, a 2 = z
  fin_cases x
  · exact canonical_group_0_0 y z
  · exact canonical_group_0_1 y z
  · exact canonical_group_0_2 y z
  · exact canonical_group_0_3 y z
  · exact canonical_group_0_4 y z
  · exact canonical_group_0_5 y z
  · exact canonical_group_0_6 y z
lemma canonical_all_true (a : Fin 3 → Fin 7) : ForestBound (canonical true a) := by
  have ha : a = ![a 0,a 1,a 2] := by funext i; fin_cases i <;> rfl
  rw [ha]
  generalize a 0 = x, a 1 = y, a 2 = z
  fin_cases x
  · exact canonical_group_1_0 y z
  · exact canonical_group_1_1 y z
  · exact canonical_group_1_2 y z
  · exact canonical_group_1_3 y z
  · exact canonical_group_1_4 y z
  · exact canonical_group_1_5 y z
  · exact canonical_group_1_6 y z
lemma base_hull_le_twenty_four : EdgeHull.value base ≤ 24 := by
  rw [← host_false]
  exact host_hull_bound false canonical_all_false
lemma target_hull_le_twenty_four : EdgeHull.value target ≤ 24 := by
  rw [← host_true]
  exact host_hull_bound true canonical_all_true
end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.base_hull_le_twenty_four
#print axioms Erdos184Work.ChainRing.target_hull_le_twenty_four

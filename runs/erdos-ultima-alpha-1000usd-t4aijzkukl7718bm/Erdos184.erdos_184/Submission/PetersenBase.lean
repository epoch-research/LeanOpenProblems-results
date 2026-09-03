import Submission.PetersenCatalogueChecks
import Submission.PetersenCatalogueCheck01
import Submission.PetersenCatalogueCheck02
import Submission.PetersenCatalogueCheck03
import Submission.PetersenCatalogueCheck04
import Submission.PetersenCatalogueCheck05
import Submission.PetersenCatalogueCheck06
import Submission.PetersenCatalogueCheck07
import Submission.PetersenCatalogueCheck08
import Submission.PetersenCatalogueCheck09
import Submission.PetersenCatalogueCheck10
import Submission.PetersenCatalogueCheck11
import Submission.PetersenCatalogueCheck12
import Submission.PetersenCatalogueCheck13
import Submission.PetersenCatalogueCheck14
import Submission.PetersenCatalogueCheck15
import Submission.PetersenCatalogueCheck16
import Submission.PetersenCatalogueCheck17
import Submission.PetersenCatalogueCheck18
import Submission.PetersenCatalogueCheck19
import Submission.PetersenCatalogueCheck20
import Submission.PetersenCatalogueCheck21
import Submission.PetersenCatalogueCheck22
import Submission.PetersenCatalogueCheck23
import Submission.PetersenCatalogueCheck24
import Submission.PetersenCatalogueCheck25
import Submission.PetersenCatalogueCheck26
import Submission.PetersenCatalogueCheck27
import Submission.PetersenCatalogueCheck28
import Submission.PetersenCatalogueCheck29
import Submission.PetersenCatalogueCheck30
import Submission.PetersenCatalogueCheck31

/-! Exhaustiveness of the Petersen simple-cycle catalogue. -/
namespace Erdos184Work.PetersenBase
open Erdos184Serial
set_option maxHeartbeats 2000000
lemma interval0 : FiniteIntervals.Covers ContainsCycle 0 1024 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 0 1024
  simpa only [Nat.zero_add] using check0
lemma interval1 : FiniteIntervals.Covers ContainsCycle 1024 2048 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 1024 1024
  simpa only [Nat.zero_add] using check1
lemma interval2 : FiniteIntervals.Covers ContainsCycle 2048 3072 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 2048 1024
  simpa only [Nat.zero_add] using check2
lemma interval3 : FiniteIntervals.Covers ContainsCycle 3072 4096 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 3072 1024
  simpa only [Nat.zero_add] using check3
lemma interval4 : FiniteIntervals.Covers ContainsCycle 4096 5120 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 4096 1024
  simpa only [Nat.zero_add] using check4
lemma interval5 : FiniteIntervals.Covers ContainsCycle 5120 6144 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 5120 1024
  simpa only [Nat.zero_add] using check5
lemma interval6 : FiniteIntervals.Covers ContainsCycle 6144 7168 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 6144 1024
  simpa only [Nat.zero_add] using check6
lemma interval7 : FiniteIntervals.Covers ContainsCycle 7168 8192 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 7168 1024
  simpa only [Nat.zero_add] using check7
lemma interval8 : FiniteIntervals.Covers ContainsCycle 8192 9216 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 8192 1024
  simpa only [Nat.zero_add] using check8
lemma interval9 : FiniteIntervals.Covers ContainsCycle 9216 10240 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 9216 1024
  simpa only [Nat.zero_add] using check9
lemma interval10 : FiniteIntervals.Covers ContainsCycle 10240 11264 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 10240 1024
  simpa only [Nat.zero_add] using check10
lemma interval11 : FiniteIntervals.Covers ContainsCycle 11264 12288 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 11264 1024
  simpa only [Nat.zero_add] using check11
lemma interval12 : FiniteIntervals.Covers ContainsCycle 12288 13312 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 12288 1024
  simpa only [Nat.zero_add] using check12
lemma interval13 : FiniteIntervals.Covers ContainsCycle 13312 14336 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 13312 1024
  simpa only [Nat.zero_add] using check13
lemma interval14 : FiniteIntervals.Covers ContainsCycle 14336 15360 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 14336 1024
  simpa only [Nat.zero_add] using check14
lemma interval15 : FiniteIntervals.Covers ContainsCycle 15360 16384 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 15360 1024
  simpa only [Nat.zero_add] using check15
lemma interval16 : FiniteIntervals.Covers ContainsCycle 16384 17408 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 16384 1024
  simpa only [Nat.zero_add] using check16
lemma interval17 : FiniteIntervals.Covers ContainsCycle 17408 18432 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 17408 1024
  simpa only [Nat.zero_add] using check17
lemma interval18 : FiniteIntervals.Covers ContainsCycle 18432 19456 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 18432 1024
  simpa only [Nat.zero_add] using check18
lemma interval19 : FiniteIntervals.Covers ContainsCycle 19456 20480 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 19456 1024
  simpa only [Nat.zero_add] using check19
lemma interval20 : FiniteIntervals.Covers ContainsCycle 20480 21504 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 20480 1024
  simpa only [Nat.zero_add] using check20
lemma interval21 : FiniteIntervals.Covers ContainsCycle 21504 22528 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 21504 1024
  simpa only [Nat.zero_add] using check21
lemma interval22 : FiniteIntervals.Covers ContainsCycle 22528 23552 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 22528 1024
  simpa only [Nat.zero_add] using check22
lemma interval23 : FiniteIntervals.Covers ContainsCycle 23552 24576 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 23552 1024
  simpa only [Nat.zero_add] using check23
lemma interval24 : FiniteIntervals.Covers ContainsCycle 24576 25600 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 24576 1024
  simpa only [Nat.zero_add] using check24
lemma interval25 : FiniteIntervals.Covers ContainsCycle 25600 26624 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 25600 1024
  simpa only [Nat.zero_add] using check25
lemma interval26 : FiniteIntervals.Covers ContainsCycle 26624 27648 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 26624 1024
  simpa only [Nat.zero_add] using check26
lemma interval27 : FiniteIntervals.Covers ContainsCycle 27648 28672 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 27648 1024
  simpa only [Nat.zero_add] using check27
lemma interval28 : FiniteIntervals.Covers ContainsCycle 28672 29696 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 28672 1024
  simpa only [Nat.zero_add] using check28
lemma interval29 : FiniteIntervals.Covers ContainsCycle 29696 30720 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 29696 1024
  simpa only [Nat.zero_add] using check29
lemma interval30 : FiniteIntervals.Covers ContainsCycle 30720 31744 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 30720 1024
  simpa only [Nat.zero_add] using check30
lemma interval31 : FiniteIntervals.Covers ContainsCycle 31744 32768 := by
  apply FiniteIntervals.of_fin (P := ContainsCycle) 31744 1024
  simpa only [Nat.zero_add] using check31
lemma interval0_2 : FiniteIntervals.Covers ContainsCycle 0 2048 :=
  FiniteIntervals.merge interval0 interval1
lemma interval2_4 : FiniteIntervals.Covers ContainsCycle 2048 4096 :=
  FiniteIntervals.merge interval2 interval3
lemma interval0_4 : FiniteIntervals.Covers ContainsCycle 0 4096 :=
  FiniteIntervals.merge interval0_2 interval2_4
lemma interval4_6 : FiniteIntervals.Covers ContainsCycle 4096 6144 :=
  FiniteIntervals.merge interval4 interval5
lemma interval6_8 : FiniteIntervals.Covers ContainsCycle 6144 8192 :=
  FiniteIntervals.merge interval6 interval7
lemma interval4_8 : FiniteIntervals.Covers ContainsCycle 4096 8192 :=
  FiniteIntervals.merge interval4_6 interval6_8
lemma interval0_8 : FiniteIntervals.Covers ContainsCycle 0 8192 :=
  FiniteIntervals.merge interval0_4 interval4_8
lemma interval8_10 : FiniteIntervals.Covers ContainsCycle 8192 10240 :=
  FiniteIntervals.merge interval8 interval9
lemma interval10_12 : FiniteIntervals.Covers ContainsCycle 10240 12288 :=
  FiniteIntervals.merge interval10 interval11
lemma interval8_12 : FiniteIntervals.Covers ContainsCycle 8192 12288 :=
  FiniteIntervals.merge interval8_10 interval10_12
lemma interval12_14 : FiniteIntervals.Covers ContainsCycle 12288 14336 :=
  FiniteIntervals.merge interval12 interval13
lemma interval14_16 : FiniteIntervals.Covers ContainsCycle 14336 16384 :=
  FiniteIntervals.merge interval14 interval15
lemma interval12_16 : FiniteIntervals.Covers ContainsCycle 12288 16384 :=
  FiniteIntervals.merge interval12_14 interval14_16
lemma interval8_16 : FiniteIntervals.Covers ContainsCycle 8192 16384 :=
  FiniteIntervals.merge interval8_12 interval12_16
lemma interval0_16 : FiniteIntervals.Covers ContainsCycle 0 16384 :=
  FiniteIntervals.merge interval0_8 interval8_16
lemma interval16_18 : FiniteIntervals.Covers ContainsCycle 16384 18432 :=
  FiniteIntervals.merge interval16 interval17
lemma interval18_20 : FiniteIntervals.Covers ContainsCycle 18432 20480 :=
  FiniteIntervals.merge interval18 interval19
lemma interval16_20 : FiniteIntervals.Covers ContainsCycle 16384 20480 :=
  FiniteIntervals.merge interval16_18 interval18_20
lemma interval20_22 : FiniteIntervals.Covers ContainsCycle 20480 22528 :=
  FiniteIntervals.merge interval20 interval21
lemma interval22_24 : FiniteIntervals.Covers ContainsCycle 22528 24576 :=
  FiniteIntervals.merge interval22 interval23
lemma interval20_24 : FiniteIntervals.Covers ContainsCycle 20480 24576 :=
  FiniteIntervals.merge interval20_22 interval22_24
lemma interval16_24 : FiniteIntervals.Covers ContainsCycle 16384 24576 :=
  FiniteIntervals.merge interval16_20 interval20_24
lemma interval24_26 : FiniteIntervals.Covers ContainsCycle 24576 26624 :=
  FiniteIntervals.merge interval24 interval25
lemma interval26_28 : FiniteIntervals.Covers ContainsCycle 26624 28672 :=
  FiniteIntervals.merge interval26 interval27
lemma interval24_28 : FiniteIntervals.Covers ContainsCycle 24576 28672 :=
  FiniteIntervals.merge interval24_26 interval26_28
lemma interval28_30 : FiniteIntervals.Covers ContainsCycle 28672 30720 :=
  FiniteIntervals.merge interval28 interval29
lemma interval30_32 : FiniteIntervals.Covers ContainsCycle 30720 32768 :=
  FiniteIntervals.merge interval30 interval31
lemma interval28_32 : FiniteIntervals.Covers ContainsCycle 28672 32768 :=
  FiniteIntervals.merge interval28_30 interval30_32
lemma interval24_32 : FiniteIntervals.Covers ContainsCycle 24576 32768 :=
  FiniteIntervals.merge interval24_28 interval28_32
lemma interval16_32 : FiniteIntervals.Covers ContainsCycle 16384 32768 :=
  FiniteIntervals.merge interval16_24 interval24_32
lemma interval0_32 : FiniteIntervals.Covers ContainsCycle 0 32768 :=
  FiniteIntervals.merge interval0_16 interval16_32
lemma catalogue (a : Finset (Fin 15)) (ha : Circuit code a) : ∃ i, a = edges i := by
  obtain ⟨j,hj⟩ := FinsetMask.exists_word a
  have hh := interval0_32 j.val (Nat.zero_le _) j.isLt
  unfold ContainsCycle at hh
  rw [hj] at hh
  obtain ⟨i,hi⟩ := hh ha.2.1 ha.1
  exact ⟨i,(ha.2.2 _ hi (edges_circuit i).1 (edges_circuit i).2.1).symm⟩
#print axioms catalogue
end Erdos184Work.PetersenBase

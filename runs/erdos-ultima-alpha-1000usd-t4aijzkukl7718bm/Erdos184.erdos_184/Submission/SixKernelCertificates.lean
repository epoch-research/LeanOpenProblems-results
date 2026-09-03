import Submission.LabelCycleCertificates

/-! Compact kernel-level certificates for thirteen six-cycle layouts.
There is no assertion here that the thirteen layouts form a complete list. -/
namespace Erdos184Work.SixKernelCertificates
open LabelKernel Erdos184Serial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace Layout0
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,5,10,11,2,6,13,9,12,3,7,10,12,14,4,11,13,8,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,5,10,11,1,6,13,9,12,2,7,10,12,14,3,11,13,8,14,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,25,26,17,11,6,7,21,22,23,28,9]
  vertex := ![0,1,3,2,4,11,13,9,5,6,7,10,12,14,8]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,29,24,20,8,27,16,15,19,18,10,14,13,12,5]
  vertex := ![0,4,14,3,7,8,13,6,2,12,9,1,11,10,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout0
namespace Layout1
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,14,8,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,25,12,11,17,16,7,21,22,23,27,9]
  vertex := ![0,1,3,2,4,11,5,9,13,6,7,10,12,14,8]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,29,28,8,20,24,26,13,14,10,18,19,15,6,5]
  vertex := ![0,4,13,8,7,3,14,11,10,1,9,12,2,6,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout1
namespace Layout2
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,11,14,8,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,25,12,13,21,7,16,17,18,23,27,9]
  vertex := ![0,1,3,2,4,11,5,10,7,6,9,13,12,14,8]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,29,28,8,20,24,26,11,10,14,22,19,15,6,5]
  vertex := ![0,4,13,8,7,3,14,11,9,1,10,12,2,6,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout2
namespace Layout3
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,13,8,11,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,13,8,11,14,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,29,23,18,17,16,7,21,13,12,27,9]
  vertex := ![0,1,3,2,4,14,12,13,9,6,7,10,5,11,8]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,25,26,8,20,24,28,11,10,14,22,19,15,6,5]
  vertex := ![0,4,13,8,7,3,14,11,9,1,10,12,2,6,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout3
namespace Layout4
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,8,7,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,13,8,11,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,8,7,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,13,8,11,14,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,29,23,18,26,27,11,16,6,13,21,9]
  vertex := ![0,1,3,2,4,14,12,13,8,11,9,6,5,10,7]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,25,17,10,14,22,19,15,7,8,20,24,28,12,5]
  vertex := ![0,4,13,9,1,10,12,2,6,8,7,3,14,11,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout4
namespace Layout5
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,8,6,7,1,9,5,10,11,2,6,9,13,12,3,12,10,7,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,8,6,7,0,9,5,10,11,1,6,9,13,12,2,12,10,7,14,3,11,8,14,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,19,18,17,16,8,23,27,6,12,13,25,4]
  vertex := ![0,1,3,2,12,13,9,6,7,14,8,5,10,11,4]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![5,11,10,14,26,7,15,3,29,28,24,20,21,22,9]
  vertex := ![0,5,9,1,11,8,6,2,4,13,14,3,12,10,7]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout5
namespace Layout6
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,8,6,7,1,9,5,10,11,2,6,13,9,12,3,7,10,12,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,8,6,7,0,9,5,10,11,1,6,13,9,12,2,7,10,12,14,3,11,8,14,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,25,13,22,23,28,17,11,6,7,8,9]
  vertex := ![0,1,3,2,4,11,10,12,14,13,9,5,8,6,7]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,29,16,15,19,18,10,14,26,27,24,20,21,12,5]
  vertex := ![0,4,13,6,2,12,9,1,11,8,14,3,7,10,5]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout6
namespace Layout7
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,8,14,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,19,18,17,28,27,26,13,21,7,6,5]
  vertex := ![0,1,3,4,2,12,9,13,14,8,11,10,7,6,5]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,15,16,29,25,12,11,10,14,22,23,24,20,8,9]
  vertex := ![0,2,6,13,4,11,5,9,1,10,12,14,3,7,8]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout7
namespace Layout8
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,14,8,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,25,12,11,17,28,27,23,22,21,7,15,4]
  vertex := ![0,1,3,4,11,5,9,13,8,14,12,10,7,6,2]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![5,6,16,29,3,19,18,10,14,13,26,24,20,8,9]
  vertex := ![0,5,6,13,4,2,12,9,1,10,11,14,3,7,8]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout8
namespace Layout9
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,8,6,7,1,9,5,10,11,2,6,13,9,12,3,12,10,7,14,4,8,14,13,11]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,8,6,7,0,9,5,10,11,1,6,13,9,12,2,12,10,7,14,3,8,14,13,11,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,25,26,27,28,13,22,8,15,19,18,11,5]
  vertex := ![0,1,3,4,8,14,13,11,10,7,6,2,12,9,5]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,3,29,14,10,17,16,7,6,12,21,20,24,23,9]
  vertex := ![0,2,4,11,1,9,13,6,8,5,10,12,3,14,7]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout9
namespace Layout10
def src : Fin 30 → Fin 15 := ![0,1,2,3,4,0,5,6,8,7,1,9,10,5,11,2,6,12,9,13,3,10,7,14,12,4,8,11,14,13]
def dst : Fin 30 → Fin 15 := ![1,2,3,4,0,5,6,8,7,0,9,10,5,11,1,6,12,9,13,2,10,7,14,12,3,8,11,14,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,24,16,6,13,27,28,18,11,21,8,25,4]
  vertex := ![0,1,2,3,12,6,5,11,14,13,9,10,7,8,4]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![5,12,20,3,29,19,15,7,26,14,10,17,23,22,9]
  vertex := ![0,5,10,3,4,13,2,6,8,11,1,9,12,14,7]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout10
namespace Layout11
def src : Fin 30 → Fin 15 := ![0,1,2,3,4,0,7,6,5,8,1,9,10,5,11,2,6,12,9,13,3,10,7,14,12,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,2,3,4,0,7,6,5,8,0,9,10,5,11,1,6,12,9,13,2,10,7,14,12,3,11,14,8,13,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,24,16,7,8,27,26,25,29,18,11,21,5]
  vertex := ![0,1,2,3,12,6,5,8,14,11,4,13,9,10,7]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,3,20,12,13,14,10,17,23,22,6,15,19,28,9]
  vertex := ![0,4,3,10,5,11,1,9,12,14,7,6,2,13,8]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout11
namespace Layout12
def src : Fin 30 → Fin 15 := ![0,1,2,4,3,0,7,6,5,8,1,5,11,10,9,2,6,12,9,13,3,10,7,14,12,4,8,14,13,11]
def dst : Fin 30 → Fin 15 := ![1,2,4,3,0,7,6,5,8,0,5,11,10,9,1,6,12,9,13,2,10,7,14,12,3,8,14,13,11,4]
def red : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![0,1,2,3,20,12,28,18,17,23,26,8,7,6,5]
  vertex := ![0,1,2,4,3,10,11,13,9,12,14,8,5,6,7]
def blue : CycleData (Fin 30) (Fin 15) where
  size := 13
  edge := ![4,24,16,15,19,27,22,21,13,14,10,11,29,25,9]
  vertex := ![0,3,12,6,2,13,14,7,10,9,1,5,11,4,8]
def certificate : PartitionData (Fin 30) (Fin 15) where
  size := 2
  cycle := ![red,blue]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma exists_two : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout12
def sourceTable : Fin 13 → Fin 30 → Fin 15 := ![Layout0.src,Layout1.src,Layout2.src,Layout3.src,Layout4.src,Layout5.src,Layout6.src,Layout7.src,Layout8.src,Layout9.src,Layout10.src,Layout11.src,Layout12.src]
def targetTable : Fin 13 → Fin 30 → Fin 15 := ![Layout0.dst,Layout1.dst,Layout2.dst,Layout3.dst,Layout4.dst,Layout5.dst,Layout6.dst,Layout7.dst,Layout8.dst,Layout9.dst,Layout10.dst,Layout11.dst,Layout12.dst]
lemma exists_two (k : Fin 13) : ∃ P, Partition (code (sourceTable k) (targetTable k)) Finset.univ P ∧ P.card = 2 := by
  fin_cases k
  · exact Layout0.exists_two
  · exact Layout1.exists_two
  · exact Layout2.exists_two
  · exact Layout3.exists_two
  · exact Layout4.exists_two
  · exact Layout5.exists_two
  · exact Layout6.exists_two
  · exact Layout7.exists_two
  · exact Layout8.exists_two
  · exact Layout9.exists_two
  · exact Layout10.exists_two
  · exact Layout11.exists_two
  · exact Layout12.exists_two
#print axioms exists_two
end Erdos184Work.SixKernelCertificates

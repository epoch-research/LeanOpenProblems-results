import Submission.LabelCycleCertificates

/-! Checked alternatives for forty-seven four-cycle kernel representatives.
Each either has two circuits or has more than four circuits in a partition.
No assertion of completeness of the representative list is made in this file. -/
namespace Erdos184Work.FourKernelCertificates
open LabelKernel Erdos184Serial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Layout0
def src : Fin 16 → Fin 8 := ![0,2,1,3,4,6,5,7,0,4,1,5,2,6,3,7]
def dst : Fin 16 → Fin 8 := ![2,1,3,0,6,5,7,4,4,1,5,0,6,3,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![11,6,7,4,13,2,1,0]
  vertex := ![0,5,7,4,6,3,1,2]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![8,9,10,5,12,15,14,3]
  vertex := ![0,4,1,5,6,2,7,3]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout0
namespace Layout1
def src : Fin 18 → Fin 9 := ![0,2,1,3,4,6,5,7,0,4,1,5,8,2,6,3,7,8]
def dst : Fin 18 → Fin 9 := ![2,1,3,0,6,5,7,4,4,1,5,8,0,6,3,7,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![12,17,0]
  vertex := ![0,8,2]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![9,4,13,1]
  vertex := ![1,4,6,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![10,5,14,2]
  vertex := ![1,5,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![8,7,15,3]
  vertex := ![0,4,7,3]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,16,6]
  vertex := ![5,8,7]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout1
namespace Layout2
def src : Fin 12 → Fin 6 := ![0,1,2,0,3,4,1,3,5,2,4,5]
def dst : Fin 12 → Fin 6 := ![1,2,0,3,4,0,3,5,1,4,5,2]
def part0 : CycleData (Fin 12) (Fin 6) where
  size := 4
  edge := ![3,7,10,9,1,0]
  vertex := ![0,3,5,4,2,1]
def part1 : CycleData (Fin 12) (Fin 6) where
  size := 4
  edge := ![5,4,6,8,11,2]
  vertex := ![0,4,3,1,5,2]
def certificate : PartitionData (Fin 12) (Fin 6) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout2
namespace Layout3
def src : Fin 14 → Fin 7 := ![0,1,2,0,3,4,1,3,5,6,2,4,5,6]
def dst : Fin 14 → Fin 7 := ![1,2,0,3,4,0,3,5,6,1,4,5,6,2]
def part0 : CycleData (Fin 14) (Fin 7) where
  size := 1
  edge := ![3,6,0]
  vertex := ![0,3,1]
def part1 : CycleData (Fin 14) (Fin 7) where
  size := 1
  edge := ![9,13,1]
  vertex := ![1,6,2]
def part2 : CycleData (Fin 14) (Fin 7) where
  size := 1
  edge := ![5,10,2]
  vertex := ![0,4,2]
def part3 : CycleData (Fin 14) (Fin 7) where
  size := 1
  edge := ![7,11,4]
  vertex := ![3,5,4]
def part4 : CycleData (Fin 14) (Fin 7) where
  size := 0
  edge := ![12,8]
  vertex := ![5,6]
def certificate : PartitionData (Fin 14) (Fin 7) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout3
namespace Layout4
def src : Fin 14 → Fin 7 := ![0,1,2,0,3,4,1,3,5,6,2,4,6,5]
def dst : Fin 14 → Fin 7 := ![1,2,0,3,4,0,3,5,6,1,4,6,5,2]
def part0 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![3,7,8,11,10,1,0]
  vertex := ![0,3,5,6,4,2,1]
def part1 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![5,4,6,9,12,13,2]
  vertex := ![0,4,3,1,6,5,2]
def certificate : PartitionData (Fin 14) (Fin 7) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout4
namespace Layout5
def src : Fin 14 → Fin 7 := ![0,1,2,0,3,4,1,3,5,6,2,5,4,6]
def dst : Fin 14 → Fin 7 := ![1,2,0,3,4,0,3,5,6,1,5,4,6,2]
def part0 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![3,4,12,8,10,1,0]
  vertex := ![0,3,4,6,5,2,1]
def part1 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![5,11,7,6,9,13,2]
  vertex := ![0,4,5,3,1,6,2]
def certificate : PartitionData (Fin 14) (Fin 7) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout5
namespace Layout6
def src : Fin 14 → Fin 7 := ![0,1,2,0,3,4,1,5,3,6,2,5,4,6]
def dst : Fin 14 → Fin 7 := ![1,2,0,3,4,0,5,3,6,1,5,4,6,2]
def part0 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![5,12,8,7,10,1,0]
  vertex := ![0,4,6,3,5,2,1]
def part1 : CycleData (Fin 14) (Fin 7) where
  size := 5
  edge := ![3,4,11,6,9,13,2]
  vertex := ![0,3,4,5,1,6,2]
def certificate : PartitionData (Fin 14) (Fin 7) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout6
namespace Layout7
def src : Fin 16 → Fin 8 := ![0,1,2,0,3,4,5,1,3,6,7,2,4,6,5,7]
def dst : Fin 16 → Fin 8 := ![1,2,0,3,4,5,0,3,6,7,1,4,6,5,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![3,7,0]
  vertex := ![0,3,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,15,1]
  vertex := ![1,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![6,5,11,2]
  vertex := ![0,5,4,2]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![8,12,4]
  vertex := ![3,6,4]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![14,9,13]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout7
namespace Layout8
def src : Fin 16 → Fin 8 := ![0,1,2,0,3,4,5,1,3,6,7,2,4,7,5,6]
def dst : Fin 16 → Fin 8 := ![1,2,0,3,4,5,0,3,6,7,1,4,7,5,6,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![6,13,9,8,4,11,1,0]
  vertex := ![0,5,7,6,3,4,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![3,7,10,12,5,14,15,2]
  vertex := ![0,3,1,7,4,5,6,2]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout8
namespace Layout9
def src : Fin 16 → Fin 8 := ![0,1,2,0,3,4,5,1,3,6,7,2,5,6,4,7]
def dst : Fin 16 → Fin 8 := ![1,2,0,3,4,5,0,3,6,7,1,5,6,4,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![3,7,0]
  vertex := ![0,3,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,15,1]
  vertex := ![1,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![6,11,2]
  vertex := ![0,5,2]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![8,12,5,4]
  vertex := ![3,6,5,4]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![14,9,13]
  vertex := ![4,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout9
namespace Layout10
def src : Fin 16 → Fin 8 := ![0,1,2,0,3,4,5,1,6,3,7,2,4,6,5,7]
def dst : Fin 16 → Fin 8 := ![1,2,0,3,4,5,0,6,3,7,1,4,6,5,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![6,14,9,8,12,11,1,0]
  vertex := ![0,5,7,3,6,4,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![3,4,5,13,7,10,15,2]
  vertex := ![0,3,4,5,6,1,7,2]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout10
namespace Layout11
def src : Fin 16 → Fin 8 := ![0,1,2,0,3,4,5,1,6,3,7,2,5,6,4,7]
def dst : Fin 16 → Fin 8 := ![1,2,0,3,4,5,0,6,3,7,1,5,6,4,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![3,8,7,0]
  vertex := ![0,3,6,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,15,1]
  vertex := ![1,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![6,11,2]
  vertex := ![0,5,2]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![9,14,4]
  vertex := ![3,7,4]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![13,12,5]
  vertex := ![4,6,5]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout11
namespace Layout12
def src : Fin 16 → Fin 8 := ![0,1,2,0,4,3,5,1,6,3,7,2,4,6,5,7]
def dst : Fin 16 → Fin 8 := ![1,2,0,4,3,5,0,6,3,7,1,4,6,5,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![6,13,7,0]
  vertex := ![0,5,6,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,15,1]
  vertex := ![1,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![3,11,2]
  vertex := ![0,4,2]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![8,12,4]
  vertex := ![3,6,4]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![9,14,5]
  vertex := ![3,7,5]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout12
namespace Layout13
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,8,2,5,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,8,1,5,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 3
  edge := ![11,10,14,2,1]
  vertex := ![1,8,7,3,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,13,5]
  vertex := ![4,7,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,16,6,12]
  vertex := ![2,8,6,5]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout13
namespace Layout14
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,8,2,5,8,3,6,7]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,8,1,5,8,3,6,7,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![11,14,2,1]
  vertex := ![1,8,3,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,9,5,12]
  vertex := ![2,7,4,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![13,10,16,6]
  vertex := ![5,8,7,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout14
namespace Layout15
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,7,4,8,2,5,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,7,4,8,1,5,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,9,8,0]
  vertex := ![0,4,7,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,17,1]
  vertex := ![1,8,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,13,14,2]
  vertex := ![2,5,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![10,16,6,5]
  vertex := ![4,8,6,5]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout15
namespace Layout16
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,7,4,8,2,6,7,3,5,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,7,4,8,1,6,7,3,5,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,9,8,0]
  vertex := ![0,4,7,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,17,1]
  vertex := ![1,8,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,12,2,3]
  vertex := ![0,6,2,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,16,5]
  vertex := ![4,8,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![15,6,13,14]
  vertex := ![3,5,6,7]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout16
namespace Layout17
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,5,4,6,1,7,4,8,2,5,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,5,4,6,0,7,4,8,1,5,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,12,1,0]
  vertex := ![0,5,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 3
  edge := ![11,17,2,14,8]
  vertex := ![1,8,2,3,7]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,13,5]
  vertex := ![4,7,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,16,6]
  vertex := ![4,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout17
namespace Layout18
def src : Fin 18 → Fin 9 := ![0,2,1,3,0,5,4,6,1,7,4,8,2,5,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![2,1,3,0,5,4,6,0,7,4,8,1,5,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,12,0]
  vertex := ![0,5,2]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,17,1]
  vertex := ![1,8,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![8,14,2]
  vertex := ![1,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,13,5]
  vertex := ![4,7,5]
def part5 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,16,6]
  vertex := ![4,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout18
namespace Layout19
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,4,5,7,2,3,6,7]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,4,5,7,1,3,6,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![11,15,1]
  vertex := ![1,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![7,13,3]
  vertex := ![0,6,3]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![9,5]
  vertex := ![4,5]
def part5 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout19
namespace Layout20
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,4,5,7,2,3,7,6]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,4,5,7,1,3,7,6,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![7,15,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 3
  edge := ![4,8,11,13,3]
  vertex := ![0,4,1,7,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![9,5]
  vertex := ![4,5]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout20
namespace Layout21
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,4,5,7,2,6,3,7]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,4,5,7,1,6,3,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![11,14,2,1]
  vertex := ![1,7,3,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![7,13,3]
  vertex := ![0,6,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![9,5]
  vertex := ![4,5]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![15,10,6,12]
  vertex := ![2,7,5,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout21
namespace Layout22
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,4,7,5,2,3,7,6]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,4,7,5,1,3,7,6,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![7,15,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![4,9,13,3]
  vertex := ![0,4,7,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![11,5,8]
  vertex := ![1,5,4]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![10,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout22
namespace Layout23
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,4,7,5,2,6,3,7]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,4,7,5,1,6,3,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![11,6,12,1]
  vertex := ![1,5,6,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![15,14,2]
  vertex := ![2,7,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![7,13,3]
  vertex := ![0,6,3]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![9,10,5]
  vertex := ![4,7,5]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout23
namespace Layout24
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,5,6,1,5,4,7,2,3,7,6]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,5,6,0,5,4,7,1,3,7,6,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![7,15,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![4,10,13,3]
  vertex := ![0,4,7,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![9,5]
  vertex := ![4,5]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![11,14,6,8]
  vertex := ![1,7,6,5]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout24
namespace Layout25
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,6,5,1,4,7,5,2,3,6,7]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,6,5,0,4,7,5,1,3,6,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![11,10,15,1]
  vertex := ![1,5,7,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![7,6,13,3]
  vertex := ![0,5,6,3]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![9,14,5]
  vertex := ![4,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout25
namespace Layout26
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,6,5,1,4,7,5,2,3,7,6]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,6,5,0,4,7,5,1,3,7,6,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![11,6,15,1]
  vertex := ![1,5,6,2]
def part2 : CycleData (Fin 16) (Fin 8) where
  size := 0
  edge := ![12,2]
  vertex := ![2,3]
def part3 : CycleData (Fin 16) (Fin 8) where
  size := 2
  edge := ![7,10,13,3]
  vertex := ![0,5,7,3]
def part4 : CycleData (Fin 16) (Fin 8) where
  size := 1
  edge := ![9,14,5]
  vertex := ![4,7,6]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout26
namespace Layout27
def src : Fin 16 → Fin 8 := ![0,1,2,3,0,4,6,5,1,4,7,5,2,6,3,7]
def dst : Fin 16 → Fin 8 := ![1,2,3,0,4,6,5,0,4,7,5,1,6,3,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![7,10,9,5,13,2,1,0]
  vertex := ![0,5,7,4,6,3,2,1]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![4,8,11,6,12,15,14,3]
  vertex := ![0,4,1,5,6,2,7,3]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout27
namespace Layout28
def src : Fin 16 → Fin 8 := ![0,2,1,3,0,4,6,5,1,4,7,5,2,6,3,7]
def dst : Fin 16 → Fin 8 := ![2,1,3,0,4,6,5,0,4,7,5,1,6,3,7,2]
def part0 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![7,10,9,5,13,2,1,0]
  vertex := ![0,5,7,4,6,3,1,2]
def part1 : CycleData (Fin 16) (Fin 8) where
  size := 6
  edge := ![4,8,11,6,12,15,14,3]
  vertex := ![0,4,1,5,6,2,7,3]
def certificate : PartitionData (Fin 16) (Fin 8) where
  size := 2
  cycle := ![part0,part1]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 2 :=
  PartitionData.exists_partition certificate_valid
end Layout28
namespace Layout29
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,5,8,2,6,7,3,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,5,8,1,6,7,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,13,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![17,16,2]
  vertex := ![2,8,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,9,15,3]
  vertex := ![0,4,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,11,5,8]
  vertex := ![1,8,5,4]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout29
namespace Layout30
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,5,8,2,6,8,3,7]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,5,8,1,6,8,3,7,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,13,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![17,16,2]
  vertex := ![2,7,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 3
  edge := ![4,8,12,15,3]
  vertex := ![0,4,1,8,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,10,5]
  vertex := ![4,7,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,14,6]
  vertex := ![5,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout30
namespace Layout31
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,5,8,2,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,5,8,1,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![12,17,1]
  vertex := ![1,8,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![13,14,2]
  vertex := ![2,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,10,5]
  vertex := ![4,7,5]
def part5 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,16,6]
  vertex := ![5,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout31
namespace Layout32
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,4,7,5,8,2,7,6,3,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,4,7,5,8,1,7,6,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 3
  edge := ![4,9,13,1,0]
  vertex := ![0,4,7,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![17,16,2]
  vertex := ![2,8,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![7,15,3]
  vertex := ![0,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,11,5,8]
  vertex := ![1,8,5,4]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout32
namespace Layout33
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,5,7,4,8,2,6,7,3,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,5,7,4,8,1,6,7,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,13,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![17,16,2]
  vertex := ![2,8,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,10,15,3]
  vertex := ![0,4,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,11,5,8]
  vertex := ![1,8,4,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,14,6]
  vertex := ![5,7,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout33
namespace Layout34
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,5,6,1,5,7,4,8,2,6,8,3,7]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,5,6,0,5,7,4,8,1,6,8,3,7,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,13,1,0]
  vertex := ![0,6,2,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![17,16,2]
  vertex := ![2,7,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,11,15,3]
  vertex := ![0,4,8,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![10,9,5]
  vertex := ![4,7,5]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,14,6,8]
  vertex := ![1,8,6,5]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout34
namespace Layout35
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,6,5,1,4,7,5,8,2,6,7,3,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,6,5,0,4,7,5,8,1,6,7,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,16,2,1]
  vertex := ![1,8,3,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,10,15,3]
  vertex := ![0,5,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,14,5]
  vertex := ![4,7,6]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,11,6,13]
  vertex := ![2,8,5,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout35
namespace Layout36
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,6,5,1,4,7,5,8,2,6,8,3,7]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,6,5,0,4,7,5,8,1,6,8,3,7,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,15,2,1]
  vertex := ![1,8,3,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,10,16,3]
  vertex := ![0,5,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,9,5,13]
  vertex := ![2,7,4,6]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,14,6]
  vertex := ![5,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout36
namespace Layout37
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,6,5,1,4,7,5,8,2,7,3,6,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,6,5,0,4,7,5,8,1,7,3,6,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![12,17,1]
  vertex := ![1,8,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 3
  edge := ![7,10,13,2,3]
  vertex := ![0,5,7,2,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![15,5,9,14]
  vertex := ![3,6,4,7]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,16,6]
  vertex := ![5,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout37
namespace Layout38
def src : Fin 18 → Fin 9 := ![0,1,2,3,0,4,6,5,1,4,7,5,8,2,7,6,3,8]
def dst : Fin 18 → Fin 9 := ![1,2,3,0,4,6,5,0,4,7,5,8,1,7,6,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![4,8,0]
  vertex := ![0,4,1]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![12,16,2,1]
  vertex := ![1,8,3,2]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,6,15,3]
  vertex := ![0,5,6,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,14,5]
  vertex := ![4,7,6]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,11,10,13]
  vertex := ![2,8,5,7]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout38
namespace Layout39
def src : Fin 18 → Fin 9 := ![0,2,1,3,0,4,6,5,1,4,7,5,8,2,6,7,3,8]
def dst : Fin 18 → Fin 9 := ![2,1,3,0,4,6,5,0,4,7,5,8,1,6,7,3,8,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,8,1,0]
  vertex := ![0,4,1,2]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![12,16,2]
  vertex := ![1,8,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,10,15,3]
  vertex := ![0,5,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![9,14,5]
  vertex := ![4,7,6]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,11,6,13]
  vertex := ![2,8,5,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout39
namespace Layout40
def src : Fin 18 → Fin 9 := ![0,2,1,3,0,4,6,5,1,4,7,5,8,2,6,8,3,7]
def dst : Fin 18 → Fin 9 := ![2,1,3,0,4,6,5,0,4,7,5,8,1,6,8,3,7,2]
def part0 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![4,8,1,0]
  vertex := ![0,4,1,2]
def part1 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![12,15,2]
  vertex := ![1,8,3]
def part2 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![7,10,16,3]
  vertex := ![0,5,7,3]
def part3 : CycleData (Fin 18) (Fin 9) where
  size := 2
  edge := ![17,9,5,13]
  vertex := ![2,7,4,6]
def part4 : CycleData (Fin 18) (Fin 9) where
  size := 1
  edge := ![11,14,6]
  vertex := ![5,8,6]
def certificate : PartitionData (Fin 18) (Fin 9) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout40
namespace Layout41
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,5,2,6,9,3,7,4,8,9]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,5,2,6,9,1,7,4,8,9,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![5,10,0]
  vertex := ![0,5,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![14,19,1]
  vertex := ![1,9,3]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![11,6,15,2]
  vertex := ![2,5,7,3]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![12,7,16,3]
  vertex := ![2,6,7,4]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![9,17,4]
  vertex := ![0,8,4]
def part5 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![13,18,8]
  vertex := ![6,9,8]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout41
namespace Layout42
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,5,2,6,9,3,7,4,9,8]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,5,2,6,9,1,7,4,9,8,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![9,19,1,0]
  vertex := ![0,8,3,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![11,6,15,2]
  vertex := ![2,5,7,3]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![12,7,16,3]
  vertex := ![2,6,7,4]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 3
  edge := ![5,10,14,17,4]
  vertex := ![0,5,1,9,4]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![13,18,8]
  vertex := ![6,9,8]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout42
namespace Layout43
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,5,2,6,9,3,7,9,4,8]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,5,2,6,9,1,7,9,4,8,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 3
  edge := ![5,11,2,1,0]
  vertex := ![0,5,2,3,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![12,13,17,3]
  vertex := ![2,6,9,4]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![9,18,4]
  vertex := ![0,8,4]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![14,16,6,10]
  vertex := ![1,9,7,5]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![19,8,7,15]
  vertex := ![3,8,6,7]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout43
namespace Layout44
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,5,2,6,9,3,8,4,7,9]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,5,2,6,9,1,8,4,7,9,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![5,10,0]
  vertex := ![0,5,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![14,19,1]
  vertex := ![1,9,3]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![12,8,15,2]
  vertex := ![2,6,8,3]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![11,6,17,3]
  vertex := ![2,5,7,4]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![9,16,4]
  vertex := ![0,8,4]
def part5 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![13,18,7]
  vertex := ![6,9,7]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout44
namespace Layout45
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,5,2,9,6,3,8,4,7,9]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,5,2,9,6,1,8,4,7,9,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![5,10,0]
  vertex := ![0,5,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![14,8,15,1]
  vertex := ![1,6,8,3]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![12,19,2]
  vertex := ![2,9,3]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![11,6,17,3]
  vertex := ![2,5,7,4]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![9,16,4]
  vertex := ![0,8,4]
def part5 : CycleData (Fin 20) (Fin 10) where
  size := 1
  edge := ![13,18,7]
  vertex := ![6,9,7]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 6
  cycle := ![part0,part1,part2,part3,part4,part5]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 6 :=
  PartitionData.exists_partition certificate_valid
end Layout45
namespace Layout46
def src : Fin 20 → Fin 10 := ![0,1,3,2,4,0,5,7,6,8,1,6,2,5,9,3,7,4,9,8]
def dst : Fin 20 → Fin 10 := ![1,3,2,4,0,5,7,6,8,0,6,2,5,9,1,7,4,9,8,3]
def part0 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![9,19,1,0]
  vertex := ![0,8,3,1]
def part1 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![12,6,15,2]
  vertex := ![2,5,7,3]
def part2 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![11,7,16,3]
  vertex := ![2,6,7,4]
def part3 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![5,13,17,4]
  vertex := ![0,5,9,4]
def part4 : CycleData (Fin 20) (Fin 10) where
  size := 2
  edge := ![14,18,8,10]
  vertex := ![1,9,8,6]
def certificate : PartitionData (Fin 20) (Fin 10) where
  size := 5
  cycle := ![part0,part1,part2,part3,part4]
lemma certificate_valid : certificate.Valid src dst Finset.univ := by decide
lemma partition_count : ∃ P, Partition (code src dst) Finset.univ P ∧ P.card = 5 :=
  PartitionData.exists_partition certificate_valid
end Layout46
def junctions : Fin 47 → ℕ := ![8,9,6,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,8,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9,9,9,9,10,10,10,10,10,10]
def srcTable : (k : Fin 47) → Fin (2 * junctions k) → Fin (junctions k) :=
  (Fin.cases Layout0.src (Fin.cases Layout1.src (Fin.cases Layout2.src (Fin.cases Layout3.src (Fin.cases Layout4.src (Fin.cases Layout5.src (Fin.cases Layout6.src (Fin.cases Layout7.src (Fin.cases Layout8.src (Fin.cases Layout9.src (Fin.cases Layout10.src (Fin.cases Layout11.src (Fin.cases Layout12.src (Fin.cases Layout13.src (Fin.cases Layout14.src (Fin.cases Layout15.src (Fin.cases Layout16.src (Fin.cases Layout17.src (Fin.cases Layout18.src (Fin.cases Layout19.src (Fin.cases Layout20.src (Fin.cases Layout21.src (Fin.cases Layout22.src (Fin.cases Layout23.src (Fin.cases Layout24.src (Fin.cases Layout25.src (Fin.cases Layout26.src (Fin.cases Layout27.src (Fin.cases Layout28.src (Fin.cases Layout29.src (Fin.cases Layout30.src (Fin.cases Layout31.src (Fin.cases Layout32.src (Fin.cases Layout33.src (Fin.cases Layout34.src (Fin.cases Layout35.src (Fin.cases Layout36.src (Fin.cases Layout37.src (Fin.cases Layout38.src (Fin.cases Layout39.src (Fin.cases Layout40.src (Fin.cases Layout41.src (Fin.cases Layout42.src (Fin.cases Layout43.src (Fin.cases Layout44.src (Fin.cases Layout45.src (Fin.cases Layout46.src (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))
def dstTable : (k : Fin 47) → Fin (2 * junctions k) → Fin (junctions k) :=
  (Fin.cases Layout0.dst (Fin.cases Layout1.dst (Fin.cases Layout2.dst (Fin.cases Layout3.dst (Fin.cases Layout4.dst (Fin.cases Layout5.dst (Fin.cases Layout6.dst (Fin.cases Layout7.dst (Fin.cases Layout8.dst (Fin.cases Layout9.dst (Fin.cases Layout10.dst (Fin.cases Layout11.dst (Fin.cases Layout12.dst (Fin.cases Layout13.dst (Fin.cases Layout14.dst (Fin.cases Layout15.dst (Fin.cases Layout16.dst (Fin.cases Layout17.dst (Fin.cases Layout18.dst (Fin.cases Layout19.dst (Fin.cases Layout20.dst (Fin.cases Layout21.dst (Fin.cases Layout22.dst (Fin.cases Layout23.dst (Fin.cases Layout24.dst (Fin.cases Layout25.dst (Fin.cases Layout26.dst (Fin.cases Layout27.dst (Fin.cases Layout28.dst (Fin.cases Layout29.dst (Fin.cases Layout30.dst (Fin.cases Layout31.dst (Fin.cases Layout32.dst (Fin.cases Layout33.dst (Fin.cases Layout34.dst (Fin.cases Layout35.dst (Fin.cases Layout36.dst (Fin.cases Layout37.dst (Fin.cases Layout38.dst (Fin.cases Layout39.dst (Fin.cases Layout40.dst (Fin.cases Layout41.dst (Fin.cases Layout42.dst (Fin.cases Layout43.dst (Fin.cases Layout44.dst (Fin.cases Layout45.dst (Fin.cases Layout46.dst (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))
def good : Finset (Fin 47) := {0,2,4,5,6,8,10,27,28}
lemma alternative (k : Fin 47) : ∃ P,
    Partition (code (srcTable k) (dstTable k)) Finset.univ P ∧
      ((k ∈ good ∧ P.card = 2) ∨ (k ∉ good ∧ 4 < P.card)) := by
  fin_cases k
  · obtain ⟨P,hP,hc⟩ := Layout0.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout1.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout2.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout3.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout4.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout5.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout6.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout7.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout8.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout9.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout10.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout11.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout12.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout13.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout14.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout15.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout16.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout17.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout18.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout19.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout20.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout21.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout22.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout23.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout24.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout25.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout26.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout27.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout28.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inl ⟨by decide,hc⟩
  · obtain ⟨P,hP,hc⟩ := Layout29.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout30.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout31.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout32.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout33.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout34.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout35.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout36.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout37.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout38.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout39.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout40.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout41.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout42.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout43.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout44.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout45.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
  · obtain ⟨P,hP,hc⟩ := Layout46.partition_count
    refine ⟨P,hP,?_⟩
    exact Or.inr ⟨by decide,by omega⟩
lemma good_of_maximum_bound (k : Fin 47)
    (hb : ∀ P, Partition (code (srcTable k) (dstTable k)) Finset.univ P → P.card ≤ 4) :
    k ∈ good := by
  obtain ⟨P,hP,h⟩ := alternative k
  rcases h with ⟨hk,_⟩ | ⟨_,hc⟩
  · exact hk
  · have hh := hb P hP
    omega
lemma exists_two_of_maximum_bound (k : Fin 47)
    (hb : ∀ P, Partition (code (srcTable k) (dstTable k)) Finset.univ P → P.card ≤ 4) :
    ∃ P, Partition (code (srcTable k) (dstTable k)) Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,h⟩ := alternative k
  rcases h with ⟨_,hc⟩ | ⟨_,hc⟩
  · exact ⟨P,hP,hc⟩
  · have hh := hb P hP
    omega
#print axioms exists_two_of_maximum_bound
end Erdos184Work.FourKernelCertificates

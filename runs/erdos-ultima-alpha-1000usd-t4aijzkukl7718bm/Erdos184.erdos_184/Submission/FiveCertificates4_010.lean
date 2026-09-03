import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src500 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,28,39,18,38]
def dst500 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle500_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle500_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle500_2 : CycleData E W := ⟨3,![4,21,22,18,11],![4,8,28,39,26]⟩
def cycle500_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,38,6,16]⟩
def cycle500_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,38,26]⟩
def cycle500_5 : CycleData E W := ⟨2,![8,23,17,9],![3,18,39,16]⟩
def data500 : PartitionData E W := ⟨6,![cycle500_0,cycle500_1,cycle500_2,cycle500_3,cycle500_4,cycle500_5]⟩
lemma valid_data500 : data500.Valid src500 dst500 Finset.univ := by decide +kernel

def src501 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,38,18,28,39]
def dst501 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle501_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle501_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle501_2 : CycleData E W := ⟨2,![4,21,19,11],![4,8,38,26]⟩
def cycle501_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle501_4 : CycleData E W := ⟨3,![7,23,24,18,12],![14,18,28,39,26]⟩
def cycle501_5 : CycleData E W := ⟨3,![8,22,20,16,9],![3,18,38,6,16]⟩
def data501 : PartitionData E W := ⟨6,![cycle501_0,cycle501_1,cycle501_2,cycle501_3,cycle501_4,cycle501_5]⟩
lemma valid_data501 : data501.Valid src501 dst501 Finset.univ := by decide +kernel

def src502 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,38,28,18,39]
def dst502 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle502_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle502_1 : CycleData E W := ⟨2,![1,20,22,14],![5,6,38,28]⟩
def cycle502_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle502_3 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle502_4 : CycleData E W := ⟨2,![4,21,19,11],![4,8,38,26]⟩
def cycle502_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle502_6 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def data502 : PartitionData E W := ⟨7,![cycle502_0,cycle502_1,cycle502_2,cycle502_3,cycle502_4,cycle502_5,cycle502_6]⟩
lemma valid_data502 : data502.Valid src502 dst502 Finset.univ := by decide +kernel

def src503 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,38,26,8,38,18,28,39]
def dst503 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle503_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle503_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle503_2 : CycleData E W := ⟨4,![5,4,11,20,16,10],![2,8,4,26,6,16]⟩
def cycle503_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,38,26]⟩
def cycle503_4 : CycleData E W := ⟨3,![8,23,24,17,9],![3,18,28,39,16]⟩
def cycle503_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data503 : PartitionData E W := ⟨6,![cycle503_0,cycle503_1,cycle503_2,cycle503_3,cycle503_4,cycle503_5]⟩
lemma valid_data503 : data503.Valid src503 dst503 Finset.univ := by decide +kernel

def src504 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,39,8,38,28,18,39]
def dst504 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle504_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle504_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle504_2 : CycleData E W := ⟨3,![5,4,11,17,10],![2,8,4,26,16]⟩
def cycle504_3 : CycleData E W := ⟨3,![16,12,7,24,20],![6,26,14,18,39]⟩
def cycle504_4 : CycleData E W := ⟨3,![8,23,22,18,9],![3,18,28,38,16]⟩
def cycle504_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data504 : PartitionData E W := ⟨6,![cycle504_0,cycle504_1,cycle504_2,cycle504_3,cycle504_4,cycle504_5]⟩
lemma valid_data504 : data504.Valid src504 dst504 Finset.univ := by decide +kernel

def src505 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,16,39,38,8,38,18,28,39]
def dst505 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle505_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle505_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle505_2 : CycleData E W := ⟨3,![5,4,11,17,10],![2,8,4,26,16]⟩
def cycle505_3 : CycleData E W := ⟨3,![16,12,7,22,20],![6,26,14,18,38]⟩
def cycle505_4 : CycleData E W := ⟨3,![8,23,24,18,9],![3,18,28,39,16]⟩
def cycle505_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data505 : PartitionData E W := ⟨6,![cycle505_0,cycle505_1,cycle505_2,cycle505_3,cycle505_4,cycle505_5]⟩
lemma valid_data505 : data505.Valid src505 dst505 Finset.univ := by decide +kernel

def src506 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,18,38,28,39]
def dst506 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle506_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle506_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle506_2 : CycleData E W := ⟨3,![4,21,7,12,11],![4,8,18,14,26]⟩
def cycle506_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle506_4 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def cycle506_5 : CycleData E W := ⟨3,![16,17,23,24,20],![6,26,38,28,39]⟩
def data506 : PartitionData E W := ⟨6,![cycle506_0,cycle506_1,cycle506_2,cycle506_3,cycle506_4,cycle506_5]⟩
lemma valid_data506 : data506.Valid src506 dst506 Finset.univ := by decide +kernel

def src507 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,18,39,28,38]
def dst507 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle507_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle507_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle507_2 : CycleData E W := ⟨3,![4,21,7,12,11],![4,8,18,14,26]⟩
def cycle507_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,38,16]⟩
def cycle507_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle507_5 : CycleData E W := ⟨3,![16,17,24,23,20],![6,26,38,28,39]⟩
def data507 : PartitionData E W := ⟨6,![cycle507_0,cycle507_1,cycle507_2,cycle507_3,cycle507_4,cycle507_5]⟩
lemma valid_data507 : data507.Valid src507 dst507 Finset.univ := by decide +kernel

def src508 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst508 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle508_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle508_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle508_2 : CycleData E W := ⟨2,![4,21,17,11],![4,8,38,26]⟩
def cycle508_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle508_4 : CycleData E W := ⟨4,![16,12,7,23,24,20],![6,26,14,18,28,39]⟩
def cycle508_5 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def data508 : PartitionData E W := ⟨6,![cycle508_0,cycle508_1,cycle508_2,cycle508_3,cycle508_4,cycle508_5]⟩
lemma valid_data508 : data508.Valid src508 dst508 Finset.univ := by decide +kernel

def src509 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst509 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle509_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle509_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle509_2 : CycleData E W := ⟨2,![4,21,17,11],![4,8,38,26]⟩
def cycle509_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle509_4 : CycleData E W := ⟨3,![16,12,7,24,20],![6,26,14,18,39]⟩
def cycle509_5 : CycleData E W := ⟨3,![8,23,22,18,9],![3,18,28,38,16]⟩
def data509 : PartitionData E W := ⟨6,![cycle509_0,cycle509_1,cycle509_2,cycle509_3,cycle509_4,cycle509_5]⟩
lemma valid_data509 : data509.Valid src509 dst509 Finset.univ := by decide +kernel

def src510 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,18,38,28,39]
def dst510 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle510_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle510_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle510_2 : CycleData E W := ⟨3,![4,21,7,12,11],![4,8,18,14,26]⟩
def cycle510_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle510_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,38,16]⟩
def cycle510_5 : CycleData E W := ⟨3,![16,17,24,23,20],![6,26,39,28,38]⟩
def data510 : PartitionData E W := ⟨6,![cycle510_0,cycle510_1,cycle510_2,cycle510_3,cycle510_4,cycle510_5]⟩
lemma valid_data510 : data510.Valid src510 dst510 Finset.univ := by decide +kernel

def src511 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,18,39,28,38]
def dst511 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle511_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle511_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle511_2 : CycleData E W := ⟨3,![4,21,7,12,11],![4,8,18,14,26]⟩
def cycle511_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,38,16]⟩
def cycle511_4 : CycleData E W := ⟨2,![8,22,18,9],![3,18,39,16]⟩
def cycle511_5 : CycleData E W := ⟨3,![16,17,23,24,20],![6,26,39,28,38]⟩
def data511 : PartitionData E W := ⟨6,![cycle511_0,cycle511_1,cycle511_2,cycle511_3,cycle511_4,cycle511_5]⟩
lemma valid_data511 : data511.Valid src511 dst511 Finset.univ := by decide +kernel

def src512 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst512 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle512_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle512_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle512_2 : CycleData E W := ⟨3,![4,21,20,16,11],![4,8,38,6,26]⟩
def cycle512_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle512_4 : CycleData E W := ⟨3,![7,23,24,17,12],![14,18,28,39,26]⟩
def cycle512_5 : CycleData E W := ⟨2,![8,22,19,9],![3,18,38,16]⟩
def data512 : PartitionData E W := ⟨6,![cycle512_0,cycle512_1,cycle512_2,cycle512_3,cycle512_4,cycle512_5]⟩
lemma valid_data512 : data512.Valid src512 dst512 Finset.univ := by decide +kernel

def src513 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst513 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle513_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle513_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle513_2 : CycleData E W := ⟨3,![4,21,20,16,11],![4,8,38,6,26]⟩
def cycle513_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle513_4 : CycleData E W := ⟨2,![7,24,17,12],![14,18,39,26]⟩
def cycle513_5 : CycleData E W := ⟨3,![8,23,22,19,9],![3,18,28,38,16]⟩
def data513 : PartitionData E W := ⟨6,![cycle513_0,cycle513_1,cycle513_2,cycle513_3,cycle513_4,cycle513_5]⟩
lemma valid_data513 : data513.Valid src513 dst513 Finset.univ := by decide +kernel

def src514 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,28,38,39]
def dst514 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle514_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,16]⟩
def cycle514_1 : CycleData E W := ⟨2,![3,4,21,8],![3,4,8,18]⟩
def cycle514_2 : CycleData E W := ⟨3,![5,25,19,12,6],![2,8,39,26,14]⟩
def cycle514_3 : CycleData E W := ⟨2,![13,7,22,14],![5,14,18,28]⟩
def cycle514_4 : CycleData E W := ⟨3,![11,18,17,23,15],![4,26,16,38,28]⟩
def cycle514_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data514 : PartitionData E W := ⟨6,![cycle514_0,cycle514_1,cycle514_2,cycle514_3,cycle514_4,cycle514_5]⟩
lemma valid_data514 : data514.Valid src514 dst514 Finset.univ := by decide +kernel

def src515 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,38,28,39]
def dst515 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle515_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle515_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle515_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle515_3 : CycleData E W := ⟨3,![21,7,12,19,25],![8,18,14,26,39]⟩
def cycle515_4 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def cycle515_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data515 : PartitionData E W := ⟨6,![cycle515_0,cycle515_1,cycle515_2,cycle515_3,cycle515_4,cycle515_5]⟩
lemma valid_data515 : data515.Valid src515 dst515 Finset.univ := by decide +kernel

def src516 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,39,28,38]
def dst516 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle516_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle516_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle516_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle516_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle516_4 : CycleData E W := ⟨3,![8,21,25,17,9],![3,18,8,38,16]⟩
def cycle516_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data516 : PartitionData E W := ⟨6,![cycle516_0,cycle516_1,cycle516_2,cycle516_3,cycle516_4,cycle516_5]⟩
lemma valid_data516 : data516.Valid src516 dst516 Finset.univ := by decide +kernel

def src517 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,39,38,28]
def dst517 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle517_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,16]⟩
def cycle517_1 : CycleData E W := ⟨2,![3,4,21,8],![3,4,8,18]⟩
def cycle517_2 : CycleData E W := ⟨3,![5,25,14,13,6],![2,8,28,5,14]⟩
def cycle517_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle517_4 : CycleData E W := ⟨3,![11,18,17,24,15],![4,26,16,38,28]⟩
def cycle517_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data517 : PartitionData E W := ⟨6,![cycle517_0,cycle517_1,cycle517_2,cycle517_3,cycle517_4,cycle517_5]⟩
lemma valid_data517 : data517.Valid src517 dst517 Finset.univ := by decide +kernel

def src518 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,28,18,39,38]
def dst518 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle518_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle518_1 : CycleData E W := ⟨3,![2,1,14,22,8],![3,6,5,28,18]⟩
def cycle518_2 : CycleData E W := ⟨2,![3,11,18,9],![3,4,26,16]⟩
def cycle518_3 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle518_4 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle518_5 : CycleData E W := ⟨2,![7,23,19,12],![14,18,39,26]⟩
def cycle518_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data518 : PartitionData E W := ⟨7,![cycle518_0,cycle518_1,cycle518_2,cycle518_3,cycle518_4,cycle518_5,cycle518_6]⟩
lemma valid_data518 : data518.Valid src518 dst518 Finset.univ := by decide +kernel

def src519 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst519 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle519_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle519_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle519_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle519_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle519_4 : CycleData E W := ⟨2,![8,23,17,9],![3,18,38,16]⟩
def cycle519_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,28,8,39]⟩
def data519 : PartitionData E W := ⟨6,![cycle519_0,cycle519_1,cycle519_2,cycle519_3,cycle519_4,cycle519_5]⟩
lemma valid_data519 : data519.Valid src519 dst519 Finset.univ := by decide +kernel

def src520 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst520 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle520_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle520_1 : CycleData E W := ⟨2,![1,20,22,14],![5,6,39,28]⟩
def cycle520_2 : CycleData E W := ⟨2,![2,16,24,8],![3,6,38,18]⟩
def cycle520_3 : CycleData E W := ⟨2,![3,11,18,9],![3,4,26,16]⟩
def cycle520_4 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle520_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle520_6 : CycleData E W := ⟨2,![7,23,19,12],![14,18,39,26]⟩
def data520 : PartitionData E W := ⟨7,![cycle520_0,cycle520_1,cycle520_2,cycle520_3,cycle520_4,cycle520_5,cycle520_6]⟩
lemma valid_data520 : data520.Valid src520 dst520 Finset.univ := by decide +kernel

def src521 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst521 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle521_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle521_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle521_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle521_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle521_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle521_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data521 : PartitionData E W := ⟨6,![cycle521_0,cycle521_1,cycle521_2,cycle521_3,cycle521_4,cycle521_5]⟩
lemma valid_data521 : data521.Valid src521 dst521 Finset.univ := by decide +kernel

def src522 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,28,39,38]
def dst522 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle522_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,16]⟩
def cycle522_1 : CycleData E W := ⟨2,![3,4,21,8],![3,4,8,18]⟩
def cycle522_2 : CycleData E W := ⟨3,![5,25,17,12,6],![2,8,38,26,14]⟩
def cycle522_3 : CycleData E W := ⟨2,![13,7,22,14],![5,14,18,28]⟩
def cycle522_4 : CycleData E W := ⟨3,![11,18,19,23,15],![4,26,16,39,28]⟩
def cycle522_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data522 : PartitionData E W := ⟨6,![cycle522_0,cycle522_1,cycle522_2,cycle522_3,cycle522_4,cycle522_5]⟩
lemma valid_data522 : data522.Valid src522 dst522 Finset.univ := by decide +kernel

def src523 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,38,28,39]
def dst523 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle523_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle523_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle523_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle523_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle523_4 : CycleData E W := ⟨3,![8,21,25,19,9],![3,18,8,39,16]⟩
def cycle523_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data523 : PartitionData E W := ⟨6,![cycle523_0,cycle523_1,cycle523_2,cycle523_3,cycle523_4,cycle523_5]⟩
lemma valid_data523 : data523.Valid src523 dst523 Finset.univ := by decide +kernel

def src524 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,38,39,28]
def dst524 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle524_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,16]⟩
def cycle524_1 : CycleData E W := ⟨2,![3,4,21,8],![3,4,8,18]⟩
def cycle524_2 : CycleData E W := ⟨3,![5,25,14,13,6],![2,8,28,5,14]⟩
def cycle524_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle524_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle524_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data524 : PartitionData E W := ⟨6,![cycle524_0,cycle524_1,cycle524_2,cycle524_3,cycle524_4,cycle524_5]⟩
lemma valid_data524 : data524.Valid src524 dst524 Finset.univ := by decide +kernel

def src525 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,39,28,38]
def dst525 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle525_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle525_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle525_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle525_3 : CycleData E W := ⟨3,![21,7,12,17,25],![8,18,14,26,38]⟩
def cycle525_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle525_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data525 : PartitionData E W := ⟨6,![cycle525_0,cycle525_1,cycle525_2,cycle525_3,cycle525_4,cycle525_5]⟩
lemma valid_data525 : data525.Valid src525 dst525 Finset.univ := by decide +kernel

def src526 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,28,18,38,39]
def dst526 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle526_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle526_1 : CycleData E W := ⟨3,![2,1,14,22,8],![3,6,5,28,18]⟩
def cycle526_2 : CycleData E W := ⟨2,![3,11,18,9],![3,4,26,16]⟩
def cycle526_3 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle526_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle526_5 : CycleData E W := ⟨2,![7,23,17,12],![14,18,38,26]⟩
def cycle526_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data526 : PartitionData E W := ⟨7,![cycle526_0,cycle526_1,cycle526_2,cycle526_3,cycle526_4,cycle526_5,cycle526_6]⟩
lemma valid_data526 : data526.Valid src526 dst526 Finset.univ := by decide +kernel

def src527 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst527 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle527_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle527_1 : CycleData E W := ⟨2,![1,16,22,14],![5,6,38,28]⟩
def cycle527_2 : CycleData E W := ⟨2,![2,20,24,8],![3,6,39,18]⟩
def cycle527_3 : CycleData E W := ⟨2,![3,11,18,9],![3,4,26,16]⟩
def cycle527_4 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle527_5 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle527_6 : CycleData E W := ⟨2,![7,23,17,12],![14,18,38,26]⟩
def data527 : PartitionData E W := ⟨7,![cycle527_0,cycle527_1,cycle527_2,cycle527_3,cycle527_4,cycle527_5,cycle527_6]⟩
lemma valid_data527 : data527.Valid src527 dst527 Finset.univ := by decide +kernel

def src528 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst528 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle528_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle528_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle528_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle528_3 : CycleData E W := ⟨2,![7,24,17,12],![14,18,38,26]⟩
def cycle528_4 : CycleData E W := ⟨2,![8,23,19,9],![3,18,39,16]⟩
def cycle528_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,28,39]⟩
def data528 : PartitionData E W := ⟨6,![cycle528_0,cycle528_1,cycle528_2,cycle528_3,cycle528_4,cycle528_5]⟩
lemma valid_data528 : data528.Valid src528 dst528 Finset.univ := by decide +kernel

def src529 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst529 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle529_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle529_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle529_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle529_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle529_4 : CycleData E W := ⟨3,![8,23,24,19,9],![3,18,28,39,16]⟩
def cycle529_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data529 : PartitionData E W := ⟨6,![cycle529_0,cycle529_1,cycle529_2,cycle529_3,cycle529_4,cycle529_5]⟩
lemma valid_data529 : data529.Valid src529 dst529 Finset.univ := by decide +kernel

def src530 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,16,38,26,39,8,38,18,28,39]
def dst530 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle530_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle530_1 : CycleData E W := ⟨3,![1,16,7,13,12],![5,6,16,14,28]⟩
def cycle530_2 : CycleData E W := ⟨3,![2,20,24,23,9],![3,6,39,28,18]⟩
def cycle530_3 : CycleData E W := ⟨2,![3,15,14,8],![3,4,26,14]⟩
def cycle530_4 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle530_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data530 : PartitionData E W := ⟨6,![cycle530_0,cycle530_1,cycle530_2,cycle530_3,cycle530_4,cycle530_5]⟩
lemma valid_data530 : data530.Valid src530 dst530 Finset.univ := by decide +kernel

def src531 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,16,38,26,39,8,38,28,18,39]
def dst531 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle531_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle531_1 : CycleData E W := ⟨3,![1,16,7,13,12],![5,6,16,14,28]⟩
def cycle531_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle531_3 : CycleData E W := ⟨2,![3,15,14,8],![3,4,26,14]⟩
def cycle531_4 : CycleData E W := ⟨3,![6,17,22,23,10],![2,16,38,28,18]⟩
def cycle531_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data531 : PartitionData E W := ⟨6,![cycle531_0,cycle531_1,cycle531_2,cycle531_3,cycle531_4,cycle531_5]⟩
lemma valid_data531 : data531.Valid src531 dst531 Finset.univ := by decide +kernel

def src532 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,16,39,26,38,8,38,18,28,39]
def dst532 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle532_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle532_1 : CycleData E W := ⟨3,![1,16,7,13,12],![5,6,16,14,28]⟩
def cycle532_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle532_3 : CycleData E W := ⟨2,![3,15,14,8],![3,4,26,14]⟩
def cycle532_4 : CycleData E W := ⟨3,![6,17,24,23,10],![2,16,39,28,18]⟩
def cycle532_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data532 : PartitionData E W := ⟨6,![cycle532_0,cycle532_1,cycle532_2,cycle532_3,cycle532_4,cycle532_5]⟩
lemma valid_data532 : data532.Valid src532 dst532 Finset.univ := by decide +kernel

def src533 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,16,39,26,38,8,38,28,18,39]
def dst533 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle533_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle533_1 : CycleData E W := ⟨3,![1,16,7,13,12],![5,6,16,14,28]⟩
def cycle533_2 : CycleData E W := ⟨3,![2,20,22,23,9],![3,6,38,28,18]⟩
def cycle533_3 : CycleData E W := ⟨2,![3,15,14,8],![3,4,26,14]⟩
def cycle533_4 : CycleData E W := ⟨2,![6,17,24,10],![2,16,39,18]⟩
def cycle533_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data533 : PartitionData E W := ⟨6,![cycle533_0,cycle533_1,cycle533_2,cycle533_3,cycle533_4,cycle533_5]⟩
lemma valid_data533 : data533.Valid src533 dst533 Finset.univ := by decide +kernel

def src534 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,16,26,39,8,18,38,28,39]
def dst534 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle534_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle534_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle534_2 : CycleData E W := ⟨2,![4,25,19,15],![4,8,39,26]⟩
def cycle534_3 : CycleData E W := ⟨3,![5,21,22,17,6],![2,8,18,38,16]⟩
def cycle534_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle534_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data534 : PartitionData E W := ⟨6,![cycle534_0,cycle534_1,cycle534_2,cycle534_3,cycle534_4,cycle534_5]⟩
lemma valid_data534 : data534.Valid src534 dst534 Finset.univ := by decide +kernel

def src535 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,16,26,39,8,18,39,28,38]
def dst535 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle535_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle535_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle535_2 : CycleData E W := ⟨3,![4,21,22,19,15],![4,8,18,39,26]⟩
def cycle535_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,38,16]⟩
def cycle535_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle535_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data535 : PartitionData E W := ⟨6,![cycle535_0,cycle535_1,cycle535_2,cycle535_3,cycle535_4,cycle535_5]⟩
lemma valid_data535 : data535.Valid src535 dst535 Finset.univ := by decide +kernel

def src536 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst536 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle536_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle536_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle536_2 : CycleData E W := ⟨2,![4,25,19,15],![4,8,39,26]⟩
def cycle536_3 : CycleData E W := ⟨2,![5,21,17,6],![2,8,38,16]⟩
def cycle536_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle536_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data536 : PartitionData E W := ⟨6,![cycle536_0,cycle536_1,cycle536_2,cycle536_3,cycle536_4,cycle536_5]⟩
lemma valid_data536 : data536.Valid src536 dst536 Finset.univ := by decide +kernel

def src537 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,26,16,39,8,18,38,28,39]
def dst537 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle537_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle537_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle537_2 : CycleData E W := ⟨3,![4,21,22,17,15],![4,8,18,38,26]⟩
def cycle537_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle537_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle537_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data537 : PartitionData E W := ⟨6,![cycle537_0,cycle537_1,cycle537_2,cycle537_3,cycle537_4,cycle537_5]⟩
lemma valid_data537 : data537.Valid src537 dst537 Finset.univ := by decide +kernel

def src538 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,26,16,39,8,18,39,28,38]
def dst538 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle538_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle538_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle538_2 : CycleData E W := ⟨2,![4,25,17,15],![4,8,38,26]⟩
def cycle538_3 : CycleData E W := ⟨3,![5,21,22,19,6],![2,8,18,39,16]⟩
def cycle538_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle538_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data538 : PartitionData E W := ⟨6,![cycle538_0,cycle538_1,cycle538_2,cycle538_3,cycle538_4,cycle538_5]⟩
lemma valid_data538 : data538.Valid src538 dst538 Finset.univ := by decide +kernel

def src539 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst539 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle539_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle539_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,28,14]⟩
def cycle539_2 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle539_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle539_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle539_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data539 : PartitionData E W := ⟨6,![cycle539_0,cycle539_1,cycle539_2,cycle539_3,cycle539_4,cycle539_5]⟩
lemma valid_data539 : data539.Valid src539 dst539 Finset.univ := by decide +kernel

def src540 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,26,38,39,8,38,18,28,39]
def dst540 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,26,38,39,6,38,18,28,39,8]
def cycle540_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle540_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle540_2 : CycleData E W := ⟨3,![5,4,15,17,6],![2,8,4,26,16]⟩
def cycle540_3 : CycleData E W := ⟨3,![16,7,12,24,20],![6,16,14,28,39]⟩
def cycle540_4 : CycleData E W := ⟨3,![13,23,22,18,14],![5,28,18,38,26]⟩
def cycle540_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data540 : PartitionData E W := ⟨6,![cycle540_0,cycle540_1,cycle540_2,cycle540_3,cycle540_4,cycle540_5]⟩
lemma valid_data540 : data540.Valid src540 dst540 Finset.univ := by decide +kernel

def src541 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,26,39,38,8,38,28,18,39]
def dst541 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,26,39,38,6,38,28,18,39,8]
def cycle541_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle541_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle541_2 : CycleData E W := ⟨3,![5,4,15,17,6],![2,8,4,26,16]⟩
def cycle541_3 : CycleData E W := ⟨3,![16,7,12,22,20],![6,16,14,28,38]⟩
def cycle541_4 : CycleData E W := ⟨3,![13,23,24,18,14],![5,28,18,39,26]⟩
def cycle541_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data541 : PartitionData E W := ⟨6,![cycle541_0,cycle541_1,cycle541_2,cycle541_3,cycle541_4,cycle541_5]⟩
lemma valid_data541 : data541.Valid src541 dst541 Finset.univ := by decide +kernel

def src542 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,28,38,18,39]
def dst542 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,28,38,18,39,8]
def cycle542_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle542_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle542_2 : CycleData E W := ⟨3,![4,21,13,14,15],![4,8,28,5,26]⟩
def cycle542_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle542_4 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle542_5 : CycleData E W := ⟨2,![23,18,19,24],![18,38,26,39]⟩
def data542 : PartitionData E W := ⟨6,![cycle542_0,cycle542_1,cycle542_2,cycle542_3,cycle542_4,cycle542_5]⟩
lemma valid_data542 : data542.Valid src542 dst542 Finset.univ := by decide +kernel

def src543 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,28,39,18,38]
def dst543 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,28,39,18,38,8]
def cycle543_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle543_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle543_2 : CycleData E W := ⟨3,![4,21,13,14,15],![4,8,28,5,26]⟩
def cycle543_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,38,16]⟩
def cycle543_4 : CycleData E W := ⟨3,![16,7,12,22,20],![6,16,14,28,39]⟩
def cycle543_5 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data543 : PartitionData E W := ⟨6,![cycle543_0,cycle543_1,cycle543_2,cycle543_3,cycle543_4,cycle543_5]⟩
lemma valid_data543 : data543.Valid src543 dst543 Finset.univ := by decide +kernel

def src544 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,38,18,28,39]
def dst544 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle544_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle544_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle544_2 : CycleData E W := ⟨2,![4,21,18,15],![4,8,38,26]⟩
def cycle544_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle544_4 : CycleData E W := ⟨3,![7,17,22,23,12],![14,16,38,18,28]⟩
def cycle544_5 : CycleData E W := ⟨2,![13,24,19,14],![5,28,39,26]⟩
def data544 : PartitionData E W := ⟨6,![cycle544_0,cycle544_1,cycle544_2,cycle544_3,cycle544_4,cycle544_5]⟩
lemma valid_data544 : data544.Valid src544 dst544 Finset.univ := by decide +kernel

def src545 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,38,28,18,39]
def dst545 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle545_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle545_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle545_2 : CycleData E W := ⟨2,![4,21,18,15],![4,8,38,26]⟩
def cycle545_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle545_4 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle545_5 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def data545 : PartitionData E W := ⟨6,![cycle545_0,cycle545_1,cycle545_2,cycle545_3,cycle545_4,cycle545_5]⟩
lemma valid_data545 : data545.Valid src545 dst545 Finset.univ := by decide +kernel

def src546 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,38,39,26,8,38,28,18,39]
def dst546 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,38,39,26,6,38,28,18,39,8]
def cycle546_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle546_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle546_2 : CycleData E W := ⟨4,![5,4,15,20,16,6],![2,8,4,26,6,16]⟩
def cycle546_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle546_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle546_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data546 : PartitionData E W := ⟨6,![cycle546_0,cycle546_1,cycle546_2,cycle546_3,cycle546_4,cycle546_5]⟩
lemma valid_data546 : data546.Valid src546 dst546 Finset.univ := by decide +kernel

def src547 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,28,38,18,39]
def dst547 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,28,38,18,39,8]
def cycle547_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle547_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle547_2 : CycleData E W := ⟨3,![4,21,13,14,15],![4,8,28,5,26]⟩
def cycle547_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle547_4 : CycleData E W := ⟨3,![16,7,12,22,20],![6,16,14,28,38]⟩
def cycle547_5 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data547 : PartitionData E W := ⟨6,![cycle547_0,cycle547_1,cycle547_2,cycle547_3,cycle547_4,cycle547_5]⟩
lemma valid_data547 : data547.Valid src547 dst547 Finset.univ := by decide +kernel

def src548 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,28,39,18,38]
def dst548 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,28,39,18,38,8]
def cycle548_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle548_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle548_2 : CycleData E W := ⟨3,![4,21,13,14,15],![4,8,28,5,26]⟩
def cycle548_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,38,6,16]⟩
def cycle548_4 : CycleData E W := ⟨2,![7,17,22,12],![14,16,39,28]⟩
def cycle548_5 : CycleData E W := ⟨2,![23,18,19,24],![18,39,26,38]⟩
def data548 : PartitionData E W := ⟨6,![cycle548_0,cycle548_1,cycle548_2,cycle548_3,cycle548_4,cycle548_5]⟩
lemma valid_data548 : data548.Valid src548 dst548 Finset.univ := by decide +kernel

def src549 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,38,18,28,39]
def dst549 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle549_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle549_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle549_2 : CycleData E W := ⟨2,![4,21,19,15],![4,8,38,26]⟩
def cycle549_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle549_4 : CycleData E W := ⟨4,![16,7,12,23,22,20],![6,16,14,28,18,38]⟩
def cycle549_5 : CycleData E W := ⟨2,![13,24,18,14],![5,28,39,26]⟩
def data549 : PartitionData E W := ⟨6,![cycle549_0,cycle549_1,cycle549_2,cycle549_3,cycle549_4,cycle549_5]⟩
lemma valid_data549 : data549.Valid src549 dst549 Finset.univ := by decide +kernel

def lookupB10 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data500 else (if j < 2 then data501 else data502)) else (if j < 4 then data503 else (if j < 5 then data504 else data505))) else (if j < 9 then (if j < 7 then data506 else (if j < 8 then data507 else data508)) else (if j < 10 then data509 else (if j < 11 then data510 else data511)))) else (if j < 18 then (if j < 15 then (if j < 13 then data512 else (if j < 14 then data513 else data514)) else (if j < 16 then data515 else (if j < 17 then data516 else data517))) else (if j < 21 then (if j < 19 then data518 else (if j < 20 then data519 else data520)) else (if j < 23 then (if j < 22 then data521 else data522) else (if j < 24 then data523 else data524))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data525 else (if j < 27 then data526 else data527)) else (if j < 29 then data528 else (if j < 30 then data529 else data530))) else (if j < 34 then (if j < 32 then data531 else (if j < 33 then data532 else data533)) else (if j < 35 then data534 else (if j < 36 then data535 else data536)))) else (if j < 43 then (if j < 40 then (if j < 38 then data537 else (if j < 39 then data538 else data539)) else (if j < 41 then data540 else (if j < 42 then data541 else data542))) else (if j < 46 then (if j < 44 then data543 else (if j < 45 then data544 else data545)) else (if j < 48 then (if j < 47 then data546 else data547) else (if j < 49 then data548 else data549))))))

def srcTableB10 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src500 else (if j < 2 then src501 else src502)) else (if j < 4 then src503 else (if j < 5 then src504 else src505))) else (if j < 9 then (if j < 7 then src506 else (if j < 8 then src507 else src508)) else (if j < 10 then src509 else (if j < 11 then src510 else src511)))) else (if j < 18 then (if j < 15 then (if j < 13 then src512 else (if j < 14 then src513 else src514)) else (if j < 16 then src515 else (if j < 17 then src516 else src517))) else (if j < 21 then (if j < 19 then src518 else (if j < 20 then src519 else src520)) else (if j < 23 then (if j < 22 then src521 else src522) else (if j < 24 then src523 else src524))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src525 else (if j < 27 then src526 else src527)) else (if j < 29 then src528 else (if j < 30 then src529 else src530))) else (if j < 34 then (if j < 32 then src531 else (if j < 33 then src532 else src533)) else (if j < 35 then src534 else (if j < 36 then src535 else src536)))) else (if j < 43 then (if j < 40 then (if j < 38 then src537 else (if j < 39 then src538 else src539)) else (if j < 41 then src540 else (if j < 42 then src541 else src542))) else (if j < 46 then (if j < 44 then src543 else (if j < 45 then src544 else src545)) else (if j < 48 then (if j < 47 then src546 else src547) else (if j < 49 then src548 else src549))))))

def dstTableB10 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst500 else (if j < 2 then dst501 else dst502)) else (if j < 4 then dst503 else (if j < 5 then dst504 else dst505))) else (if j < 9 then (if j < 7 then dst506 else (if j < 8 then dst507 else dst508)) else (if j < 10 then dst509 else (if j < 11 then dst510 else dst511)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst512 else (if j < 14 then dst513 else dst514)) else (if j < 16 then dst515 else (if j < 17 then dst516 else dst517))) else (if j < 21 then (if j < 19 then dst518 else (if j < 20 then dst519 else dst520)) else (if j < 23 then (if j < 22 then dst521 else dst522) else (if j < 24 then dst523 else dst524))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst525 else (if j < 27 then dst526 else dst527)) else (if j < 29 then dst528 else (if j < 30 then dst529 else dst530))) else (if j < 34 then (if j < 32 then dst531 else (if j < 33 then dst532 else dst533)) else (if j < 35 then dst534 else (if j < 36 then dst535 else dst536)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst537 else (if j < 39 then dst538 else dst539)) else (if j < 41 then dst540 else (if j < 42 then dst541 else dst542))) else (if j < 46 then (if j < 44 then dst543 else (if j < 45 then dst544 else dst545)) else (if j < 48 then (if j < 47 then dst546 else dst547) else (if j < 49 then dst548 else dst549))))))

def caseB10 (i : Fin 50) : Cases := ⟨500 + i.val,by have := i.isLt; omega⟩
lemma tableB10_valid (i : Fin 50) :
    (lookupB10 i.val).Valid (srcTableB10 i.val) (dstTableB10 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data500
  · exact valid_data501
  · exact valid_data502
  · exact valid_data503
  · exact valid_data504
  · exact valid_data505
  · exact valid_data506
  · exact valid_data507
  · exact valid_data508
  · exact valid_data509
  · exact valid_data510
  · exact valid_data511
  · exact valid_data512
  · exact valid_data513
  · exact valid_data514
  · exact valid_data515
  · exact valid_data516
  · exact valid_data517
  · exact valid_data518
  · exact valid_data519
  · exact valid_data520
  · exact valid_data521
  · exact valid_data522
  · exact valid_data523
  · exact valid_data524
  · exact valid_data525
  · exact valid_data526
  · exact valid_data527
  · exact valid_data528
  · exact valid_data529
  · exact valid_data530
  · exact valid_data531
  · exact valid_data532
  · exact valid_data533
  · exact valid_data534
  · exact valid_data535
  · exact valid_data536
  · exact valid_data537
  · exact valid_data538
  · exact valid_data539
  · exact valid_data540
  · exact valid_data541
  · exact valid_data542
  · exact valid_data543
  · exact valid_data544
  · exact valid_data545
  · exact valid_data546
  · exact valid_data547
  · exact valid_data548
  · exact valid_data549

lemma srcB10_row : ∀ (i : Fin 50) (e : E),
    srcTableB10 i.val e = caseSource (caseB10 i) e := by decide +kernel

lemma dstB10_row : ∀ (i : Fin 50) (e : E),
    dstTableB10 i.val e = caseTarget (caseB10 i) e := by decide +kernel

lemma sizeB10 : ∀ i : Fin 50, (lookupB10 i.val).size ≤ 5 →
    (lookupB10 i.val).size = 2 ∧
      (⟨caseKey (caseB10 i),caseKey_lt (caseB10 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB10 (i : Fin 50) : Certificate (caseB10 i) := by
  refine ⟨lookupB10 i.val,?_,sizeB10 i⟩
  have hv := tableB10_valid i
  rw [funext (srcB10_row i),funext (dstB10_row i)] at hv
  exact hv
lemma certificateInterval10 : FiniteIntervals.Covers CertificateAt 500 550 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 500 50 (fun i _ => certificateB10 i)
#print axioms certificateInterval10
end Erdos184Work.FiveRows4

import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src750 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,38,18,28,39]
def dst750 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle750_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle750_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle750_2 : CycleData E W := ⟨2,![4,21,18,11],![4,8,38,26]⟩
def cycle750_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle750_4 : CycleData E W := ⟨3,![7,23,24,19,12],![14,18,28,39,26]⟩
def cycle750_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data750 : PartitionData E W := ⟨6,![cycle750_0,cycle750_1,cycle750_2,cycle750_3,cycle750_4,cycle750_5]⟩
lemma valid_data750 : data750.Valid src750 dst750 Finset.univ := by decide +kernel

def src751 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,38,28,18,39]
def dst751 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle751_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle751_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle751_2 : CycleData E W := ⟨2,![4,21,18,11],![4,8,38,26]⟩
def cycle751_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle751_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle751_5 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def data751 : PartitionData E W := ⟨6,![cycle751_0,cycle751_1,cycle751_2,cycle751_3,cycle751_4,cycle751_5]⟩
lemma valid_data751 : data751.Valid src751 dst751 Finset.univ := by decide +kernel

def src752 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,38,18,28,39]
def dst752 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle752_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle752_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle752_2 : CycleData E W := ⟨2,![4,21,19,11],![4,8,38,26]⟩
def cycle752_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle752_4 : CycleData E W := ⟨3,![7,23,24,18,12],![14,18,28,39,26]⟩
def cycle752_5 : CycleData E W := ⟨3,![8,22,20,16,9],![3,18,38,6,16]⟩
def data752 : PartitionData E W := ⟨6,![cycle752_0,cycle752_1,cycle752_2,cycle752_3,cycle752_4,cycle752_5]⟩
lemma valid_data752 : data752.Valid src752 dst752 Finset.univ := by decide +kernel

def src753 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,38,28,18,39]
def dst753 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle753_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle753_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle753_2 : CycleData E W := ⟨2,![4,21,19,11],![4,8,38,26]⟩
def cycle753_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle753_4 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def cycle753_5 : CycleData E W := ⟨4,![8,23,22,20,16,9],![3,18,28,38,6,16]⟩
def data753 : PartitionData E W := ⟨6,![cycle753_0,cycle753_1,cycle753_2,cycle753_3,cycle753_4,cycle753_5]⟩
lemma valid_data753 : data753.Valid src753 dst753 Finset.univ := by decide +kernel

def src754 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,38,28,39]
def dst754 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle754_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle754_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle754_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle754_3 : CycleData E W := ⟨3,![21,7,12,19,25],![8,18,14,26,39]⟩
def cycle754_4 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def cycle754_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data754 : PartitionData E W := ⟨6,![cycle754_0,cycle754_1,cycle754_2,cycle754_3,cycle754_4,cycle754_5]⟩
lemma valid_data754 : data754.Valid src754 dst754 Finset.univ := by decide +kernel

def src755 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,18,39,28,38]
def dst755 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle755_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle755_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle755_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle755_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle755_4 : CycleData E W := ⟨3,![8,21,25,17,9],![3,18,8,38,16]⟩
def cycle755_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data755 : PartitionData E W := ⟨6,![cycle755_0,cycle755_1,cycle755_2,cycle755_3,cycle755_4,cycle755_5]⟩
lemma valid_data755 : data755.Valid src755 dst755 Finset.univ := by decide +kernel

def src756 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst756 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle756_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle756_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle756_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle756_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle756_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle756_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data756 : PartitionData E W := ⟨6,![cycle756_0,cycle756_1,cycle756_2,cycle756_3,cycle756_4,cycle756_5]⟩
lemma valid_data756 : data756.Valid src756 dst756 Finset.univ := by decide +kernel

def src757 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,38,28,39]
def dst757 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle757_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle757_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle757_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle757_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle757_4 : CycleData E W := ⟨3,![8,21,25,19,9],![3,18,8,39,16]⟩
def cycle757_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data757 : PartitionData E W := ⟨6,![cycle757_0,cycle757_1,cycle757_2,cycle757_3,cycle757_4,cycle757_5]⟩
lemma valid_data757 : data757.Valid src757 dst757 Finset.univ := by decide +kernel

def src758 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,18,39,28,38]
def dst758 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle758_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle758_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle758_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle758_3 : CycleData E W := ⟨3,![21,7,12,17,25],![8,18,14,26,38]⟩
def cycle758_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle758_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data758 : PartitionData E W := ⟨6,![cycle758_0,cycle758_1,cycle758_2,cycle758_3,cycle758_4,cycle758_5]⟩
lemma valid_data758 : data758.Valid src758 dst758 Finset.univ := by decide +kernel

def src759 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst759 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle759_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle759_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle759_2 : CycleData E W := ⟨3,![5,4,11,18,10],![2,8,4,26,16]⟩
def cycle759_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle759_4 : CycleData E W := ⟨3,![8,23,24,19,9],![3,18,28,39,16]⟩
def cycle759_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data759 : PartitionData E W := ⟨6,![cycle759_0,cycle759_1,cycle759_2,cycle759_3,cycle759_4,cycle759_5]⟩
lemma valid_data759 : data759.Valid src759 dst759 Finset.univ := by decide +kernel

def lookupB15 (j : ℕ) : PartitionData E W := (if j < 5 then (if j < 2 then (if j < 1 then data750 else data751) else (if j < 3 then data752 else (if j < 4 then data753 else data754))) else (if j < 7 then (if j < 6 then data755 else data756) else (if j < 8 then data757 else (if j < 9 then data758 else data759))))

def srcTableB15 (j : ℕ) : E → W := (if j < 5 then (if j < 2 then (if j < 1 then src750 else src751) else (if j < 3 then src752 else (if j < 4 then src753 else src754))) else (if j < 7 then (if j < 6 then src755 else src756) else (if j < 8 then src757 else (if j < 9 then src758 else src759))))

def dstTableB15 (j : ℕ) : E → W := (if j < 5 then (if j < 2 then (if j < 1 then dst750 else dst751) else (if j < 3 then dst752 else (if j < 4 then dst753 else dst754))) else (if j < 7 then (if j < 6 then dst755 else dst756) else (if j < 8 then dst757 else (if j < 9 then dst758 else dst759))))

def caseB15 (i : Fin 10) : Cases := ⟨750 + i.val,by have := i.isLt; omega⟩
lemma tableB15_valid (i : Fin 10) :
    (lookupB15 i.val).Valid (srcTableB15 i.val) (dstTableB15 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data750
  · exact valid_data751
  · exact valid_data752
  · exact valid_data753
  · exact valid_data754
  · exact valid_data755
  · exact valid_data756
  · exact valid_data757
  · exact valid_data758
  · exact valid_data759

lemma srcB15_row : ∀ (i : Fin 10) (e : E),
    srcTableB15 i.val e = caseSource (caseB15 i) e := by decide +kernel

lemma dstB15_row : ∀ (i : Fin 10) (e : E),
    dstTableB15 i.val e = caseTarget (caseB15 i) e := by decide +kernel

lemma sizeB15 : ∀ i : Fin 10, (lookupB15 i.val).size ≤ 5 →
    (lookupB15 i.val).size = 2 ∧
      (⟨caseKey (caseB15 i),caseKey_lt (caseB15 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB15 (i : Fin 10) : Certificate (caseB15 i) := by
  refine ⟨lookupB15 i.val,?_,sizeB15 i⟩
  have hv := tableB15_valid i
  rw [funext (srcB15_row i),funext (dstB15_row i)] at hv
  exact hv
lemma certificateInterval15 : FiniteIntervals.Covers CertificateAt 750 760 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 750 10 (fun i _ => certificateB15 i)
#print axioms certificateInterval15
end Erdos184Work.FiveRows4

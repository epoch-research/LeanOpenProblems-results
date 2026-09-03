import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src50 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst50 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle50_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle50_1 : CycleData E W := ⟨3,![2,3,12,18,8],![3,8,5,26,16]⟩
def cycle50_2 : CycleData E W := ⟨2,![5,4,13,6],![2,6,5,14]⟩
def cycle50_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle50_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle50_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data50 : PartitionData E W := ⟨6,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4,cycle50_5]⟩
lemma valid_data50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel

def src51 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst51 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle51_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle51_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,39,18]⟩
def cycle51_2 : CycleData E W := ⟨2,![3,21,14,13],![5,8,28,14]⟩
def cycle51_3 : CycleData E W := ⟨3,![4,20,19,18,12],![5,6,39,16,26]⟩
def cycle51_4 : CycleData E W := ⟨2,![5,16,23,10],![2,6,38,18]⟩
def cycle51_5 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def data51 : PartitionData E W := ⟨6,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4,cycle51_5]⟩
lemma valid_data51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel

def src52 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst52 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle52_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle52_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,38,18]⟩
def cycle52_2 : CycleData E W := ⟨2,![3,21,14,13],![5,8,28,14]⟩
def cycle52_3 : CycleData E W := ⟨2,![4,16,17,12],![5,6,38,26]⟩
def cycle52_4 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle52_5 : CycleData E W := ⟨3,![11,18,19,22,15],![4,26,16,39,28]⟩
def data52 : PartitionData E W := ⟨6,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5]⟩
lemma valid_data52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel

def src53 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst53 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle53_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle53_1 : CycleData E W := ⟨3,![2,3,12,18,8],![3,8,5,26,16]⟩
def cycle53_2 : CycleData E W := ⟨2,![5,4,13,6],![2,6,5,14]⟩
def cycle53_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle53_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle53_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data53 : PartitionData E W := ⟨6,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4,cycle53_5]⟩
lemma valid_data53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel

def src54 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,5,14,26,28,6,38,16,26,39,8,38,28,18,39]
def dst54 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,5,14,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle54_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle54_1 : CycleData E W := ⟨2,![2,3,12,8],![3,8,5,14]⟩
def cycle54_2 : CycleData E W := ⟨3,![11,4,16,22,15],![4,5,6,38,28]⟩
def cycle54_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle54_4 : CycleData E W := ⟨2,![9,23,14,13],![14,18,28,26]⟩
def cycle54_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data54 : PartitionData E W := ⟨6,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4,cycle54_5]⟩
lemma valid_data54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel

def src55 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,5,14,26,28,6,38,26,16,39,8,38,18,28,39]
def dst55 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,5,14,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle55_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle55_1 : CycleData E W := ⟨2,![2,3,12,8],![3,8,5,14]⟩
def cycle55_2 : CycleData E W := ⟨4,![5,4,11,15,23,10],![2,6,5,4,28,18]⟩
def cycle55_3 : CycleData E W := ⟨2,![9,22,17,13],![14,18,38,26]⟩
def cycle55_4 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def cycle55_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data55 : PartitionData E W := ⟨6,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4,cycle55_5]⟩
lemma valid_data55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel

def src56 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,5,14,28,26,6,38,16,26,39,8,38,28,18,39]
def dst56 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,5,14,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle56_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle56_1 : CycleData E W := ⟨2,![2,3,12,8],![3,8,5,14]⟩
def cycle56_2 : CycleData E W := ⟨4,![11,4,16,17,18,15],![4,5,6,38,16,26]⟩
def cycle56_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle56_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle56_5 : CycleData E W := ⟨3,![21,22,14,19,25],![8,38,28,26,39]⟩
def data56 : PartitionData E W := ⟨6,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4,cycle56_5]⟩
lemma valid_data56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel

def src57 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,5,14,28,26,6,38,26,16,39,8,38,18,28,39]
def dst57 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,5,14,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle57_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle57_1 : CycleData E W := ⟨2,![2,3,12,8],![3,8,5,14]⟩
def cycle57_2 : CycleData E W := ⟨3,![11,4,16,17,15],![4,5,6,38,26]⟩
def cycle57_3 : CycleData E W := ⟨4,![5,20,25,21,22,10],![2,6,39,8,38,18]⟩
def cycle57_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle57_5 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def data57 : PartitionData E W := ⟨6,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4,cycle57_5]⟩
lemma valid_data57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel

def src58 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst58 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle58_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle58_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle58_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle58_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle58_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle58_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data58 : PartitionData E W := ⟨6,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4,cycle58_5]⟩
lemma valid_data58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel

def src59 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst59 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle59_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle59_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle59_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle59_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle59_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle59_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data59 : PartitionData E W := ⟨6,![cycle59_0,cycle59_1,cycle59_2,cycle59_3,cycle59_4,cycle59_5]⟩
lemma valid_data59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel

def src60 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst60 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle60_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle60_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle60_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle60_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle60_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle60_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data60 : PartitionData E W := ⟨6,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4,cycle60_5]⟩
lemma valid_data60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel

def src61 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst61 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle61_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle61_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle61_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle61_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle61_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle61_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data61 : PartitionData E W := ⟨6,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4,cycle61_5]⟩
lemma valid_data61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel

def src62 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst62 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle62_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle62_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle62_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle62_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle62_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle62_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def data62 : PartitionData E W := ⟨6,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4,cycle62_5]⟩
lemma valid_data62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel

def src63 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst63 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle63_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle63_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle63_2 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle63_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle63_4 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle63_5 : CycleData E W := ⟨4,![11,18,17,25,21,15],![4,26,16,38,8,28]⟩
def data63 : PartitionData E W := ⟨6,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4,cycle63_5]⟩
lemma valid_data63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel

def src64 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst64 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle64_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle64_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle64_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle64_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle64_4 : CycleData E W := ⟨3,![11,12,9,23,15],![4,26,14,18,28]⟩
def cycle64_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data64 : PartitionData E W := ⟨6,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4,cycle64_5]⟩
lemma valid_data64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel

def src65 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst65 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle65_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle65_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle65_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle65_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle65_4 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle65_5 : CycleData E W := ⟨4,![11,18,19,25,21,15],![4,26,16,39,8,28]⟩
def data65 : PartitionData E W := ⟨6,![cycle65_0,cycle65_1,cycle65_2,cycle65_3,cycle65_4,cycle65_5]⟩
lemma valid_data65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel

def src66 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst66 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle66_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle66_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle66_2 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle66_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle66_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle66_5 : CycleData E W := ⟨3,![11,17,25,21,15],![4,26,38,8,28]⟩
def data66 : PartitionData E W := ⟨6,![cycle66_0,cycle66_1,cycle66_2,cycle66_3,cycle66_4,cycle66_5]⟩
lemma valid_data66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel

def src67 : E → W := ![2,4,3,8,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst67 : E → W := ![4,3,8,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle67_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle67_1 : CycleData E W := ⟨2,![2,3,13,8],![3,8,5,14]⟩
def cycle67_2 : CycleData E W := ⟨3,![5,4,14,23,10],![2,6,5,28,18]⟩
def cycle67_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle67_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle67_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data67 : PartitionData E W := ⟨6,![cycle67_0,cycle67_1,cycle67_2,cycle67_3,cycle67_4,cycle67_5]⟩
lemma valid_data67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel

def src68 : E → W := ![2,4,3,8,6,5,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst68 : E → W := ![4,3,8,6,5,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle68_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle68_1 : CycleData E W := ⟨3,![2,3,4,13,8],![3,8,6,5,14]⟩
def cycle68_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle68_3 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle68_4 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def cycle68_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data68 : PartitionData E W := ⟨6,![cycle68_0,cycle68_1,cycle68_2,cycle68_3,cycle68_4,cycle68_5]⟩
lemma valid_data68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel

def src69 : E → W := ![2,4,3,8,6,5,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst69 : E → W := ![4,3,8,6,5,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle69_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle69_1 : CycleData E W := ⟨3,![2,3,4,13,8],![3,8,6,5,14]⟩
def cycle69_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle69_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle69_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle69_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data69 : PartitionData E W := ⟨6,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4,cycle69_5]⟩
lemma valid_data69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel

def src70 : E → W := ![2,4,3,8,6,5,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst70 : E → W := ![4,3,8,6,5,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle70_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle70_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,39,18]⟩
def cycle70_2 : CycleData E W := ⟨1,![3,21,16],![6,8,38]⟩
def cycle70_3 : CycleData E W := ⟨2,![4,20,19,12],![5,6,39,26]⟩
def cycle70_4 : CycleData E W := ⟨3,![5,13,14,23,10],![2,5,14,28,18]⟩
def cycle70_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data70 : PartitionData E W := ⟨6,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4,cycle70_5]⟩
lemma valid_data70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel

def src71 : E → W := ![2,4,3,8,6,5,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst71 : E → W := ![4,3,8,6,5,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle71_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle71_1 : CycleData E W := ⟨2,![2,21,22,9],![3,8,38,18]⟩
def cycle71_2 : CycleData E W := ⟨1,![3,25,20],![6,8,39]⟩
def cycle71_3 : CycleData E W := ⟨2,![4,16,17,12],![5,6,38,26]⟩
def cycle71_4 : CycleData E W := ⟨3,![5,13,14,23,10],![2,5,14,28,18]⟩
def cycle71_5 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def data71 : PartitionData E W := ⟨6,![cycle71_0,cycle71_1,cycle71_2,cycle71_3,cycle71_4,cycle71_5]⟩
lemma valid_data71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel

def src72 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst72 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle72_0 : CycleData E W := ⟨2,![0,11,3,6],![2,4,5,3]⟩
def cycle72_1 : CycleData E W := ⟨2,![1,16,22,15],![4,6,38,28]⟩
def cycle72_2 : CycleData E W := ⟨2,![2,20,24,7],![3,6,39,18]⟩
def cycle72_3 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle72_4 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle72_5 : CycleData E W := ⟨1,![8,23,14],![14,18,28]⟩
def cycle72_6 : CycleData E W := ⟨1,![9,18,13],![14,16,26]⟩
def data72 : PartitionData E W := ⟨7,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4,cycle72_5,cycle72_6]⟩
lemma valid_data72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel

def src73 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst73 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle73_0 : CycleData E W := ⟨2,![0,11,3,6],![2,4,5,3]⟩
def cycle73_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle73_2 : CycleData E W := ⟨2,![2,16,22,7],![3,6,38,18]⟩
def cycle73_3 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle73_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle73_5 : CycleData E W := ⟨1,![8,23,14],![14,18,28]⟩
def cycle73_6 : CycleData E W := ⟨1,![9,18,13],![14,16,26]⟩
def data73 : PartitionData E W := ⟨7,![cycle73_0,cycle73_1,cycle73_2,cycle73_3,cycle73_4,cycle73_5,cycle73_6]⟩
lemma valid_data73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel

def src74 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,5,26,28,6,38,16,26,39,8,38,28,18,39]
def dst74 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,5,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle74_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle74_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,18]⟩
def cycle74_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle74_3 : CycleData E W := ⟨3,![11,9,17,22,15],![4,14,16,38,28]⟩
def cycle74_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle74_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data74 : PartitionData E W := ⟨6,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4,cycle74_5]⟩
lemma valid_data74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel

def src75 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,5,26,28,6,38,26,16,39,8,38,18,28,39]
def dst75 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,5,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle75_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle75_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,18]⟩
def cycle75_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle75_3 : CycleData E W := ⟨3,![11,9,19,24,15],![4,14,16,39,28]⟩
def cycle75_4 : CycleData E W := ⟨2,![22,17,14,23],![18,38,26,28]⟩
def cycle75_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data75 : PartitionData E W := ⟨6,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4,cycle75_5]⟩
lemma valid_data75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel

def src76 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,5,28,26,6,38,16,26,39,8,38,28,18,39]
def dst76 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,5,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle76_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle76_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,18]⟩
def cycle76_2 : CycleData E W := ⟨4,![5,4,13,22,17,10],![2,8,5,28,38,16]⟩
def cycle76_3 : CycleData E W := ⟨2,![11,9,18,15],![4,14,16,26]⟩
def cycle76_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle76_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data76 : PartitionData E W := ⟨6,![cycle76_0,cycle76_1,cycle76_2,cycle76_3,cycle76_4,cycle76_5]⟩
lemma valid_data76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel

def src77 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,5,28,26,6,38,26,16,39,8,38,18,28,39]
def dst77 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,5,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle77_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle77_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,18]⟩
def cycle77_2 : CycleData E W := ⟨3,![4,21,17,14,13],![5,8,38,26,28]⟩
def cycle77_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle77_4 : CycleData E W := ⟨2,![11,9,18,15],![4,14,16,26]⟩
def cycle77_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data77 : PartitionData E W := ⟨6,![cycle77_0,cycle77_1,cycle77_2,cycle77_3,cycle77_4,cycle77_5]⟩
lemma valid_data77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel

def src78 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst78 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle78_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle78_1 : CycleData E W := ⟨3,![3,13,17,22,7],![3,5,26,38,18]⟩
def cycle78_2 : CycleData E W := ⟨2,![4,25,24,14],![5,8,39,28]⟩
def cycle78_3 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle78_4 : CycleData E W := ⟨2,![11,8,23,15],![4,14,18,28]⟩
def cycle78_5 : CycleData E W := ⟨3,![16,12,9,19,20],![6,26,14,16,39]⟩
def data78 : PartitionData E W := ⟨6,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4,cycle78_5]⟩
lemma valid_data78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel

def src79 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst79 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle79_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle79_1 : CycleData E W := ⟨2,![3,14,23,7],![3,5,28,18]⟩
def cycle79_2 : CycleData E W := ⟨2,![4,21,17,13],![5,8,38,26]⟩
def cycle79_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle79_4 : CycleData E W := ⟨3,![16,12,8,24,20],![6,26,14,18,39]⟩
def cycle79_5 : CycleData E W := ⟨3,![11,9,18,22,15],![4,14,16,38,28]⟩
def data79 : PartitionData E W := ⟨6,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4,cycle79_5]⟩
lemma valid_data79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel

def src80 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst80 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle80_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle80_1 : CycleData E W := ⟨4,![3,13,16,20,22,7],![3,5,26,6,38,18]⟩
def cycle80_2 : CycleData E W := ⟨2,![4,25,24,14],![5,8,39,28]⟩
def cycle80_3 : CycleData E W := ⟨2,![5,21,19,10],![2,8,38,16]⟩
def cycle80_4 : CycleData E W := ⟨2,![11,8,23,15],![4,14,18,28]⟩
def cycle80_5 : CycleData E W := ⟨2,![9,18,17,12],![14,16,39,26]⟩
def data80 : PartitionData E W := ⟨6,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4,cycle80_5]⟩
lemma valid_data80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel

def src81 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst81 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle81_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle81_1 : CycleData E W := ⟨2,![3,14,23,7],![3,5,28,18]⟩
def cycle81_2 : CycleData E W := ⟨3,![4,21,20,16,13],![5,8,38,6,26]⟩
def cycle81_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle81_4 : CycleData E W := ⟨2,![8,24,17,12],![14,18,39,26]⟩
def cycle81_5 : CycleData E W := ⟨3,![11,9,19,22,15],![4,14,16,38,28]⟩
def data81 : PartitionData E W := ⟨6,![cycle81_0,cycle81_1,cycle81_2,cycle81_3,cycle81_4,cycle81_5]⟩
lemma valid_data81 : data81.Valid src81 dst81 Finset.univ := by decide +kernel

def src82 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst82 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle82_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle82_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,26,14,18]⟩
def cycle82_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle82_3 : CycleData E W := ⟨3,![5,25,19,18,10],![2,8,39,26,16]⟩
def cycle82_4 : CycleData E W := ⟨3,![11,9,17,22,15],![4,14,16,38,28]⟩
def cycle82_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data82 : PartitionData E W := ⟨6,![cycle82_0,cycle82_1,cycle82_2,cycle82_3,cycle82_4,cycle82_5]⟩
lemma valid_data82 : data82.Valid src82 dst82 Finset.univ := by decide +kernel

def src83 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst83 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle83_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle83_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,26,14,18]⟩
def cycle83_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle83_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle83_4 : CycleData E W := ⟨4,![11,9,18,19,22,15],![4,14,16,26,39,28]⟩
def cycle83_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data83 : PartitionData E W := ⟨6,![cycle83_0,cycle83_1,cycle83_2,cycle83_3,cycle83_4,cycle83_5]⟩
lemma valid_data83 : data83.Valid src83 dst83 Finset.univ := by decide +kernel

def src84 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst84 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle84_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle84_1 : CycleData E W := ⟨4,![3,14,15,11,8,7],![3,5,28,4,14,18]⟩
def cycle84_2 : CycleData E W := ⟨2,![4,25,19,13],![5,8,39,26]⟩
def cycle84_3 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle84_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle84_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data84 : PartitionData E W := ⟨6,![cycle84_0,cycle84_1,cycle84_2,cycle84_3,cycle84_4,cycle84_5]⟩
lemma valid_data84 : data84.Valid src84 dst84 Finset.univ := by decide +kernel

def src85 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst85 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle85_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle85_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,26,14,18]⟩
def cycle85_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle85_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle85_4 : CycleData E W := ⟨4,![11,9,18,17,22,15],![4,14,16,26,38,28]⟩
def cycle85_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data85 : PartitionData E W := ⟨6,![cycle85_0,cycle85_1,cycle85_2,cycle85_3,cycle85_4,cycle85_5]⟩
lemma valid_data85 : data85.Valid src85 dst85 Finset.univ := by decide +kernel

def src86 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst86 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle86_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle86_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,26,14,18]⟩
def cycle86_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle86_3 : CycleData E W := ⟨3,![5,25,17,18,10],![2,8,38,26,16]⟩
def cycle86_4 : CycleData E W := ⟨3,![11,9,19,22,15],![4,14,16,39,28]⟩
def cycle86_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data86 : PartitionData E W := ⟨6,![cycle86_0,cycle86_1,cycle86_2,cycle86_3,cycle86_4,cycle86_5]⟩
lemma valid_data86 : data86.Valid src86 dst86 Finset.univ := by decide +kernel

def src87 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst87 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle87_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle87_1 : CycleData E W := ⟨4,![3,14,15,11,8,7],![3,5,28,4,14,18]⟩
def cycle87_2 : CycleData E W := ⟨2,![4,21,17,13],![5,8,38,26]⟩
def cycle87_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle87_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle87_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data87 : PartitionData E W := ⟨6,![cycle87_0,cycle87_1,cycle87_2,cycle87_3,cycle87_4,cycle87_5]⟩
lemma valid_data87 : data87.Valid src87 dst87 Finset.univ := by decide +kernel

def src88 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst88 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle88_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle88_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle88_2 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle88_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle88_4 : CycleData E W := ⟨3,![9,18,22,23,14],![14,16,38,18,28]⟩
def cycle88_5 : CycleData E W := ⟨3,![11,16,20,24,15],![4,26,6,39,28]⟩
def data88 : PartitionData E W := ⟨6,![cycle88_0,cycle88_1,cycle88_2,cycle88_3,cycle88_4,cycle88_5]⟩
lemma valid_data88 : data88.Valid src88 dst88 Finset.univ := by decide +kernel

def src89 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst89 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle89_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle89_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle89_2 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle89_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle89_4 : CycleData E W := ⟨2,![9,18,22,14],![14,16,38,28]⟩
def cycle89_5 : CycleData E W := ⟨4,![11,16,20,24,23,15],![4,26,6,39,18,28]⟩
def data89 : PartitionData E W := ⟨6,![cycle89_0,cycle89_1,cycle89_2,cycle89_3,cycle89_4,cycle89_5]⟩
lemma valid_data89 : data89.Valid src89 dst89 Finset.univ := by decide +kernel

def src90 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst90 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle90_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle90_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle90_2 : CycleData E W := ⟨3,![4,21,20,16,12],![5,8,38,6,26]⟩
def cycle90_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle90_4 : CycleData E W := ⟨3,![9,19,22,23,14],![14,16,38,18,28]⟩
def cycle90_5 : CycleData E W := ⟨2,![11,17,24,15],![4,26,39,28]⟩
def data90 : PartitionData E W := ⟨6,![cycle90_0,cycle90_1,cycle90_2,cycle90_3,cycle90_4,cycle90_5]⟩
lemma valid_data90 : data90.Valid src90 dst90 Finset.univ := by decide +kernel

def src91 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst91 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle91_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle91_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle91_2 : CycleData E W := ⟨3,![4,21,20,16,12],![5,8,38,6,26]⟩
def cycle91_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle91_4 : CycleData E W := ⟨2,![9,19,22,14],![14,16,38,28]⟩
def cycle91_5 : CycleData E W := ⟨3,![11,17,24,23,15],![4,26,39,18,28]⟩
def data91 : PartitionData E W := ⟨6,![cycle91_0,cycle91_1,cycle91_2,cycle91_3,cycle91_4,cycle91_5]⟩
lemma valid_data91 : data91.Valid src91 dst91 Finset.univ := by decide +kernel

def src92 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst92 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle92_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle92_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle92_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle92_3 : CycleData E W := ⟨2,![9,17,22,14],![14,16,38,28]⟩
def cycle92_4 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def cycle92_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data92 : PartitionData E W := ⟨6,![cycle92_0,cycle92_1,cycle92_2,cycle92_3,cycle92_4,cycle92_5]⟩
lemma valid_data92 : data92.Valid src92 dst92 Finset.univ := by decide +kernel

def src93 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst93 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle93_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle93_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle93_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle93_3 : CycleData E W := ⟨3,![21,14,9,17,25],![8,28,14,16,38]⟩
def cycle93_4 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def cycle93_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data93 : PartitionData E W := ⟨6,![cycle93_0,cycle93_1,cycle93_2,cycle93_3,cycle93_4,cycle93_5]⟩
lemma valid_data93 : data93.Valid src93 dst93 Finset.univ := by decide +kernel

def src94 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst94 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle94_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle94_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle94_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle94_3 : CycleData E W := ⟨2,![9,17,22,14],![14,16,38,28]⟩
def cycle94_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle94_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data94 : PartitionData E W := ⟨6,![cycle94_0,cycle94_1,cycle94_2,cycle94_3,cycle94_4,cycle94_5]⟩
lemma valid_data94 : data94.Valid src94 dst94 Finset.univ := by decide +kernel

def src95 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst95 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle95_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle95_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle95_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle95_3 : CycleData E W := ⟨3,![21,14,9,19,25],![8,28,14,16,39]⟩
def cycle95_4 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def cycle95_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data95 : PartitionData E W := ⟨6,![cycle95_0,cycle95_1,cycle95_2,cycle95_3,cycle95_4,cycle95_5]⟩
lemma valid_data95 : data95.Valid src95 dst95 Finset.univ := by decide +kernel

def src96 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst96 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle96_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle96_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle96_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle96_3 : CycleData E W := ⟨2,![9,19,22,14],![14,16,39,28]⟩
def cycle96_4 : CycleData E W := ⟨3,![11,17,25,21,15],![4,26,38,8,28]⟩
def cycle96_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data96 : PartitionData E W := ⟨6,![cycle96_0,cycle96_1,cycle96_2,cycle96_3,cycle96_4,cycle96_5]⟩
lemma valid_data96 : data96.Valid src96 dst96 Finset.univ := by decide +kernel

def src97 : E → W := ![2,4,6,3,5,8,2,3,18,14,16,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst97 : E → W := ![4,6,3,5,8,2,3,18,14,16,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle97_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle97_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,18]⟩
def cycle97_2 : CycleData E W := ⟨3,![5,4,12,18,10],![2,8,5,26,16]⟩
def cycle97_3 : CycleData E W := ⟨2,![9,19,24,14],![14,16,39,28]⟩
def cycle97_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle97_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data97 : PartitionData E W := ⟨6,![cycle97_0,cycle97_1,cycle97_2,cycle97_3,cycle97_4,cycle97_5]⟩
lemma valid_data97 : data97.Valid src97 dst97 Finset.univ := by decide +kernel

def src98 : E → W := ![2,4,6,3,5,8,2,14,3,16,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst98 : E → W := ![4,6,3,5,8,2,14,3,16,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle98_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle98_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,6,4,28,14]⟩
def cycle98_2 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle98_3 : CycleData E W := ⟨3,![6,13,19,24,10],![2,14,26,39,18]⟩
def cycle98_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle98_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data98 : PartitionData E W := ⟨6,![cycle98_0,cycle98_1,cycle98_2,cycle98_3,cycle98_4,cycle98_5]⟩
lemma valid_data98 : data98.Valid src98 dst98 Finset.univ := by decide +kernel

def src99 : E → W := ![2,4,6,3,5,8,2,14,3,16,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst99 : E → W := ![4,6,3,5,8,2,14,3,16,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle99_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle99_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,6,4,28,14]⟩
def cycle99_2 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle99_3 : CycleData E W := ⟨3,![6,13,17,22,10],![2,14,26,38,18]⟩
def cycle99_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle99_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data99 : PartitionData E W := ⟨6,![cycle99_0,cycle99_1,cycle99_2,cycle99_3,cycle99_4,cycle99_5]⟩
lemma valid_data99 : data99.Valid src99 dst99 Finset.univ := by decide +kernel

def lookupB1 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data50 else (if j < 2 then data51 else data52)) else (if j < 4 then data53 else (if j < 5 then data54 else data55))) else (if j < 9 then (if j < 7 then data56 else (if j < 8 then data57 else data58)) else (if j < 10 then data59 else (if j < 11 then data60 else data61)))) else (if j < 18 then (if j < 15 then (if j < 13 then data62 else (if j < 14 then data63 else data64)) else (if j < 16 then data65 else (if j < 17 then data66 else data67))) else (if j < 21 then (if j < 19 then data68 else (if j < 20 then data69 else data70)) else (if j < 23 then (if j < 22 then data71 else data72) else (if j < 24 then data73 else data74))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data75 else (if j < 27 then data76 else data77)) else (if j < 29 then data78 else (if j < 30 then data79 else data80))) else (if j < 34 then (if j < 32 then data81 else (if j < 33 then data82 else data83)) else (if j < 35 then data84 else (if j < 36 then data85 else data86)))) else (if j < 43 then (if j < 40 then (if j < 38 then data87 else (if j < 39 then data88 else data89)) else (if j < 41 then data90 else (if j < 42 then data91 else data92))) else (if j < 46 then (if j < 44 then data93 else (if j < 45 then data94 else data95)) else (if j < 48 then (if j < 47 then data96 else data97) else (if j < 49 then data98 else data99))))))

def srcTableB1 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src50 else (if j < 2 then src51 else src52)) else (if j < 4 then src53 else (if j < 5 then src54 else src55))) else (if j < 9 then (if j < 7 then src56 else (if j < 8 then src57 else src58)) else (if j < 10 then src59 else (if j < 11 then src60 else src61)))) else (if j < 18 then (if j < 15 then (if j < 13 then src62 else (if j < 14 then src63 else src64)) else (if j < 16 then src65 else (if j < 17 then src66 else src67))) else (if j < 21 then (if j < 19 then src68 else (if j < 20 then src69 else src70)) else (if j < 23 then (if j < 22 then src71 else src72) else (if j < 24 then src73 else src74))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src75 else (if j < 27 then src76 else src77)) else (if j < 29 then src78 else (if j < 30 then src79 else src80))) else (if j < 34 then (if j < 32 then src81 else (if j < 33 then src82 else src83)) else (if j < 35 then src84 else (if j < 36 then src85 else src86)))) else (if j < 43 then (if j < 40 then (if j < 38 then src87 else (if j < 39 then src88 else src89)) else (if j < 41 then src90 else (if j < 42 then src91 else src92))) else (if j < 46 then (if j < 44 then src93 else (if j < 45 then src94 else src95)) else (if j < 48 then (if j < 47 then src96 else src97) else (if j < 49 then src98 else src99))))))

def dstTableB1 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst50 else (if j < 2 then dst51 else dst52)) else (if j < 4 then dst53 else (if j < 5 then dst54 else dst55))) else (if j < 9 then (if j < 7 then dst56 else (if j < 8 then dst57 else dst58)) else (if j < 10 then dst59 else (if j < 11 then dst60 else dst61)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst62 else (if j < 14 then dst63 else dst64)) else (if j < 16 then dst65 else (if j < 17 then dst66 else dst67))) else (if j < 21 then (if j < 19 then dst68 else (if j < 20 then dst69 else dst70)) else (if j < 23 then (if j < 22 then dst71 else dst72) else (if j < 24 then dst73 else dst74))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst75 else (if j < 27 then dst76 else dst77)) else (if j < 29 then dst78 else (if j < 30 then dst79 else dst80))) else (if j < 34 then (if j < 32 then dst81 else (if j < 33 then dst82 else dst83)) else (if j < 35 then dst84 else (if j < 36 then dst85 else dst86)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst87 else (if j < 39 then dst88 else dst89)) else (if j < 41 then dst90 else (if j < 42 then dst91 else dst92))) else (if j < 46 then (if j < 44 then dst93 else (if j < 45 then dst94 else dst95)) else (if j < 48 then (if j < 47 then dst96 else dst97) else (if j < 49 then dst98 else dst99))))))

def caseB1 (i : Fin 50) : Cases := ⟨50 + i.val,by have := i.isLt; omega⟩
lemma tableB1_valid (i : Fin 50) :
    (lookupB1 i.val).Valid (srcTableB1 i.val) (dstTableB1 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data50
  · exact valid_data51
  · exact valid_data52
  · exact valid_data53
  · exact valid_data54
  · exact valid_data55
  · exact valid_data56
  · exact valid_data57
  · exact valid_data58
  · exact valid_data59
  · exact valid_data60
  · exact valid_data61
  · exact valid_data62
  · exact valid_data63
  · exact valid_data64
  · exact valid_data65
  · exact valid_data66
  · exact valid_data67
  · exact valid_data68
  · exact valid_data69
  · exact valid_data70
  · exact valid_data71
  · exact valid_data72
  · exact valid_data73
  · exact valid_data74
  · exact valid_data75
  · exact valid_data76
  · exact valid_data77
  · exact valid_data78
  · exact valid_data79
  · exact valid_data80
  · exact valid_data81
  · exact valid_data82
  · exact valid_data83
  · exact valid_data84
  · exact valid_data85
  · exact valid_data86
  · exact valid_data87
  · exact valid_data88
  · exact valid_data89
  · exact valid_data90
  · exact valid_data91
  · exact valid_data92
  · exact valid_data93
  · exact valid_data94
  · exact valid_data95
  · exact valid_data96
  · exact valid_data97
  · exact valid_data98
  · exact valid_data99

lemma srcB1_row : ∀ (i : Fin 50) (e : E),
    srcTableB1 i.val e = caseSource (caseB1 i) e := by decide +kernel

lemma dstB1_row : ∀ (i : Fin 50) (e : E),
    dstTableB1 i.val e = caseTarget (caseB1 i) e := by decide +kernel

lemma sizeB1 : ∀ i : Fin 50, (lookupB1 i.val).size ≤ 5 →
    (lookupB1 i.val).size = 2 ∧
      (⟨caseKey (caseB1 i),caseKey_lt (caseB1 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB1 (i : Fin 50) : Certificate (caseB1 i) := by
  refine ⟨lookupB1 i.val,?_,sizeB1 i⟩
  have hv := tableB1_valid i
  rw [funext (srcB1_row i),funext (dstB1_row i)] at hv
  exact hv
lemma certificateInterval1 : FiniteIntervals.Covers CertificateAt 50 100 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 50 50 (fun i _ => certificateB1 i)
#print axioms certificateInterval1
end Erdos184Work.FiveRows4

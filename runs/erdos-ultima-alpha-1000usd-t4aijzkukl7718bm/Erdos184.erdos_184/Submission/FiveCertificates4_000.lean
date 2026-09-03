import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst0 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle0_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle0_1 : CycleData E W := ⟨3,![2,13,14,23,9],![3,5,14,28,18]⟩
def cycle0_2 : CycleData E W := ⟨2,![3,20,19,12],![5,6,39,26]⟩
def cycle0_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle0_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle0_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data0 : PartitionData E W := ⟨6,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst1 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle1_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle1_1 : CycleData E W := ⟨3,![2,13,14,23,9],![3,5,14,28,18]⟩
def cycle1_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,38,26]⟩
def cycle1_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle1_4 : CycleData E W := ⟨2,![5,21,22,10],![2,8,38,18]⟩
def cycle1_5 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def data1 : PartitionData E W := ⟨6,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4,cycle1_5]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst2 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle2_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle2_1 : CycleData E W := ⟨3,![2,13,12,18,9],![3,5,14,26,16]⟩
def cycle2_2 : CycleData E W := ⟨2,![3,16,22,14],![5,6,38,28]⟩
def cycle2_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle2_4 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle2_5 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def data2 : PartitionData E W := ⟨6,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4,cycle2_5]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst3 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle3_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle3_1 : CycleData E W := ⟨3,![2,13,12,18,9],![3,5,14,26,16]⟩
def cycle3_2 : CycleData E W := ⟨2,![3,20,24,14],![5,6,39,28]⟩
def cycle3_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle3_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle3_5 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def data3 : PartitionData E W := ⟨6,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4,cycle3_5]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst4 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle4_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle4_1 : CycleData E W := ⟨3,![2,13,14,23,9],![3,5,14,28,18]⟩
def cycle4_2 : CycleData E W := ⟨2,![3,25,19,12],![5,8,39,26]⟩
def cycle4_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle4_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle4_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data4 : PartitionData E W := ⟨6,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4,cycle4_5]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst5 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle5_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle5_1 : CycleData E W := ⟨3,![2,13,14,23,9],![3,5,14,28,18]⟩
def cycle5_2 : CycleData E W := ⟨2,![3,21,17,12],![5,8,38,26]⟩
def cycle5_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle5_4 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle5_5 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def data5 : PartitionData E W := ⟨6,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4,cycle5_5]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst6 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle6_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle6_1 : CycleData E W := ⟨3,![2,13,12,18,9],![3,5,14,26,16]⟩
def cycle6_2 : CycleData E W := ⟨2,![3,21,22,14],![5,8,38,28]⟩
def cycle6_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle6_4 : CycleData E W := ⟨2,![5,16,17,10],![2,6,38,16]⟩
def cycle6_5 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def data6 : PartitionData E W := ⟨6,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4,cycle6_5]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst7 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle7_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle7_1 : CycleData E W := ⟨3,![2,13,12,18,9],![3,5,14,26,16]⟩
def cycle7_2 : CycleData E W := ⟨2,![3,25,24,14],![5,8,39,28]⟩
def cycle7_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle7_4 : CycleData E W := ⟨2,![5,20,19,10],![2,6,39,16]⟩
def cycle7_5 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def data7 : PartitionData E W := ⟨6,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,5,14,26,28,6,38,16,26,39,8,38,28,18,39]
def dst8 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,5,14,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle8_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle8_1 : CycleData E W := ⟨4,![2,3,11,15,23,8],![3,6,5,4,28,18]⟩
def cycle8_2 : CycleData E W := ⟨2,![5,4,12,6],![2,8,5,14]⟩
def cycle8_3 : CycleData E W := ⟨2,![7,24,19,13],![14,18,39,26]⟩
def cycle8_4 : CycleData E W := ⟨2,![17,22,14,18],![16,38,28,26]⟩
def cycle8_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data8 : PartitionData E W := ⟨6,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4,cycle8_5]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,5,14,26,28,6,38,26,16,39,8,38,18,28,39]
def dst9 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,5,14,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle9_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle9_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle9_2 : CycleData E W := ⟨3,![11,3,20,24,15],![4,5,6,39,28]⟩
def cycle9_3 : CycleData E W := ⟨2,![5,4,12,6],![2,8,5,14]⟩
def cycle9_4 : CycleData E W := ⟨2,![7,23,14,13],![14,18,28,26]⟩
def cycle9_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data9 : PartitionData E W := ⟨6,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4,cycle9_5]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,5,14,28,26,6,38,16,26,39,8,38,28,18,39]
def dst10 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,5,14,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle10_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle10_1 : CycleData E W := ⟨5,![2,3,11,15,19,24,8],![3,6,5,4,26,39,18]⟩
def cycle10_2 : CycleData E W := ⟨2,![5,4,12,6],![2,8,5,14]⟩
def cycle10_3 : CycleData E W := ⟨1,![7,23,13],![14,18,28]⟩
def cycle10_4 : CycleData E W := ⟨2,![17,22,14,18],![16,38,28,26]⟩
def cycle10_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data10 : PartitionData E W := ⟨6,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4,cycle10_5]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,5,14,28,26,6,38,26,16,39,8,38,18,28,39]
def dst11 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,5,14,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle11_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle11_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle11_2 : CycleData E W := ⟨4,![11,3,20,19,18,15],![4,5,6,39,16,26]⟩
def cycle11_3 : CycleData E W := ⟨2,![5,4,12,6],![2,8,5,14]⟩
def cycle11_4 : CycleData E W := ⟨1,![7,23,13],![14,18,28]⟩
def cycle11_5 : CycleData E W := ⟨3,![21,17,14,24,25],![8,38,26,28,39]⟩
def data11 : PartitionData E W := ⟨6,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4,cycle11_5]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst12 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle12_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle12_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle12_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle12_3 : CycleData E W := ⟨2,![4,25,24,14],![5,8,39,28]⟩
def cycle12_4 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle12_5 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def data12 : PartitionData E W := ⟨6,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4,cycle12_5]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst13 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle13_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle13_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle13_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle13_3 : CycleData E W := ⟨3,![4,25,24,23,14],![5,8,39,18,28]⟩
def cycle13_4 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle13_5 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def data13 : PartitionData E W := ⟨6,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4,cycle13_5]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst14 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle14_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle14_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,38,16]⟩
def cycle14_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle14_3 : CycleData E W := ⟨3,![4,21,22,23,14],![5,8,38,18,28]⟩
def cycle14_4 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle14_5 : CycleData E W := ⟨2,![11,17,24,15],![4,26,39,28]⟩
def data14 : PartitionData E W := ⟨6,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4,cycle14_5]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst15 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle15_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle15_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,38,16]⟩
def cycle15_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle15_3 : CycleData E W := ⟨2,![4,21,22,14],![5,8,38,28]⟩
def cycle15_4 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle15_5 : CycleData E W := ⟨3,![11,17,24,23,15],![4,26,39,18,28]⟩
def data15 : PartitionData E W := ⟨6,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4,cycle15_5]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst16 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle16_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle16_1 : CycleData E W := ⟨3,![2,3,13,7,8],![3,6,5,14,18]⟩
def cycle16_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle16_3 : CycleData E W := ⟨3,![5,25,19,12,6],![2,8,39,26,14]⟩
def cycle16_4 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def cycle16_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data16 : PartitionData E W := ⟨6,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4,cycle16_5]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst17 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle17_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle17_1 : CycleData E W := ⟨4,![2,3,13,12,18,9],![3,6,5,14,26,16]⟩
def cycle17_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle17_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle17_4 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def cycle17_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data17 : PartitionData E W := ⟨6,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4,cycle17_5]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst18 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle18_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle18_1 : CycleData E W := ⟨3,![2,3,14,23,8],![3,6,5,28,18]⟩
def cycle18_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle18_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle18_4 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def cycle18_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data18 : PartitionData E W := ⟨6,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4,cycle18_5]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst19 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle19_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle19_1 : CycleData E W := ⟨4,![2,3,13,12,18,9],![3,6,5,14,26,16]⟩
def cycle19_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle19_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle19_4 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def cycle19_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data19 : PartitionData E W := ⟨6,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4,cycle19_5]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst20 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle20_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle20_1 : CycleData E W := ⟨3,![2,3,13,7,8],![3,6,5,14,18]⟩
def cycle20_2 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle20_3 : CycleData E W := ⟨3,![5,25,17,12,6],![2,8,38,26,14]⟩
def cycle20_4 : CycleData E W := ⟨3,![11,18,19,22,15],![4,26,16,39,28]⟩
def cycle20_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data20 : PartitionData E W := ⟨6,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4,cycle20_5]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,3,6,5,8,2,14,18,3,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst21 : E → W := ![4,3,6,5,8,2,14,18,3,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle21_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle21_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle21_2 : CycleData E W := ⟨2,![3,20,24,14],![5,6,39,28]⟩
def cycle21_3 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle21_4 : CycleData E W := ⟨3,![11,12,7,23,15],![4,26,14,18,28]⟩
def cycle21_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data21 : PartitionData E W := ⟨6,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4,cycle21_5]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,5,14,26,28,6,38,16,26,39,8,38,28,18,39]
def dst22 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,5,14,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle22_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle22_1 : CycleData E W := ⟨2,![2,3,12,8],![3,6,5,14]⟩
def cycle22_2 : CycleData E W := ⟨5,![5,4,11,15,22,17,6],![2,8,5,4,28,38,16]⟩
def cycle22_3 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle22_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle22_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data22 : PartitionData E W := ⟨6,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4,cycle22_5]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,5,14,26,28,6,38,26,16,39,8,38,18,28,39]
def dst23 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,5,14,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle23_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle23_1 : CycleData E W := ⟨2,![2,3,12,8],![3,6,5,14]⟩
def cycle23_2 : CycleData E W := ⟨4,![11,4,21,17,14,15],![4,5,8,38,26,28]⟩
def cycle23_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle23_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle23_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data23 : PartitionData E W := ⟨6,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4,cycle23_5]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,5,14,28,26,6,38,16,26,39,8,38,28,18,39]
def dst24 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,5,14,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle24_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle24_1 : CycleData E W := ⟨2,![2,3,12,8],![3,6,5,14]⟩
def cycle24_2 : CycleData E W := ⟨4,![5,4,11,15,18,6],![2,8,5,4,26,16]⟩
def cycle24_3 : CycleData E W := ⟨2,![7,17,22,13],![14,16,38,28]⟩
def cycle24_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle24_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data24 : PartitionData E W := ⟨6,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4,cycle24_5]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,5,14,28,26,6,38,26,16,39,8,38,18,28,39]
def dst25 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,5,14,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle25_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle25_1 : CycleData E W := ⟨2,![2,3,12,8],![3,6,5,14]⟩
def cycle25_2 : CycleData E W := ⟨4,![5,4,11,15,18,6],![2,8,5,4,26,16]⟩
def cycle25_3 : CycleData E W := ⟨2,![7,19,24,13],![14,16,39,28]⟩
def cycle25_4 : CycleData E W := ⟨2,![22,17,14,23],![18,38,26,28]⟩
def cycle25_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data25 : PartitionData E W := ⟨6,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4,cycle25_5]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst26 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle26_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle26_1 : CycleData E W := ⟨2,![2,3,13,8],![3,6,5,14]⟩
def cycle26_2 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle26_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle26_4 : CycleData E W := ⟨3,![7,18,22,23,14],![14,16,38,18,28]⟩
def cycle26_5 : CycleData E W := ⟨3,![11,16,20,24,15],![4,26,6,39,28]⟩
def data26 : PartitionData E W := ⟨6,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4,cycle26_5]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst27 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle27_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle27_1 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle27_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle27_3 : CycleData E W := ⟨4,![5,4,13,14,23,10],![2,8,5,14,28,18]⟩
def cycle27_4 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def cycle27_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data27 : PartitionData E W := ⟨6,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4,cycle27_5]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst28 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle28_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle28_1 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle28_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle28_3 : CycleData E W := ⟨4,![5,4,13,14,23,10],![2,8,5,14,28,18]⟩
def cycle28_4 : CycleData E W := ⟨2,![11,17,24,15],![4,26,39,28]⟩
def cycle28_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data28 : PartitionData E W := ⟨6,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4,cycle28_5]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst29 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle29_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle29_1 : CycleData E W := ⟨2,![2,3,13,8],![3,6,5,14]⟩
def cycle29_2 : CycleData E W := ⟨3,![4,21,20,16,12],![5,8,38,6,26]⟩
def cycle29_3 : CycleData E W := ⟨2,![5,25,18,6],![2,8,39,16]⟩
def cycle29_4 : CycleData E W := ⟨2,![7,19,22,14],![14,16,38,28]⟩
def cycle29_5 : CycleData E W := ⟨3,![11,17,24,23,15],![4,26,39,18,28]⟩
def data29 : PartitionData E W := ⟨6,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4,cycle29_5]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst30 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle30_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle30_1 : CycleData E W := ⟨2,![2,16,23,9],![3,6,38,18]⟩
def cycle30_2 : CycleData E W := ⟨2,![3,20,19,12],![5,6,39,26]⟩
def cycle30_3 : CycleData E W := ⟨2,![4,21,14,13],![5,8,28,14]⟩
def cycle30_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle30_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data30 : PartitionData E W := ⟨6,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4,cycle30_5]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst31 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle31_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle31_1 : CycleData E W := ⟨2,![2,20,23,9],![3,6,39,18]⟩
def cycle31_2 : CycleData E W := ⟨3,![3,16,17,18,12],![5,6,38,16,26]⟩
def cycle31_3 : CycleData E W := ⟨2,![4,21,14,13],![5,8,28,14]⟩
def cycle31_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,38,18]⟩
def cycle31_5 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def data31 : PartitionData E W := ⟨6,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4,cycle31_5]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst32 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle32_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle32_1 : CycleData E W := ⟨2,![2,3,13,8],![3,6,5,14]⟩
def cycle32_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle32_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle32_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle32_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data32 : PartitionData E W := ⟨6,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4,cycle32_5]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst33 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle33_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle33_1 : CycleData E W := ⟨2,![2,16,23,9],![3,6,38,18]⟩
def cycle33_2 : CycleData E W := ⟨3,![3,20,19,18,12],![5,6,39,16,26]⟩
def cycle33_3 : CycleData E W := ⟨2,![4,21,14,13],![5,8,28,14]⟩
def cycle33_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle33_5 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def data33 : PartitionData E W := ⟨6,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4,cycle33_5]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst34 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle34_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle34_1 : CycleData E W := ⟨2,![2,20,23,9],![3,6,39,18]⟩
def cycle34_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,38,26]⟩
def cycle34_3 : CycleData E W := ⟨2,![4,21,14,13],![5,8,28,14]⟩
def cycle34_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,38,18]⟩
def cycle34_5 : CycleData E W := ⟨3,![11,18,19,22,15],![4,26,16,39,28]⟩
def data34 : PartitionData E W := ⟨6,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4,cycle34_5]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,3,6,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst35 : E → W := ![4,3,6,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle35_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle35_1 : CycleData E W := ⟨2,![2,3,13,8],![3,6,5,14]⟩
def cycle35_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle35_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle35_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle35_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data35 : PartitionData E W := ⟨6,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4,cycle35_5]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def src36 : E → W := ![2,4,3,6,8,5,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst36 : E → W := ![4,3,6,8,5,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle36_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle36_1 : CycleData E W := ⟨3,![2,3,4,13,8],![3,6,8,5,14]⟩
def cycle36_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle36_3 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle36_4 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def cycle36_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data36 : PartitionData E W := ⟨6,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4,cycle36_5]⟩
lemma valid_data36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel

def src37 : E → W := ![2,4,3,6,8,5,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst37 : E → W := ![4,3,6,8,5,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle37_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,16]⟩
def cycle37_1 : CycleData E W := ⟨3,![2,3,4,13,8],![3,6,8,5,14]⟩
def cycle37_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle37_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle37_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle37_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data37 : PartitionData E W := ⟨6,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4,cycle37_5]⟩
lemma valid_data37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel

def src38 : E → W := ![2,4,3,6,8,5,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst38 : E → W := ![4,3,6,8,5,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle38_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle38_1 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle38_2 : CycleData E W := ⟨1,![3,21,16],![6,8,38]⟩
def cycle38_3 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle38_4 : CycleData E W := ⟨3,![5,13,14,23,10],![2,5,14,28,18]⟩
def cycle38_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data38 : PartitionData E W := ⟨6,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4,cycle38_5]⟩
lemma valid_data38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel

def src39 : E → W := ![2,4,3,6,8,5,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst39 : E → W := ![4,3,6,8,5,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle39_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,14,16]⟩
def cycle39_1 : CycleData E W := ⟨2,![2,16,22,9],![3,6,38,18]⟩
def cycle39_2 : CycleData E W := ⟨1,![3,25,20],![6,8,39]⟩
def cycle39_3 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle39_4 : CycleData E W := ⟨3,![5,13,14,23,10],![2,5,14,28,18]⟩
def cycle39_5 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def data39 : PartitionData E W := ⟨6,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4,cycle39_5]⟩
lemma valid_data39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel

def src40 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,5,14,26,28,6,38,16,26,39,8,38,28,18,39]
def dst40 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,5,14,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle40_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle40_1 : CycleData E W := ⟨2,![2,21,17,8],![3,8,38,16]⟩
def cycle40_2 : CycleData E W := ⟨4,![11,3,25,19,14,15],![4,5,8,39,26,28]⟩
def cycle40_3 : CycleData E W := ⟨2,![5,4,12,6],![2,6,5,14]⟩
def cycle40_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle40_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data40 : PartitionData E W := ⟨6,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4,cycle40_5]⟩
lemma valid_data40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel

def src41 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,5,14,26,28,6,38,26,16,39,8,38,18,28,39]
def dst41 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,5,14,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle41_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle41_1 : CycleData E W := ⟨4,![2,21,16,20,19,8],![3,8,38,6,39,16]⟩
def cycle41_2 : CycleData E W := ⟨3,![11,3,25,24,15],![4,5,8,39,28]⟩
def cycle41_3 : CycleData E W := ⟨2,![5,4,12,6],![2,6,5,14]⟩
def cycle41_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle41_5 : CycleData E W := ⟨2,![22,17,14,23],![18,38,26,28]⟩
def data41 : PartitionData E W := ⟨6,![cycle41_0,cycle41_1,cycle41_2,cycle41_3,cycle41_4,cycle41_5]⟩
lemma valid_data41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel

def src42 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,5,14,28,26,6,38,16,26,39,8,38,28,18,39]
def dst42 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,5,14,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle42_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle42_1 : CycleData E W := ⟨4,![2,3,11,15,18,8],![3,8,5,4,26,16]⟩
def cycle42_2 : CycleData E W := ⟨2,![5,4,12,6],![2,6,5,14]⟩
def cycle42_3 : CycleData E W := ⟨2,![7,17,22,13],![14,16,38,28]⟩
def cycle42_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle42_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data42 : PartitionData E W := ⟨6,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4,cycle42_5]⟩
lemma valid_data42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel

def src43 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,5,14,28,26,6,38,26,16,39,8,38,18,28,39]
def dst43 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,5,14,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle43_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle43_1 : CycleData E W := ⟨4,![2,3,11,15,18,8],![3,8,5,4,26,16]⟩
def cycle43_2 : CycleData E W := ⟨2,![5,4,12,6],![2,6,5,14]⟩
def cycle43_3 : CycleData E W := ⟨2,![7,19,24,13],![14,16,39,28]⟩
def cycle43_4 : CycleData E W := ⟨2,![22,17,14,23],![18,38,26,28]⟩
def cycle43_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data43 : PartitionData E W := ⟨6,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4,cycle43_5]⟩
lemma valid_data43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel

def src44 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst44 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle44_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle44_1 : CycleData E W := ⟨3,![2,3,13,7,8],![3,8,5,14,16]⟩
def cycle44_2 : CycleData E W := ⟨1,![4,16,12],![5,6,26]⟩
def cycle44_3 : CycleData E W := ⟨3,![5,20,24,14,6],![2,6,39,28,14]⟩
def cycle44_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle44_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data44 : PartitionData E W := ⟨6,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4,cycle44_5]⟩
lemma valid_data44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel

def src45 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst45 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle45_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle45_1 : CycleData E W := ⟨4,![2,3,13,14,23,9],![3,8,5,14,28,18]⟩
def cycle45_2 : CycleData E W := ⟨1,![4,16,12],![5,6,26]⟩
def cycle45_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle45_4 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def cycle45_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data45 : PartitionData E W := ⟨6,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4,cycle45_5]⟩
lemma valid_data45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel

def src46 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst46 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle46_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle46_1 : CycleData E W := ⟨4,![2,3,13,14,23,9],![3,8,5,14,28,18]⟩
def cycle46_2 : CycleData E W := ⟨1,![4,16,12],![5,6,26]⟩
def cycle46_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle46_4 : CycleData E W := ⟨2,![11,17,24,15],![4,26,39,28]⟩
def cycle46_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data46 : PartitionData E W := ⟨6,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4,cycle46_5]⟩
lemma valid_data46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel

def src47 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst47 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle47_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle47_1 : CycleData E W := ⟨3,![2,3,13,7,8],![3,8,5,14,16]⟩
def cycle47_2 : CycleData E W := ⟨1,![4,16,12],![5,6,26]⟩
def cycle47_3 : CycleData E W := ⟨3,![5,20,22,14,6],![2,6,38,28,14]⟩
def cycle47_4 : CycleData E W := ⟨3,![11,17,24,23,15],![4,26,39,18,28]⟩
def cycle47_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data47 : PartitionData E W := ⟨6,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4,cycle47_5]⟩
lemma valid_data47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel

def src48 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst48 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle48_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle48_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,39,18]⟩
def cycle48_2 : CycleData E W := ⟨2,![3,21,14,13],![5,8,28,14]⟩
def cycle48_3 : CycleData E W := ⟨2,![4,20,19,12],![5,6,39,26]⟩
def cycle48_4 : CycleData E W := ⟨2,![5,16,23,10],![2,6,38,18]⟩
def cycle48_5 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def data48 : PartitionData E W := ⟨6,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4,cycle48_5]⟩
lemma valid_data48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel

def src49 : E → W := ![2,4,3,8,5,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst49 : E → W := ![4,3,8,5,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle49_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle49_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,38,18]⟩
def cycle49_2 : CycleData E W := ⟨2,![3,21,14,13],![5,8,28,14]⟩
def cycle49_3 : CycleData E W := ⟨3,![4,16,17,18,12],![5,6,38,16,26]⟩
def cycle49_4 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle49_5 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def data49 : PartitionData E W := ⟨6,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4,cycle49_5]⟩
lemma valid_data49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel

def lookupB0 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data0 else (if j < 2 then data1 else data2)) else (if j < 4 then data3 else (if j < 5 then data4 else data5))) else (if j < 9 then (if j < 7 then data6 else (if j < 8 then data7 else data8)) else (if j < 10 then data9 else (if j < 11 then data10 else data11)))) else (if j < 18 then (if j < 15 then (if j < 13 then data12 else (if j < 14 then data13 else data14)) else (if j < 16 then data15 else (if j < 17 then data16 else data17))) else (if j < 21 then (if j < 19 then data18 else (if j < 20 then data19 else data20)) else (if j < 23 then (if j < 22 then data21 else data22) else (if j < 24 then data23 else data24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data25 else (if j < 27 then data26 else data27)) else (if j < 29 then data28 else (if j < 30 then data29 else data30))) else (if j < 34 then (if j < 32 then data31 else (if j < 33 then data32 else data33)) else (if j < 35 then data34 else (if j < 36 then data35 else data36)))) else (if j < 43 then (if j < 40 then (if j < 38 then data37 else (if j < 39 then data38 else data39)) else (if j < 41 then data40 else (if j < 42 then data41 else data42))) else (if j < 46 then (if j < 44 then data43 else (if j < 45 then data44 else data45)) else (if j < 48 then (if j < 47 then data46 else data47) else (if j < 49 then data48 else data49))))))

def srcTableB0 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src0 else (if j < 2 then src1 else src2)) else (if j < 4 then src3 else (if j < 5 then src4 else src5))) else (if j < 9 then (if j < 7 then src6 else (if j < 8 then src7 else src8)) else (if j < 10 then src9 else (if j < 11 then src10 else src11)))) else (if j < 18 then (if j < 15 then (if j < 13 then src12 else (if j < 14 then src13 else src14)) else (if j < 16 then src15 else (if j < 17 then src16 else src17))) else (if j < 21 then (if j < 19 then src18 else (if j < 20 then src19 else src20)) else (if j < 23 then (if j < 22 then src21 else src22) else (if j < 24 then src23 else src24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src25 else (if j < 27 then src26 else src27)) else (if j < 29 then src28 else (if j < 30 then src29 else src30))) else (if j < 34 then (if j < 32 then src31 else (if j < 33 then src32 else src33)) else (if j < 35 then src34 else (if j < 36 then src35 else src36)))) else (if j < 43 then (if j < 40 then (if j < 38 then src37 else (if j < 39 then src38 else src39)) else (if j < 41 then src40 else (if j < 42 then src41 else src42))) else (if j < 46 then (if j < 44 then src43 else (if j < 45 then src44 else src45)) else (if j < 48 then (if j < 47 then src46 else src47) else (if j < 49 then src48 else src49))))))

def dstTableB0 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst0 else (if j < 2 then dst1 else dst2)) else (if j < 4 then dst3 else (if j < 5 then dst4 else dst5))) else (if j < 9 then (if j < 7 then dst6 else (if j < 8 then dst7 else dst8)) else (if j < 10 then dst9 else (if j < 11 then dst10 else dst11)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst12 else (if j < 14 then dst13 else dst14)) else (if j < 16 then dst15 else (if j < 17 then dst16 else dst17))) else (if j < 21 then (if j < 19 then dst18 else (if j < 20 then dst19 else dst20)) else (if j < 23 then (if j < 22 then dst21 else dst22) else (if j < 24 then dst23 else dst24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst25 else (if j < 27 then dst26 else dst27)) else (if j < 29 then dst28 else (if j < 30 then dst29 else dst30))) else (if j < 34 then (if j < 32 then dst31 else (if j < 33 then dst32 else dst33)) else (if j < 35 then dst34 else (if j < 36 then dst35 else dst36)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst37 else (if j < 39 then dst38 else dst39)) else (if j < 41 then dst40 else (if j < 42 then dst41 else dst42))) else (if j < 46 then (if j < 44 then dst43 else (if j < 45 then dst44 else dst45)) else (if j < 48 then (if j < 47 then dst46 else dst47) else (if j < 49 then dst48 else dst49))))))

def caseB0 (i : Fin 50) : Cases := ⟨0 + i.val,by have := i.isLt; omega⟩
lemma tableB0_valid (i : Fin 50) :
    (lookupB0 i.val).Valid (srcTableB0 i.val) (dstTableB0 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data0
  · exact valid_data1
  · exact valid_data2
  · exact valid_data3
  · exact valid_data4
  · exact valid_data5
  · exact valid_data6
  · exact valid_data7
  · exact valid_data8
  · exact valid_data9
  · exact valid_data10
  · exact valid_data11
  · exact valid_data12
  · exact valid_data13
  · exact valid_data14
  · exact valid_data15
  · exact valid_data16
  · exact valid_data17
  · exact valid_data18
  · exact valid_data19
  · exact valid_data20
  · exact valid_data21
  · exact valid_data22
  · exact valid_data23
  · exact valid_data24
  · exact valid_data25
  · exact valid_data26
  · exact valid_data27
  · exact valid_data28
  · exact valid_data29
  · exact valid_data30
  · exact valid_data31
  · exact valid_data32
  · exact valid_data33
  · exact valid_data34
  · exact valid_data35
  · exact valid_data36
  · exact valid_data37
  · exact valid_data38
  · exact valid_data39
  · exact valid_data40
  · exact valid_data41
  · exact valid_data42
  · exact valid_data43
  · exact valid_data44
  · exact valid_data45
  · exact valid_data46
  · exact valid_data47
  · exact valid_data48
  · exact valid_data49

lemma srcB0_row : ∀ (i : Fin 50) (e : E),
    srcTableB0 i.val e = caseSource (caseB0 i) e := by decide +kernel

lemma dstB0_row : ∀ (i : Fin 50) (e : E),
    dstTableB0 i.val e = caseTarget (caseB0 i) e := by decide +kernel

lemma sizeB0 : ∀ i : Fin 50, (lookupB0 i.val).size ≤ 5 →
    (lookupB0 i.val).size = 2 ∧
      (⟨caseKey (caseB0 i),caseKey_lt (caseB0 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB0 (i : Fin 50) : Certificate (caseB0 i) := by
  refine ⟨lookupB0 i.val,?_,sizeB0 i⟩
  have hv := tableB0_valid i
  rw [funext (srcB0_row i),funext (dstB0_row i)] at hv
  exact hv
lemma certificateInterval0 : FiniteIntervals.Covers CertificateAt 0 50 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 0 50 (fun i _ => certificateB0 i)
#print axioms certificateInterval0
end Erdos184Work.FiveRows4

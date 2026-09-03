import Submission.FiveCertificates2Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,26,38,8,18,28,38]
def dst0 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle0_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle0_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle0_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle0_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle0_4 : CycleData E W := ⟨3,![5,20,21,13,10],![2,8,18,28,14]⟩
def cycle0_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data0 : PartitionData E W := ⟨6,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,26,38,8,18,38,28]
def dst1 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle1_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle1_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle1_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle1_4 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle1_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1 : PartitionData E W := ⟨6,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4,cycle1_5]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,26,38,8,28,18,38]
def dst2 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle2_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle2_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle2_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle2_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle2_4 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle2_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data2 : PartitionData E W := ⟨6,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4,cycle2_5]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,38,26,8,18,28,38]
def dst3 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle3_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle3_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle3_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle3_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle3_4 : CycleData E W := ⟨3,![5,20,21,13,10],![2,8,18,28,14]⟩
def cycle3_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data3 : PartitionData E W := ⟨6,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4,cycle3_5]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,38,26,8,18,38,28]
def dst4 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle4_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle4_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle4_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle4_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle4_4 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle4_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data4 : PartitionData E W := ⟨6,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4,cycle4_5]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,16,38,26,8,28,18,38]
def dst5 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle5_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle5_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle5_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle5_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle5_4 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle5_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data5 : PartitionData E W := ⟨6,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4,cycle5_5]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,26,16,38,8,18,28,38]
def dst6 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle6_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle6_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle6_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle6_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle6_4 : CycleData E W := ⟨3,![5,20,21,13,10],![2,8,18,28,14]⟩
def cycle6_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data6 : PartitionData E W := ⟨6,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4,cycle6_5]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,26,16,38,8,18,38,28]
def dst7 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle7_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle7_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle7_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle7_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle7_4 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle7_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data7 : PartitionData E W := ⟨6,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,5,14,28,26,6,26,16,38,8,28,18,38]
def dst8 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,5,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle8_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle8_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,16,18]⟩
def cycle8_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle8_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle8_4 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle8_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data8 : PartitionData E W := ⟨6,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4,cycle8_5]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,18,28,38]
def dst9 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,18,28,38,8]
def cycle9_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle9_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle9_2 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle9_3 : CycleData E W := ⟨4,![5,20,21,13,12,10],![2,8,18,28,5,14]⟩
def cycle9_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle9_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data9 : PartitionData E W := ⟨6,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4,cycle9_5]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,18,38,28]
def dst10 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,18,38,28,8]
def cycle10_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle10_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle10_2 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle10_3 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle10_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle10_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data10 : PartitionData E W := ⟨6,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4,cycle10_5]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,28,18,38]
def dst11 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,28,18,38,8]
def cycle11_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle11_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle11_2 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle11_3 : CycleData E W := ⟨3,![5,20,13,12,10],![2,8,28,5,14]⟩
def cycle11_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle11_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data11 : PartitionData E W := ⟨6,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4,cycle11_5]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,18,28,38]
def dst12 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,18,28,38,8]
def cycle12_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle12_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle12_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,8,6,5,14]⟩
def cycle12_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle12_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle12_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data12 : PartitionData E W := ⟨6,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4,cycle12_5]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,18,38,28]
def dst13 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,18,38,28,8]
def cycle13_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle13_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,5,6,8,18]⟩
def cycle13_2 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle13_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle13_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle13_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data13 : PartitionData E W := ⟨6,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4,cycle13_5]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,28,18,38]
def dst14 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,28,18,38,8]
def cycle14_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle14_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle14_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,8,6,5,14]⟩
def cycle14_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle14_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle14_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data14 : PartitionData E W := ⟨6,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4,cycle14_5]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,18,28,38]
def dst15 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,18,28,38,8]
def cycle15_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle15_1 : CycleData E W := ⟨4,![5,20,7,2,12,10],![2,8,18,3,5,14]⟩
def cycle15_2 : CycleData E W := ⟨2,![3,16,14,13],![5,6,26,28]⟩
def cycle15_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle15_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle15_5 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def data15 : PartitionData E W := ⟨6,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4,cycle15_5]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,18,38,28]
def dst16 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,18,38,28,8]
def cycle16_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle16_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,5,6,8,18]⟩
def cycle16_2 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle16_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle16_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle16_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data16 : PartitionData E W := ⟨6,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4,cycle16_5]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,28,18,38]
def dst17 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,28,18,38,8]
def cycle17_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle17_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle17_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,8,6,5,14]⟩
def cycle17_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle17_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle17_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data17 : PartitionData E W := ⟨6,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4,cycle17_5]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst18 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle18_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle18_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle18_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle18_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle18_4 : CycleData E W := ⟨3,![5,20,21,14,10],![2,8,18,28,14]⟩
def cycle18_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data18 : PartitionData E W := ⟨6,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4,cycle18_5]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst19 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle19_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle19_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle19_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle19_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle19_4 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle19_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data19 : PartitionData E W := ⟨6,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4,cycle19_5]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst20 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle20_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle20_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle20_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle20_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle20_4 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle20_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data20 : PartitionData E W := ⟨6,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4,cycle20_5]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst21 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle21_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle21_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle21_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle21_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle21_4 : CycleData E W := ⟨3,![5,20,21,14,10],![2,8,18,28,14]⟩
def cycle21_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data21 : PartitionData E W := ⟨6,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4,cycle21_5]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst22 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle22_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle22_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle22_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle22_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle22_4 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle22_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data22 : PartitionData E W := ⟨6,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4,cycle22_5]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst23 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle23_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle23_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle23_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle23_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle23_4 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle23_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data23 : PartitionData E W := ⟨6,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4,cycle23_5]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst24 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle24_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle24_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle24_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle24_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle24_4 : CycleData E W := ⟨3,![5,20,21,14,10],![2,8,18,28,14]⟩
def cycle24_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data24 : PartitionData E W := ⟨6,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4,cycle24_5]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst25 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle25_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle25_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle25_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle25_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle25_4 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle25_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data25 : PartitionData E W := ⟨6,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4,cycle25_5]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst26 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle26_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle26_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,16,18]⟩
def cycle26_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle26_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle26_4 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle26_5 : CycleData E W := ⟨4,![11,17,18,22,21,15],![4,26,16,38,18,28]⟩
def data26 : PartitionData E W := ⟨6,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4,cycle26_5]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst27 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle27_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle27_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle27_2 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle27_3 : CycleData E W := ⟨4,![5,20,21,14,13,10],![2,8,18,28,5,14]⟩
def cycle27_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle27_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data27 : PartitionData E W := ⟨6,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4,cycle27_5]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst28 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle28_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle28_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle28_2 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle28_3 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle28_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle28_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data28 : PartitionData E W := ⟨6,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4,cycle28_5]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst29 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle29_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle29_1 : CycleData E W := ⟨3,![2,3,16,8,7],![3,5,6,16,18]⟩
def cycle29_2 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle29_3 : CycleData E W := ⟨3,![5,20,14,13,10],![2,8,28,5,14]⟩
def cycle29_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle29_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data29 : PartitionData E W := ⟨6,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4,cycle29_5]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst30 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle30_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle30_1 : CycleData E W := ⟨2,![2,14,21,7],![3,5,28,18]⟩
def cycle30_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,8,6,5,14]⟩
def cycle30_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle30_4 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def cycle30_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data30 : PartitionData E W := ⟨6,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4,cycle30_5]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst31 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle31_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle31_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,5,6,8,18]⟩
def cycle31_2 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle31_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle31_4 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def cycle31_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data31 : PartitionData E W := ⟨6,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4,cycle31_5]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst32 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle32_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle32_1 : CycleData E W := ⟨2,![2,14,21,7],![3,5,28,18]⟩
def cycle32_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,8,6,5,14]⟩
def cycle32_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle32_4 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def cycle32_5 : CycleData E W := ⟨3,![11,18,23,20,15],![4,26,38,8,28]⟩
def data32 : PartitionData E W := ⟨6,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4,cycle32_5]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst33 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle33_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle33_1 : CycleData E W := ⟨4,![5,20,7,2,13,10],![2,8,18,3,5,14]⟩
def cycle33_2 : CycleData E W := ⟨3,![11,16,3,14,15],![4,26,6,5,28]⟩
def cycle33_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle33_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle33_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data33 : PartitionData E W := ⟨6,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4,cycle33_5]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst34 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle34_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle34_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,5,6,8,18]⟩
def cycle34_2 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle34_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle34_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle34_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data34 : PartitionData E W := ⟨6,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4,cycle34_5]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,3,5,6,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst35 : E → W := ![4,3,5,6,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle35_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle35_1 : CycleData E W := ⟨2,![2,14,21,7],![3,5,28,18]⟩
def cycle35_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,8,6,5,14]⟩
def cycle35_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle35_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle35_5 : CycleData E W := ⟨4,![11,16,19,23,20,15],![4,26,6,38,8,28]⟩
def data35 : PartitionData E W := ⟨6,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4,cycle35_5]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def src36 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,26,38,8,18,28,38]
def dst36 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle36_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle36_1 : CycleData E W := ⟨3,![2,12,13,21,8],![3,5,14,28,18]⟩
def cycle36_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle36_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle36_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,16]⟩
def cycle36_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data36 : PartitionData E W := ⟨6,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4,cycle36_5]⟩
lemma valid_data36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel

def src37 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,26,38,8,18,38,28]
def dst37 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle37_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,18,16]⟩
def cycle37_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle37_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle37_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle37_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle37_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data37 : PartitionData E W := ⟨6,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4,cycle37_5]⟩
lemma valid_data37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel

def src38 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,26,38,8,28,18,38]
def dst38 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle38_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,18,16]⟩
def cycle38_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle38_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle38_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle38_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle38_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data38 : PartitionData E W := ⟨6,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4,cycle38_5]⟩
lemma valid_data38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel

def src39 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,38,26,8,18,28,38]
def dst39 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle39_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle39_1 : CycleData E W := ⟨3,![2,12,13,21,8],![3,5,14,28,18]⟩
def cycle39_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle39_3 : CycleData E W := ⟨2,![5,4,16,10],![2,8,6,16]⟩
def cycle39_4 : CycleData E W := ⟨2,![20,9,17,23],![8,18,16,38]⟩
def cycle39_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data39 : PartitionData E W := ⟨6,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4,cycle39_5]⟩
lemma valid_data39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel

def src40 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,38,26,8,18,38,28]
def dst40 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle40_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle40_1 : CycleData E W := ⟨4,![2,12,13,23,20,8],![3,5,14,28,8,18]⟩
def cycle40_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle40_3 : CycleData E W := ⟨2,![5,4,16,10],![2,8,6,16]⟩
def cycle40_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle40_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data40 : PartitionData E W := ⟨6,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4,cycle40_5]⟩
lemma valid_data40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel

def src41 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,16,38,26,8,28,18,38]
def dst41 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle41_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle41_1 : CycleData E W := ⟨3,![2,12,13,21,8],![3,5,14,28,18]⟩
def cycle41_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle41_3 : CycleData E W := ⟨2,![5,4,16,10],![2,8,6,16]⟩
def cycle41_4 : CycleData E W := ⟨1,![9,22,17],![16,18,38]⟩
def cycle41_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data41 : PartitionData E W := ⟨6,![cycle41_0,cycle41_1,cycle41_2,cycle41_3,cycle41_4,cycle41_5]⟩
lemma valid_data41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel

def src42 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,26,16,38,8,18,28,38]
def dst42 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle42_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle42_1 : CycleData E W := ⟨3,![2,12,13,21,8],![3,5,14,28,18]⟩
def cycle42_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle42_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle42_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,16]⟩
def cycle42_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data42 : PartitionData E W := ⟨6,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4,cycle42_5]⟩
lemma valid_data42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel

def src43 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,26,16,38,8,18,38,28]
def dst43 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle43_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,18,16]⟩
def cycle43_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle43_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle43_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle43_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle43_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data43 : PartitionData E W := ⟨6,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4,cycle43_5]⟩
lemma valid_data43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel

def src44 : E → W := ![2,4,3,5,6,8,2,14,3,18,16,4,5,14,28,26,6,26,16,38,8,28,18,38]
def dst44 : E → W := ![4,3,5,6,8,2,14,3,18,16,2,5,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle44_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle44_1 : CycleData E W := ⟨3,![2,12,13,21,8],![3,5,14,28,18]⟩
def cycle44_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle44_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle44_4 : CycleData E W := ⟨3,![5,20,14,17,10],![2,8,28,26,16]⟩
def cycle44_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data44 : PartitionData E W := ⟨6,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4,cycle44_5]⟩
lemma valid_data44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel

def src45 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,26,38,8,18,28,38]
def dst45 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle45_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle45_1 : CycleData E W := ⟨3,![2,12,13,21,9],![3,5,14,28,18]⟩
def cycle45_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle45_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle45_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle45_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data45 : PartitionData E W := ⟨6,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4,cycle45_5]⟩
lemma valid_data45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel

def src46 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,26,38,8,18,38,28]
def dst46 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle46_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle46_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle46_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle46_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle46_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle46_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data46 : PartitionData E W := ⟨6,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4,cycle46_5]⟩
lemma valid_data46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel

def src47 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,26,38,8,28,18,38]
def dst47 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle47_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle47_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle47_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle47_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle47_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle47_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data47 : PartitionData E W := ⟨6,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4,cycle47_5]⟩
lemma valid_data47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel

def src48 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,38,26,8,18,28,38]
def dst48 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle48_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle48_1 : CycleData E W := ⟨3,![2,12,13,21,9],![3,5,14,28,18]⟩
def cycle48_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle48_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle48_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle48_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data48 : PartitionData E W := ⟨6,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4,cycle48_5]⟩
lemma valid_data48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel

def src49 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,38,26,8,18,38,28]
def dst49 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle49_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle49_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle49_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle49_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle49_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle49_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data49 : PartitionData E W := ⟨6,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4,cycle49_5]⟩
lemma valid_data49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel

def src50 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,16,38,26,8,28,18,38]
def dst50 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle50_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle50_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle50_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle50_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle50_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle50_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data50 : PartitionData E W := ⟨6,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4,cycle50_5]⟩
lemma valid_data50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel

def src51 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,26,16,38,8,18,28,38]
def dst51 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle51_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle51_1 : CycleData E W := ⟨3,![2,12,13,21,9],![3,5,14,28,18]⟩
def cycle51_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle51_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle51_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle51_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data51 : PartitionData E W := ⟨6,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4,cycle51_5]⟩
lemma valid_data51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel

def src52 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,26,16,38,8,18,38,28]
def dst52 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle52_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle52_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle52_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle52_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle52_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle52_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data52 : PartitionData E W := ⟨6,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5]⟩
lemma valid_data52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel

def src53 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,5,14,28,26,6,26,16,38,8,28,18,38]
def dst53 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,5,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle53_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle53_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle53_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle53_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle53_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle53_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data53 : PartitionData E W := ⟨6,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4,cycle53_5]⟩
lemma valid_data53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel

def src54 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst54 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle54_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle54_1 : CycleData E W := ⟨3,![2,13,14,21,9],![3,5,14,28,18]⟩
def cycle54_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle54_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle54_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle54_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data54 : PartitionData E W := ⟨6,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4,cycle54_5]⟩
lemma valid_data54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel

def src55 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst55 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle55_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle55_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle55_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle55_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle55_4 : CycleData E W := ⟨2,![5,23,14,6],![2,8,28,14]⟩
def cycle55_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data55 : PartitionData E W := ⟨6,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4,cycle55_5]⟩
lemma valid_data55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel

def src56 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst56 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle56_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle56_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle56_2 : CycleData E W := ⟨2,![3,16,17,12],![5,6,16,26]⟩
def cycle56_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle56_4 : CycleData E W := ⟨2,![5,20,14,6],![2,8,28,14]⟩
def cycle56_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data56 : PartitionData E W := ⟨6,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4,cycle56_5]⟩
lemma valid_data56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel

def src57 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst57 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle57_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle57_1 : CycleData E W := ⟨3,![2,13,14,21,9],![3,5,14,28,18]⟩
def cycle57_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle57_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle57_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle57_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data57 : PartitionData E W := ⟨6,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4,cycle57_5]⟩
lemma valid_data57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel

def src58 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst58 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle58_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle58_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle58_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle58_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle58_4 : CycleData E W := ⟨2,![5,23,14,6],![2,8,28,14]⟩
def cycle58_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data58 : PartitionData E W := ⟨6,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4,cycle58_5]⟩
lemma valid_data58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel

def src59 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst59 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle59_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle59_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle59_2 : CycleData E W := ⟨1,![3,19,12],![5,6,26]⟩
def cycle59_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle59_4 : CycleData E W := ⟨2,![5,20,14,6],![2,8,28,14]⟩
def cycle59_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data59 : PartitionData E W := ⟨6,![cycle59_0,cycle59_1,cycle59_2,cycle59_3,cycle59_4,cycle59_5]⟩
lemma valid_data59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel

def src60 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst60 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle60_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,16,14]⟩
def cycle60_1 : CycleData E W := ⟨3,![2,13,14,21,9],![3,5,14,28,18]⟩
def cycle60_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle60_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle60_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle60_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data60 : PartitionData E W := ⟨6,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4,cycle60_5]⟩
lemma valid_data60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel

def src61 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst61 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle61_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle61_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle61_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle61_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle61_4 : CycleData E W := ⟨2,![5,23,14,6],![2,8,28,14]⟩
def cycle61_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data61 : PartitionData E W := ⟨6,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4,cycle61_5]⟩
lemma valid_data61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel

def src62 : E → W := ![2,4,3,5,6,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst62 : E → W := ![4,3,5,6,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle62_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle62_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,16]⟩
def cycle62_2 : CycleData E W := ⟨1,![3,16,12],![5,6,26]⟩
def cycle62_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle62_4 : CycleData E W := ⟨2,![5,20,14,6],![2,8,28,14]⟩
def cycle62_5 : CycleData E W := ⟨4,![11,17,18,22,21,15],![4,26,16,38,18,28]⟩
def data62 : PartitionData E W := ⟨6,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4,cycle62_5]⟩
lemma valid_data62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel

def src63 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,26,38,8,18,28,38]
def dst63 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle63_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle63_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle63_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle63_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle63_4 : CycleData E W := ⟨3,![5,20,21,13,6],![2,8,18,28,14]⟩
def cycle63_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data63 : PartitionData E W := ⟨6,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4,cycle63_5]⟩
lemma valid_data63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel

def src64 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,26,38,8,18,38,28]
def dst64 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle64_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle64_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle64_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle64_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle64_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle64_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data64 : PartitionData E W := ⟨6,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4,cycle64_5]⟩
lemma valid_data64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel

def src65 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,26,38,8,28,18,38]
def dst65 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle65_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle65_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle65_2 : CycleData E W := ⟨3,![11,3,16,17,15],![4,5,6,16,26]⟩
def cycle65_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle65_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle65_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data65 : PartitionData E W := ⟨6,![cycle65_0,cycle65_1,cycle65_2,cycle65_3,cycle65_4,cycle65_5]⟩
lemma valid_data65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel

def src66 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,38,26,8,18,28,38]
def dst66 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle66_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle66_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle66_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle66_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle66_4 : CycleData E W := ⟨3,![5,20,21,13,6],![2,8,18,28,14]⟩
def cycle66_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data66 : PartitionData E W := ⟨6,![cycle66_0,cycle66_1,cycle66_2,cycle66_3,cycle66_4,cycle66_5]⟩
lemma valid_data66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel

def src67 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,38,26,8,18,38,28]
def dst67 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle67_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle67_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle67_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle67_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle67_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle67_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data67 : PartitionData E W := ⟨6,![cycle67_0,cycle67_1,cycle67_2,cycle67_3,cycle67_4,cycle67_5]⟩
lemma valid_data67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel

def src68 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,16,38,26,8,28,18,38]
def dst68 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle68_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle68_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle68_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle68_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle68_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle68_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data68 : PartitionData E W := ⟨6,![cycle68_0,cycle68_1,cycle68_2,cycle68_3,cycle68_4,cycle68_5]⟩
lemma valid_data68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel

def src69 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,26,16,38,8,18,28,38]
def dst69 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle69_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle69_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle69_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle69_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle69_4 : CycleData E W := ⟨3,![5,20,21,13,6],![2,8,18,28,14]⟩
def cycle69_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data69 : PartitionData E W := ⟨6,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4,cycle69_5]⟩
lemma valid_data69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel

def src70 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,26,16,38,8,18,38,28]
def dst70 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle70_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle70_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle70_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle70_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle70_4 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle70_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data70 : PartitionData E W := ⟨6,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4,cycle70_5]⟩
lemma valid_data70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel

def src71 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,5,14,28,26,6,26,16,38,8,28,18,38]
def dst71 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,5,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle71_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle71_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle71_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle71_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle71_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle71_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data71 : PartitionData E W := ⟨6,![cycle71_0,cycle71_1,cycle71_2,cycle71_3,cycle71_4,cycle71_5]⟩
lemma valid_data71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel

def src72 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst72 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle72_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle72_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle72_2 : CycleData E W := ⟨3,![3,16,17,12,13],![5,6,16,26,14]⟩
def cycle72_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle72_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle72_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data72 : PartitionData E W := ⟨6,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4,cycle72_5]⟩
lemma valid_data72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel

def src73 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst73 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle73_0 : CycleData E W := ⟨10,![5,20,7,12,18,19,3,14,15,1,9,10],![2,8,18,14,26,38,6,5,28,4,3,16]⟩
def cycle73_1 : CycleData E W := ⟨10,![0,11,17,16,4,23,22,21,8,2,13,6],![2,4,26,16,6,8,28,38,18,3,5,14]⟩
def data73 : PartitionData E W := ⟨2,![cycle73_0,cycle73_1]⟩
lemma valid_data73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel

def src74 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst74 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle74_0 : CycleData E W := ⟨2,![0,11,17,10],![2,4,26,16]⟩
def cycle74_1 : CycleData E W := ⟨2,![1,15,21,8],![3,4,28,18]⟩
def cycle74_2 : CycleData E W := ⟨2,![2,3,16,9],![3,5,6,16]⟩
def cycle74_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle74_4 : CycleData E W := ⟨3,![5,20,14,13,6],![2,8,28,5,14]⟩
def cycle74_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data74 : PartitionData E W := ⟨6,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4,cycle74_5]⟩
lemma valid_data74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel

def src75 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst75 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle75_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle75_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle75_2 : CycleData E W := ⟨2,![3,19,12,13],![5,6,26,14]⟩
def cycle75_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle75_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle75_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data75 : PartitionData E W := ⟨6,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4,cycle75_5]⟩
lemma valid_data75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel

def src76 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst76 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle76_0 : CycleData E W := ⟨10,![0,15,14,3,4,20,8,9,17,18,12,6],![2,4,28,5,6,8,18,3,16,38,26,14]⟩
def cycle76_1 : CycleData E W := ⟨10,![5,23,22,21,7,13,2,1,11,19,16,10],![2,8,28,38,18,14,5,3,4,26,6,16]⟩
def data76 : PartitionData E W := ⟨2,![cycle76_0,cycle76_1]⟩
lemma valid_data76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel

def src77 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst77 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle77_0 : CycleData E W := ⟨10,![6,7,8,2,3,4,20,15,11,18,17,10],![2,14,18,3,5,6,8,28,4,26,38,16]⟩
def cycle77_1 : CycleData E W := ⟨10,![0,1,9,16,19,12,13,14,21,22,23,5],![2,4,3,16,6,26,14,5,28,18,38,8]⟩
def data77 : PartitionData E W := ⟨2,![cycle77_0,cycle77_1]⟩
lemma valid_data77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel

def src78 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst78 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle78_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle78_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle78_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle78_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle78_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle78_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data78 : PartitionData E W := ⟨6,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4,cycle78_5]⟩
lemma valid_data78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel

def src79 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst79 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle79_0 : CycleData E W := ⟨2,![0,11,17,10],![2,4,26,16]⟩
def cycle79_1 : CycleData E W := ⟨2,![1,15,14,2],![3,4,28,5]⟩
def cycle79_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle79_3 : CycleData E W := ⟨2,![4,23,22,19],![6,8,28,38]⟩
def cycle79_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle79_5 : CycleData E W := ⟨2,![8,21,18,9],![3,18,38,16]⟩
def data79 : PartitionData E W := ⟨6,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4,cycle79_5]⟩
lemma valid_data79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel

def src80 : E → W := ![2,4,3,5,6,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst80 : E → W := ![4,3,5,6,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle80_0 : CycleData E W := ⟨2,![0,11,17,10],![2,4,26,16]⟩
def cycle80_1 : CycleData E W := ⟨2,![1,15,14,2],![3,4,28,5]⟩
def cycle80_2 : CycleData E W := ⟨2,![3,16,12,13],![5,6,26,14]⟩
def cycle80_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle80_4 : CycleData E W := ⟨3,![5,20,21,7,6],![2,8,28,18,14]⟩
def cycle80_5 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def data80 : PartitionData E W := ⟨6,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4,cycle80_5]⟩
lemma valid_data80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel

def src81 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,26,38,8,18,28,38]
def dst81 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle81_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle81_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle81_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle81_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle81_4 : CycleData E W := ⟨3,![5,16,17,13,10],![2,6,16,26,14]⟩
def cycle81_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data81 : PartitionData E W := ⟨6,![cycle81_0,cycle81_1,cycle81_2,cycle81_3,cycle81_4,cycle81_5]⟩
lemma valid_data81 : data81.Valid src81 dst81 Finset.univ := by decide +kernel

def src82 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,26,38,8,18,38,28]
def dst82 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle82_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle82_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle82_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle82_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle82_4 : CycleData E W := ⟨3,![5,16,17,13,10],![2,6,16,26,14]⟩
def cycle82_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data82 : PartitionData E W := ⟨6,![cycle82_0,cycle82_1,cycle82_2,cycle82_3,cycle82_4,cycle82_5]⟩
lemma valid_data82 : data82.Valid src82 dst82 Finset.univ := by decide +kernel

def src83 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,26,38,8,28,18,38]
def dst83 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle83_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle83_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle83_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle83_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle83_4 : CycleData E W := ⟨3,![5,16,17,13,10],![2,6,16,26,14]⟩
def cycle83_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data83 : PartitionData E W := ⟨6,![cycle83_0,cycle83_1,cycle83_2,cycle83_3,cycle83_4,cycle83_5]⟩
lemma valid_data83 : data83.Valid src83 dst83 Finset.univ := by decide +kernel

def src84 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,38,26,8,18,28,38]
def dst84 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle84_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle84_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle84_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle84_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle84_4 : CycleData E W := ⟨2,![5,19,13,10],![2,6,26,14]⟩
def cycle84_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data84 : PartitionData E W := ⟨6,![cycle84_0,cycle84_1,cycle84_2,cycle84_3,cycle84_4,cycle84_5]⟩
lemma valid_data84 : data84.Valid src84 dst84 Finset.univ := by decide +kernel

def src85 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,38,26,8,18,38,28]
def dst85 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle85_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle85_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle85_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle85_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle85_4 : CycleData E W := ⟨2,![5,19,13,10],![2,6,26,14]⟩
def cycle85_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data85 : PartitionData E W := ⟨6,![cycle85_0,cycle85_1,cycle85_2,cycle85_3,cycle85_4,cycle85_5]⟩
lemma valid_data85 : data85.Valid src85 dst85 Finset.univ := by decide +kernel

def src86 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,16,38,26,8,28,18,38]
def dst86 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle86_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle86_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle86_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle86_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle86_4 : CycleData E W := ⟨2,![5,19,13,10],![2,6,26,14]⟩
def cycle86_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data86 : PartitionData E W := ⟨6,![cycle86_0,cycle86_1,cycle86_2,cycle86_3,cycle86_4,cycle86_5]⟩
lemma valid_data86 : data86.Valid src86 dst86 Finset.univ := by decide +kernel

def src87 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,26,16,38,8,18,28,38]
def dst87 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle87_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle87_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle87_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle87_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle87_4 : CycleData E W := ⟨2,![5,16,13,10],![2,6,26,14]⟩
def cycle87_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data87 : PartitionData E W := ⟨6,![cycle87_0,cycle87_1,cycle87_2,cycle87_3,cycle87_4,cycle87_5]⟩
lemma valid_data87 : data87.Valid src87 dst87 Finset.univ := by decide +kernel

def src88 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,26,16,38,8,18,38,28]
def dst88 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle88_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle88_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle88_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle88_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle88_4 : CycleData E W := ⟨2,![5,16,13,10],![2,6,26,14]⟩
def cycle88_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data88 : PartitionData E W := ⟨6,![cycle88_0,cycle88_1,cycle88_2,cycle88_3,cycle88_4,cycle88_5]⟩
lemma valid_data88 : data88.Valid src88 dst88 Finset.univ := by decide +kernel

def src89 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,5,14,26,28,6,26,16,38,8,28,18,38]
def dst89 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,5,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle89_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle89_1 : CycleData E W := ⟨3,![2,12,9,8,7],![3,5,14,18,16]⟩
def cycle89_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle89_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle89_4 : CycleData E W := ⟨2,![5,16,13,10],![2,6,26,14]⟩
def cycle89_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data89 : PartitionData E W := ⟨6,![cycle89_0,cycle89_1,cycle89_2,cycle89_3,cycle89_4,cycle89_5]⟩
lemma valid_data89 : data89.Valid src89 dst89 Finset.univ := by decide +kernel

def src90 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,18,28,38]
def dst90 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,18,28,38,8]
def cycle90_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle90_1 : CycleData E W := ⟨4,![5,16,7,2,12,10],![2,6,16,3,5,14]⟩
def cycle90_2 : CycleData E W := ⟨3,![3,20,8,17,13],![5,8,18,16,26]⟩
def cycle90_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle90_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle90_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data90 : PartitionData E W := ⟨6,![cycle90_0,cycle90_1,cycle90_2,cycle90_3,cycle90_4,cycle90_5]⟩
lemma valid_data90 : data90.Valid src90 dst90 Finset.univ := by decide +kernel

def src91 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,18,38,28]
def dst91 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,18,38,28,8]
def cycle91_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle91_1 : CycleData E W := ⟨2,![2,13,17,7],![3,5,26,16]⟩
def cycle91_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,6,8,5,14]⟩
def cycle91_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle91_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle91_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data91 : PartitionData E W := ⟨6,![cycle91_0,cycle91_1,cycle91_2,cycle91_3,cycle91_4,cycle91_5]⟩
lemma valid_data91 : data91.Valid src91 dst91 Finset.univ := by decide +kernel

def src92 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,28,18,38]
def dst92 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,28,18,38,8]
def cycle92_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle92_1 : CycleData E W := ⟨4,![5,16,7,2,12,10],![2,6,16,3,5,14]⟩
def cycle92_2 : CycleData E W := ⟨2,![3,20,14,13],![5,8,28,26]⟩
def cycle92_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle92_4 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def cycle92_5 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def data92 : PartitionData E W := ⟨6,![cycle92_0,cycle92_1,cycle92_2,cycle92_3,cycle92_4,cycle92_5]⟩
lemma valid_data92 : data92.Valid src92 dst92 Finset.univ := by decide +kernel

def src93 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,18,28,38]
def dst93 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,18,28,38,8]
def cycle93_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle93_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle93_2 : CycleData E W := ⟨3,![5,19,13,12,10],![2,6,26,5,14]⟩
def cycle93_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle93_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle93_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data93 : PartitionData E W := ⟨6,![cycle93_0,cycle93_1,cycle93_2,cycle93_3,cycle93_4,cycle93_5]⟩
lemma valid_data93 : data93.Valid src93 dst93 Finset.univ := by decide +kernel

def src94 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,18,38,28]
def dst94 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,18,38,28,8]
def cycle94_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle94_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle94_2 : CycleData E W := ⟨3,![5,19,13,12,10],![2,6,26,5,14]⟩
def cycle94_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle94_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle94_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data94 : PartitionData E W := ⟨6,![cycle94_0,cycle94_1,cycle94_2,cycle94_3,cycle94_4,cycle94_5]⟩
lemma valid_data94 : data94.Valid src94 dst94 Finset.univ := by decide +kernel

def src95 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,28,18,38]
def dst95 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,28,18,38,8]
def cycle95_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle95_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle95_2 : CycleData E W := ⟨3,![5,19,13,12,10],![2,6,26,5,14]⟩
def cycle95_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle95_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle95_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data95 : PartitionData E W := ⟨6,![cycle95_0,cycle95_1,cycle95_2,cycle95_3,cycle95_4,cycle95_5]⟩
lemma valid_data95 : data95.Valid src95 dst95 Finset.univ := by decide +kernel

def src96 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,18,28,38]
def dst96 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,18,28,38,8]
def cycle96_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle96_1 : CycleData E W := ⟨2,![2,13,17,7],![3,5,26,16]⟩
def cycle96_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,6,8,5,14]⟩
def cycle96_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle96_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle96_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data96 : PartitionData E W := ⟨6,![cycle96_0,cycle96_1,cycle96_2,cycle96_3,cycle96_4,cycle96_5]⟩
lemma valid_data96 : data96.Valid src96 dst96 Finset.univ := by decide +kernel

def src97 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,18,38,28]
def dst97 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,18,38,28,8]
def cycle97_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle97_1 : CycleData E W := ⟨2,![2,13,17,7],![3,5,26,16]⟩
def cycle97_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,6,8,5,14]⟩
def cycle97_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle97_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle97_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data97 : PartitionData E W := ⟨6,![cycle97_0,cycle97_1,cycle97_2,cycle97_3,cycle97_4,cycle97_5]⟩
lemma valid_data97 : data97.Valid src97 dst97 Finset.univ := by decide +kernel

def src98 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,28,18,38]
def dst98 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,28,18,38,8]
def cycle98_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle98_1 : CycleData E W := ⟨2,![2,13,17,7],![3,5,26,16]⟩
def cycle98_2 : CycleData E W := ⟨3,![5,4,3,12,10],![2,6,8,5,14]⟩
def cycle98_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle98_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle98_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data98 : PartitionData E W := ⟨6,![cycle98_0,cycle98_1,cycle98_2,cycle98_3,cycle98_4,cycle98_5]⟩
lemma valid_data98 : data98.Valid src98 dst98 Finset.univ := by decide +kernel

def src99 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst99 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle99_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle99_1 : CycleData E W := ⟨4,![5,16,7,2,13,10],![2,6,16,3,5,14]⟩
def cycle99_2 : CycleData E W := ⟨3,![3,20,8,17,12],![5,8,18,16,26]⟩
def cycle99_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle99_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle99_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data99 : PartitionData E W := ⟨6,![cycle99_0,cycle99_1,cycle99_2,cycle99_3,cycle99_4,cycle99_5]⟩
lemma valid_data99 : data99.Valid src99 dst99 Finset.univ := by decide +kernel

def src100 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst100 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle100_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle100_1 : CycleData E W := ⟨2,![2,12,17,7],![3,5,26,16]⟩
def cycle100_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,6,8,5,14]⟩
def cycle100_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle100_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle100_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data100 : PartitionData E W := ⟨6,![cycle100_0,cycle100_1,cycle100_2,cycle100_3,cycle100_4,cycle100_5]⟩
lemma valid_data100 : data100.Valid src100 dst100 Finset.univ := by decide +kernel

def src101 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst101 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle101_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle101_1 : CycleData E W := ⟨4,![5,16,7,2,13,10],![2,6,16,3,5,14]⟩
def cycle101_2 : CycleData E W := ⟨3,![11,12,3,20,15],![4,26,5,8,28]⟩
def cycle101_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle101_4 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def cycle101_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data101 : PartitionData E W := ⟨6,![cycle101_0,cycle101_1,cycle101_2,cycle101_3,cycle101_4,cycle101_5]⟩
lemma valid_data101 : data101.Valid src101 dst101 Finset.univ := by decide +kernel

def src102 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst102 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle102_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle102_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle102_2 : CycleData E W := ⟨3,![5,19,12,13,10],![2,6,26,5,14]⟩
def cycle102_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle102_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle102_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data102 : PartitionData E W := ⟨6,![cycle102_0,cycle102_1,cycle102_2,cycle102_3,cycle102_4,cycle102_5]⟩
lemma valid_data102 : data102.Valid src102 dst102 Finset.univ := by decide +kernel

def src103 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst103 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle103_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle103_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle103_2 : CycleData E W := ⟨3,![5,19,12,13,10],![2,6,26,5,14]⟩
def cycle103_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle103_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle103_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data103 : PartitionData E W := ⟨6,![cycle103_0,cycle103_1,cycle103_2,cycle103_3,cycle103_4,cycle103_5]⟩
lemma valid_data103 : data103.Valid src103 dst103 Finset.univ := by decide +kernel

def src104 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst104 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle104_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle104_1 : CycleData E W := ⟨3,![2,3,4,16,7],![3,5,8,6,16]⟩
def cycle104_2 : CycleData E W := ⟨3,![5,19,12,13,10],![2,6,26,5,14]⟩
def cycle104_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle104_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle104_5 : CycleData E W := ⟨3,![11,18,23,20,15],![4,26,38,8,28]⟩
def data104 : PartitionData E W := ⟨6,![cycle104_0,cycle104_1,cycle104_2,cycle104_3,cycle104_4,cycle104_5]⟩
lemma valid_data104 : data104.Valid src104 dst104 Finset.univ := by decide +kernel

def src105 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst105 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle105_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle105_1 : CycleData E W := ⟨2,![2,12,17,7],![3,5,26,16]⟩
def cycle105_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,6,8,5,14]⟩
def cycle105_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle105_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle105_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data105 : PartitionData E W := ⟨6,![cycle105_0,cycle105_1,cycle105_2,cycle105_3,cycle105_4,cycle105_5]⟩
lemma valid_data105 : data105.Valid src105 dst105 Finset.univ := by decide +kernel

def src106 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst106 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle106_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle106_1 : CycleData E W := ⟨2,![2,12,17,7],![3,5,26,16]⟩
def cycle106_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,6,8,5,14]⟩
def cycle106_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle106_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle106_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data106 : PartitionData E W := ⟨6,![cycle106_0,cycle106_1,cycle106_2,cycle106_3,cycle106_4,cycle106_5]⟩
lemma valid_data106 : data106.Valid src106 dst106 Finset.univ := by decide +kernel

def src107 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst107 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle107_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle107_1 : CycleData E W := ⟨2,![2,12,17,7],![3,5,26,16]⟩
def cycle107_2 : CycleData E W := ⟨3,![5,4,3,13,10],![2,6,8,5,14]⟩
def cycle107_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle107_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle107_5 : CycleData E W := ⟨4,![11,16,19,23,20,15],![4,26,6,38,8,28]⟩
def data107 : PartitionData E W := ⟨6,![cycle107_0,cycle107_1,cycle107_2,cycle107_3,cycle107_4,cycle107_5]⟩
lemma valid_data107 : data107.Valid src107 dst107 Finset.univ := by decide +kernel

def src108 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst108 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle108_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle108_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle108_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle108_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle108_4 : CycleData E W := ⟨3,![5,16,17,12,10],![2,6,16,26,14]⟩
def cycle108_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data108 : PartitionData E W := ⟨6,![cycle108_0,cycle108_1,cycle108_2,cycle108_3,cycle108_4,cycle108_5]⟩
lemma valid_data108 : data108.Valid src108 dst108 Finset.univ := by decide +kernel

def src109 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst109 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle109_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle109_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle109_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle109_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle109_4 : CycleData E W := ⟨3,![5,16,17,12,10],![2,6,16,26,14]⟩
def cycle109_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data109 : PartitionData E W := ⟨6,![cycle109_0,cycle109_1,cycle109_2,cycle109_3,cycle109_4,cycle109_5]⟩
lemma valid_data109 : data109.Valid src109 dst109 Finset.univ := by decide +kernel

def src110 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst110 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle110_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle110_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle110_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle110_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle110_4 : CycleData E W := ⟨3,![5,16,17,12,10],![2,6,16,26,14]⟩
def cycle110_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data110 : PartitionData E W := ⟨6,![cycle110_0,cycle110_1,cycle110_2,cycle110_3,cycle110_4,cycle110_5]⟩
lemma valid_data110 : data110.Valid src110 dst110 Finset.univ := by decide +kernel

def src111 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst111 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle111_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle111_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle111_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle111_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle111_4 : CycleData E W := ⟨2,![5,19,12,10],![2,6,26,14]⟩
def cycle111_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data111 : PartitionData E W := ⟨6,![cycle111_0,cycle111_1,cycle111_2,cycle111_3,cycle111_4,cycle111_5]⟩
lemma valid_data111 : data111.Valid src111 dst111 Finset.univ := by decide +kernel

def src112 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst112 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle112_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle112_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle112_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle112_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle112_4 : CycleData E W := ⟨2,![5,19,12,10],![2,6,26,14]⟩
def cycle112_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data112 : PartitionData E W := ⟨6,![cycle112_0,cycle112_1,cycle112_2,cycle112_3,cycle112_4,cycle112_5]⟩
lemma valid_data112 : data112.Valid src112 dst112 Finset.univ := by decide +kernel

def src113 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst113 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle113_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle113_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle113_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle113_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle113_4 : CycleData E W := ⟨2,![5,19,12,10],![2,6,26,14]⟩
def cycle113_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data113 : PartitionData E W := ⟨6,![cycle113_0,cycle113_1,cycle113_2,cycle113_3,cycle113_4,cycle113_5]⟩
lemma valid_data113 : data113.Valid src113 dst113 Finset.univ := by decide +kernel

def src114 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst114 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle114_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle114_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle114_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle114_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle114_4 : CycleData E W := ⟨2,![5,16,12,10],![2,6,26,14]⟩
def cycle114_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data114 : PartitionData E W := ⟨6,![cycle114_0,cycle114_1,cycle114_2,cycle114_3,cycle114_4,cycle114_5]⟩
lemma valid_data114 : data114.Valid src114 dst114 Finset.univ := by decide +kernel

def src115 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst115 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle115_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle115_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle115_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle115_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle115_4 : CycleData E W := ⟨2,![5,16,12,10],![2,6,26,14]⟩
def cycle115_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data115 : PartitionData E W := ⟨6,![cycle115_0,cycle115_1,cycle115_2,cycle115_3,cycle115_4,cycle115_5]⟩
lemma valid_data115 : data115.Valid src115 dst115 Finset.univ := by decide +kernel

def src116 : E → W := ![2,4,3,5,8,6,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst116 : E → W := ![4,3,5,8,6,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle116_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle116_1 : CycleData E W := ⟨3,![2,13,9,8,7],![3,5,14,18,16]⟩
def cycle116_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle116_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle116_4 : CycleData E W := ⟨2,![5,16,12,10],![2,6,26,14]⟩
def cycle116_5 : CycleData E W := ⟨4,![11,17,18,22,21,15],![4,26,16,38,18,28]⟩
def data116 : PartitionData E W := ⟨6,![cycle116_0,cycle116_1,cycle116_2,cycle116_3,cycle116_4,cycle116_5]⟩
lemma valid_data116 : data116.Valid src116 dst116 Finset.univ := by decide +kernel

def src117 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,26,38,8,18,28,38]
def dst117 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle117_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle117_1 : CycleData E W := ⟨3,![2,12,13,17,8],![3,5,14,26,16]⟩
def cycle117_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle117_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle117_4 : CycleData E W := ⟨2,![5,16,9,10],![2,6,16,18]⟩
def cycle117_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data117 : PartitionData E W := ⟨6,![cycle117_0,cycle117_1,cycle117_2,cycle117_3,cycle117_4,cycle117_5]⟩
lemma valid_data117 : data117.Valid src117 dst117 Finset.univ := by decide +kernel

def src118 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,26,38,8,18,38,28]
def dst118 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle118_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle118_1 : CycleData E W := ⟨3,![2,12,13,17,8],![3,5,14,26,16]⟩
def cycle118_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle118_3 : CycleData E W := ⟨2,![5,4,20,10],![2,6,8,18]⟩
def cycle118_4 : CycleData E W := ⟨2,![16,9,21,19],![6,16,18,38]⟩
def cycle118_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data118 : PartitionData E W := ⟨6,![cycle118_0,cycle118_1,cycle118_2,cycle118_3,cycle118_4,cycle118_5]⟩
lemma valid_data118 : data118.Valid src118 dst118 Finset.univ := by decide +kernel

def src119 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,26,38,8,28,18,38]
def dst119 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle119_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle119_1 : CycleData E W := ⟨3,![2,12,13,17,8],![3,5,14,26,16]⟩
def cycle119_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle119_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle119_4 : CycleData E W := ⟨2,![5,16,9,10],![2,6,16,18]⟩
def cycle119_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data119 : PartitionData E W := ⟨6,![cycle119_0,cycle119_1,cycle119_2,cycle119_3,cycle119_4,cycle119_5]⟩
lemma valid_data119 : data119.Valid src119 dst119 Finset.univ := by decide +kernel

def src120 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,38,26,8,18,28,38]
def dst120 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle120_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,16,18]⟩
def cycle120_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle120_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle120_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle120_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle120_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data120 : PartitionData E W := ⟨6,![cycle120_0,cycle120_1,cycle120_2,cycle120_3,cycle120_4,cycle120_5]⟩
lemma valid_data120 : data120.Valid src120 dst120 Finset.univ := by decide +kernel

def src121 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,38,26,8,18,38,28]
def dst121 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle121_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle121_1 : CycleData E W := ⟨4,![2,12,13,19,16,8],![3,5,14,26,6,16]⟩
def cycle121_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle121_3 : CycleData E W := ⟨2,![5,4,20,10],![2,6,8,18]⟩
def cycle121_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle121_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data121 : PartitionData E W := ⟨6,![cycle121_0,cycle121_1,cycle121_2,cycle121_3,cycle121_4,cycle121_5]⟩
lemma valid_data121 : data121.Valid src121 dst121 Finset.univ := by decide +kernel

def src122 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,16,38,26,8,28,18,38]
def dst122 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle122_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,16,18]⟩
def cycle122_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle122_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle122_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle122_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle122_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data122 : PartitionData E W := ⟨6,![cycle122_0,cycle122_1,cycle122_2,cycle122_3,cycle122_4,cycle122_5]⟩
lemma valid_data122 : data122.Valid src122 dst122 Finset.univ := by decide +kernel

def src123 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,26,16,38,8,18,28,38]
def dst123 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle123_0 : CycleData E W := ⟨3,![0,1,8,9,10],![2,4,3,16,18]⟩
def cycle123_1 : CycleData E W := ⟨1,![2,12,7],![3,5,14]⟩
def cycle123_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle123_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle123_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle123_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data123 : PartitionData E W := ⟨6,![cycle123_0,cycle123_1,cycle123_2,cycle123_3,cycle123_4,cycle123_5]⟩
lemma valid_data123 : data123.Valid src123 dst123 Finset.univ := by decide +kernel

def src124 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,26,16,38,8,18,38,28]
def dst124 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle124_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle124_1 : CycleData E W := ⟨3,![2,12,13,17,8],![3,5,14,26,16]⟩
def cycle124_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle124_3 : CycleData E W := ⟨2,![5,4,20,10],![2,6,8,18]⟩
def cycle124_4 : CycleData E W := ⟨1,![9,21,18],![16,18,38]⟩
def cycle124_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data124 : PartitionData E W := ⟨6,![cycle124_0,cycle124_1,cycle124_2,cycle124_3,cycle124_4,cycle124_5]⟩
lemma valid_data124 : data124.Valid src124 dst124 Finset.univ := by decide +kernel

def src125 : E → W := ![2,4,3,5,8,6,2,14,3,16,18,4,5,14,26,28,6,26,16,38,8,28,18,38]
def dst125 : E → W := ![4,3,5,8,6,2,14,3,16,18,2,5,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle125_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,14]⟩
def cycle125_1 : CycleData E W := ⟨3,![2,12,13,17,8],![3,5,14,26,16]⟩
def cycle125_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle125_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle125_4 : CycleData E W := ⟨3,![5,16,14,21,10],![2,6,26,28,18]⟩
def cycle125_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data125 : PartitionData E W := ⟨6,![cycle125_0,cycle125_1,cycle125_2,cycle125_3,cycle125_4,cycle125_5]⟩
lemma valid_data125 : data125.Valid src125 dst125 Finset.univ := by decide +kernel

def src126 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,26,38,8,18,28,38]
def dst126 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle126_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle126_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle126_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle126_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle126_4 : CycleData E W := ⟨3,![5,16,17,13,6],![2,6,16,26,14]⟩
def cycle126_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data126 : PartitionData E W := ⟨6,![cycle126_0,cycle126_1,cycle126_2,cycle126_3,cycle126_4,cycle126_5]⟩
lemma valid_data126 : data126.Valid src126 dst126 Finset.univ := by decide +kernel

def src127 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,26,38,8,18,38,28]
def dst127 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle127_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle127_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle127_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle127_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle127_4 : CycleData E W := ⟨3,![5,16,17,13,6],![2,6,16,26,14]⟩
def cycle127_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data127 : PartitionData E W := ⟨6,![cycle127_0,cycle127_1,cycle127_2,cycle127_3,cycle127_4,cycle127_5]⟩
lemma valid_data127 : data127.Valid src127 dst127 Finset.univ := by decide +kernel

def src128 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,26,38,8,28,18,38]
def dst128 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle128_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle128_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle128_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle128_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle128_4 : CycleData E W := ⟨3,![5,16,17,13,6],![2,6,16,26,14]⟩
def cycle128_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data128 : PartitionData E W := ⟨6,![cycle128_0,cycle128_1,cycle128_2,cycle128_3,cycle128_4,cycle128_5]⟩
lemma valid_data128 : data128.Valid src128 dst128 Finset.univ := by decide +kernel

def src129 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,38,26,8,18,28,38]
def dst129 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle129_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle129_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle129_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle129_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle129_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle129_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data129 : PartitionData E W := ⟨6,![cycle129_0,cycle129_1,cycle129_2,cycle129_3,cycle129_4,cycle129_5]⟩
lemma valid_data129 : data129.Valid src129 dst129 Finset.univ := by decide +kernel

def src130 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,38,26,8,18,38,28]
def dst130 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle130_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle130_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle130_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle130_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle130_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle130_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data130 : PartitionData E W := ⟨6,![cycle130_0,cycle130_1,cycle130_2,cycle130_3,cycle130_4,cycle130_5]⟩
lemma valid_data130 : data130.Valid src130 dst130 Finset.univ := by decide +kernel

def src131 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,16,38,26,8,28,18,38]
def dst131 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle131_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle131_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle131_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle131_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle131_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle131_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data131 : PartitionData E W := ⟨6,![cycle131_0,cycle131_1,cycle131_2,cycle131_3,cycle131_4,cycle131_5]⟩
lemma valid_data131 : data131.Valid src131 dst131 Finset.univ := by decide +kernel

def src132 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,26,16,38,8,18,28,38]
def dst132 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle132_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle132_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle132_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle132_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle132_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle132_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data132 : PartitionData E W := ⟨6,![cycle132_0,cycle132_1,cycle132_2,cycle132_3,cycle132_4,cycle132_5]⟩
lemma valid_data132 : data132.Valid src132 dst132 Finset.univ := by decide +kernel

def src133 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,26,16,38,8,18,38,28]
def dst133 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle133_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle133_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle133_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle133_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle133_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle133_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data133 : PartitionData E W := ⟨6,![cycle133_0,cycle133_1,cycle133_2,cycle133_3,cycle133_4,cycle133_5]⟩
lemma valid_data133 : data133.Valid src133 dst133 Finset.univ := by decide +kernel

def src134 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,5,14,26,28,6,26,16,38,8,28,18,38]
def dst134 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,5,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle134_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle134_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,16]⟩
def cycle134_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle134_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle134_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle134_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data134 : PartitionData E W := ⟨6,![cycle134_0,cycle134_1,cycle134_2,cycle134_3,cycle134_4,cycle134_5]⟩
lemma valid_data134 : data134.Valid src134 dst134 Finset.univ := by decide +kernel

def src135 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst135 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle135_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle135_1 : CycleData E W := ⟨2,![2,12,17,8],![3,5,26,16]⟩
def cycle135_2 : CycleData E W := ⟨3,![3,20,21,14,13],![5,8,18,28,14]⟩
def cycle135_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle135_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle135_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data135 : PartitionData E W := ⟨6,![cycle135_0,cycle135_1,cycle135_2,cycle135_3,cycle135_4,cycle135_5]⟩
lemma valid_data135 : data135.Valid src135 dst135 Finset.univ := by decide +kernel

def src136 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst136 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle136_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle136_1 : CycleData E W := ⟨2,![2,12,17,8],![3,5,26,16]⟩
def cycle136_2 : CycleData E W := ⟨2,![3,23,14,13],![5,8,28,14]⟩
def cycle136_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle136_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle136_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data136 : PartitionData E W := ⟨6,![cycle136_0,cycle136_1,cycle136_2,cycle136_3,cycle136_4,cycle136_5]⟩
lemma valid_data136 : data136.Valid src136 dst136 Finset.univ := by decide +kernel

def src137 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst137 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle137_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,18]⟩
def cycle137_1 : CycleData E W := ⟨2,![2,12,17,8],![3,5,26,16]⟩
def cycle137_2 : CycleData E W := ⟨2,![3,20,14,13],![5,8,28,14]⟩
def cycle137_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle137_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle137_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data137 : PartitionData E W := ⟨6,![cycle137_0,cycle137_1,cycle137_2,cycle137_3,cycle137_4,cycle137_5]⟩
lemma valid_data137 : data137.Valid src137 dst137 Finset.univ := by decide +kernel

def src138 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst138 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle138_0 : CycleData E W := ⟨10,![0,15,14,13,12,18,17,8,9,20,4,5],![2,4,28,14,5,26,38,16,3,18,8,6]⟩
def cycle138_1 : CycleData E W := ⟨10,![6,7,16,19,11,1,2,3,23,22,21,10],![2,14,16,6,26,4,3,5,8,38,28,18]⟩
def data138 : PartitionData E W := ⟨2,![cycle138_0,cycle138_1]⟩
lemma valid_data138 : data138.Valid src138 dst138 Finset.univ := by decide +kernel

def src139 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst139 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle139_0 : CycleData E W := ⟨10,![0,15,14,13,12,18,17,8,9,20,4,5],![2,4,28,14,5,26,38,16,3,18,8,6]⟩
def cycle139_1 : CycleData E W := ⟨10,![6,7,16,19,11,1,2,3,23,22,21,10],![2,14,16,6,26,4,3,5,8,28,38,18]⟩
def data139 : PartitionData E W := ⟨2,![cycle139_0,cycle139_1]⟩
lemma valid_data139 : data139.Valid src139 dst139 Finset.univ := by decide +kernel

def src140 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst140 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle140_0 : CycleData E W := ⟨2,![0,15,21,10],![2,4,28,18]⟩
def cycle140_1 : CycleData E W := ⟨2,![1,11,12,2],![3,4,26,5]⟩
def cycle140_2 : CycleData E W := ⟨2,![3,20,14,13],![5,8,28,14]⟩
def cycle140_3 : CycleData E W := ⟨2,![4,23,18,19],![6,8,38,26]⟩
def cycle140_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle140_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data140 : PartitionData E W := ⟨6,![cycle140_0,cycle140_1,cycle140_2,cycle140_3,cycle140_4,cycle140_5]⟩
lemma valid_data140 : data140.Valid src140 dst140 Finset.univ := by decide +kernel

def src141 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst141 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle141_0 : CycleData E W := ⟨2,![0,11,16,5],![2,4,26,6]⟩
def cycle141_1 : CycleData E W := ⟨2,![1,15,21,9],![3,4,28,18]⟩
def cycle141_2 : CycleData E W := ⟨2,![2,12,17,8],![3,5,26,16]⟩
def cycle141_3 : CycleData E W := ⟨3,![6,13,3,20,10],![2,14,5,8,18]⟩
def cycle141_4 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle141_5 : CycleData E W := ⟨2,![7,18,22,14],![14,16,38,28]⟩
def data141 : PartitionData E W := ⟨6,![cycle141_0,cycle141_1,cycle141_2,cycle141_3,cycle141_4,cycle141_5]⟩
lemma valid_data141 : data141.Valid src141 dst141 Finset.univ := by decide +kernel

def src142 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst142 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle142_0 : CycleData E W := ⟨10,![5,19,18,8,9,20,3,12,11,15,14,6],![2,6,38,16,3,18,8,5,26,4,28,14]⟩
def cycle142_1 : CycleData E W := ⟨10,![0,1,2,13,7,17,16,4,23,22,21,10],![2,4,3,5,14,16,26,6,8,28,38,18]⟩
def data142 : PartitionData E W := ⟨2,![cycle142_0,cycle142_1]⟩
lemma valid_data142 : data142.Valid src142 dst142 Finset.univ := by decide +kernel

def src143 : E → W := ![2,4,3,5,8,6,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst143 : E → W := ![4,3,5,8,6,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle143_0 : CycleData E W := ⟨2,![0,11,16,5],![2,4,26,6]⟩
def cycle143_1 : CycleData E W := ⟨3,![1,15,20,3,2],![3,4,28,8,5]⟩
def cycle143_2 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle143_3 : CycleData E W := ⟨2,![6,14,21,10],![2,14,28,18]⟩
def cycle143_4 : CycleData E W := ⟨2,![12,17,7,13],![5,26,16,14]⟩
def cycle143_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def data143 : PartitionData E W := ⟨6,![cycle143_0,cycle143_1,cycle143_2,cycle143_3,cycle143_4,cycle143_5]⟩
lemma valid_data143 : data143.Valid src143 dst143 Finset.univ := by decide +kernel

def src144 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,26,38,8,18,28,38]
def dst144 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle144_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle144_1 : CycleData E W := ⟨3,![2,12,13,17,9],![3,5,14,26,16]⟩
def cycle144_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle144_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle144_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle144_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data144 : PartitionData E W := ⟨6,![cycle144_0,cycle144_1,cycle144_2,cycle144_3,cycle144_4,cycle144_5]⟩
lemma valid_data144 : data144.Valid src144 dst144 Finset.univ := by decide +kernel

def src145 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,26,38,8,18,38,28]
def dst145 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle145_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle145_1 : CycleData E W := ⟨3,![2,12,13,17,9],![3,5,14,26,16]⟩
def cycle145_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle145_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle145_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle145_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data145 : PartitionData E W := ⟨6,![cycle145_0,cycle145_1,cycle145_2,cycle145_3,cycle145_4,cycle145_5]⟩
lemma valid_data145 : data145.Valid src145 dst145 Finset.univ := by decide +kernel

def src146 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,26,38,8,28,18,38]
def dst146 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle146_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle146_1 : CycleData E W := ⟨3,![2,12,13,17,9],![3,5,14,26,16]⟩
def cycle146_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle146_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle146_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle146_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data146 : PartitionData E W := ⟨6,![cycle146_0,cycle146_1,cycle146_2,cycle146_3,cycle146_4,cycle146_5]⟩
lemma valid_data146 : data146.Valid src146 dst146 Finset.univ := by decide +kernel

def src147 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,38,26,8,18,28,38]
def dst147 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle147_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle147_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle147_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle147_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle147_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle147_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data147 : PartitionData E W := ⟨6,![cycle147_0,cycle147_1,cycle147_2,cycle147_3,cycle147_4,cycle147_5]⟩
lemma valid_data147 : data147.Valid src147 dst147 Finset.univ := by decide +kernel

def src148 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,38,26,8,18,38,28]
def dst148 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle148_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle148_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle148_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle148_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle148_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle148_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data148 : PartitionData E W := ⟨6,![cycle148_0,cycle148_1,cycle148_2,cycle148_3,cycle148_4,cycle148_5]⟩
lemma valid_data148 : data148.Valid src148 dst148 Finset.univ := by decide +kernel

def src149 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,16,38,26,8,28,18,38]
def dst149 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle149_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle149_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle149_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle149_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle149_4 : CycleData E W := ⟨2,![5,19,13,6],![2,6,26,14]⟩
def cycle149_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data149 : PartitionData E W := ⟨6,![cycle149_0,cycle149_1,cycle149_2,cycle149_3,cycle149_4,cycle149_5]⟩
lemma valid_data149 : data149.Valid src149 dst149 Finset.univ := by decide +kernel

def src150 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,26,16,38,8,18,28,38]
def dst150 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle150_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle150_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle150_2 : CycleData E W := ⟨3,![11,3,20,21,15],![4,5,8,18,28]⟩
def cycle150_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle150_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle150_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data150 : PartitionData E W := ⟨6,![cycle150_0,cycle150_1,cycle150_2,cycle150_3,cycle150_4,cycle150_5]⟩
lemma valid_data150 : data150.Valid src150 dst150 Finset.univ := by decide +kernel

def src151 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,26,16,38,8,18,38,28]
def dst151 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle151_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle151_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle151_2 : CycleData E W := ⟨2,![11,3,23,15],![4,5,8,28]⟩
def cycle151_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle151_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle151_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data151 : PartitionData E W := ⟨6,![cycle151_0,cycle151_1,cycle151_2,cycle151_3,cycle151_4,cycle151_5]⟩
lemma valid_data151 : data151.Valid src151 dst151 Finset.univ := by decide +kernel

def src152 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,5,14,26,28,6,26,16,38,8,28,18,38]
def dst152 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,5,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle152_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle152_1 : CycleData E W := ⟨2,![2,12,7,8],![3,5,14,18]⟩
def cycle152_2 : CycleData E W := ⟨2,![11,3,20,15],![4,5,8,28]⟩
def cycle152_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle152_4 : CycleData E W := ⟨2,![5,16,13,6],![2,6,26,14]⟩
def cycle152_5 : CycleData E W := ⟨3,![17,14,21,22,18],![16,26,28,18,38]⟩
def data152 : PartitionData E W := ⟨6,![cycle152_0,cycle152_1,cycle152_2,cycle152_3,cycle152_4,cycle152_5]⟩
lemma valid_data152 : data152.Valid src152 dst152 Finset.univ := by decide +kernel

def src153 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst153 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle153_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle153_1 : CycleData E W := ⟨3,![2,13,12,17,9],![3,5,14,26,16]⟩
def cycle153_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle153_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle153_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle153_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data153 : PartitionData E W := ⟨6,![cycle153_0,cycle153_1,cycle153_2,cycle153_3,cycle153_4,cycle153_5]⟩
lemma valid_data153 : data153.Valid src153 dst153 Finset.univ := by decide +kernel

def src154 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst154 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle154_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle154_1 : CycleData E W := ⟨3,![2,13,12,17,9],![3,5,14,26,16]⟩
def cycle154_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle154_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle154_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle154_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data154 : PartitionData E W := ⟨6,![cycle154_0,cycle154_1,cycle154_2,cycle154_3,cycle154_4,cycle154_5]⟩
lemma valid_data154 : data154.Valid src154 dst154 Finset.univ := by decide +kernel

def src155 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst155 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle155_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,14]⟩
def cycle155_1 : CycleData E W := ⟨3,![2,13,12,17,9],![3,5,14,26,16]⟩
def cycle155_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle155_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle155_4 : CycleData E W := ⟨1,![5,16,10],![2,6,16]⟩
def cycle155_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data155 : PartitionData E W := ⟨6,![cycle155_0,cycle155_1,cycle155_2,cycle155_3,cycle155_4,cycle155_5]⟩
lemma valid_data155 : data155.Valid src155 dst155 Finset.univ := by decide +kernel

def src156 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst156 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle156_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle156_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle156_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle156_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle156_4 : CycleData E W := ⟨2,![5,19,12,6],![2,6,26,14]⟩
def cycle156_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data156 : PartitionData E W := ⟨6,![cycle156_0,cycle156_1,cycle156_2,cycle156_3,cycle156_4,cycle156_5]⟩
lemma valid_data156 : data156.Valid src156 dst156 Finset.univ := by decide +kernel

def src157 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst157 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle157_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle157_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle157_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle157_3 : CycleData E W := ⟨3,![4,20,21,17,16],![6,8,18,38,16]⟩
def cycle157_4 : CycleData E W := ⟨2,![5,19,12,6],![2,6,26,14]⟩
def cycle157_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data157 : PartitionData E W := ⟨6,![cycle157_0,cycle157_1,cycle157_2,cycle157_3,cycle157_4,cycle157_5]⟩
lemma valid_data157 : data157.Valid src157 dst157 Finset.univ := by decide +kernel

def src158 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst158 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle158_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle158_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle158_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle158_3 : CycleData E W := ⟨2,![4,23,17,16],![6,8,38,16]⟩
def cycle158_4 : CycleData E W := ⟨2,![5,19,12,6],![2,6,26,14]⟩
def cycle158_5 : CycleData E W := ⟨3,![11,18,22,21,15],![4,26,38,18,28]⟩
def data158 : PartitionData E W := ⟨6,![cycle158_0,cycle158_1,cycle158_2,cycle158_3,cycle158_4,cycle158_5]⟩
lemma valid_data158 : data158.Valid src158 dst158 Finset.univ := by decide +kernel

def src159 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst159 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle159_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle159_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle159_2 : CycleData E W := ⟨2,![3,20,21,14],![5,8,18,28]⟩
def cycle159_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle159_4 : CycleData E W := ⟨2,![5,16,12,6],![2,6,26,14]⟩
def cycle159_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data159 : PartitionData E W := ⟨6,![cycle159_0,cycle159_1,cycle159_2,cycle159_3,cycle159_4,cycle159_5]⟩
lemma valid_data159 : data159.Valid src159 dst159 Finset.univ := by decide +kernel

def src160 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst160 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle160_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle160_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle160_2 : CycleData E W := ⟨1,![3,23,14],![5,8,28]⟩
def cycle160_3 : CycleData E W := ⟨2,![4,20,21,19],![6,8,18,38]⟩
def cycle160_4 : CycleData E W := ⟨2,![5,16,12,6],![2,6,26,14]⟩
def cycle160_5 : CycleData E W := ⟨3,![11,17,18,22,15],![4,26,16,38,28]⟩
def data160 : PartitionData E W := ⟨6,![cycle160_0,cycle160_1,cycle160_2,cycle160_3,cycle160_4,cycle160_5]⟩
lemma valid_data160 : data160.Valid src160 dst160 Finset.univ := by decide +kernel

def src161 : E → W := ![2,4,3,5,8,6,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst161 : E → W := ![4,3,5,8,6,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle161_0 : CycleData E W := ⟨2,![0,1,9,10],![2,4,3,16]⟩
def cycle161_1 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle161_2 : CycleData E W := ⟨1,![3,20,14],![5,8,28]⟩
def cycle161_3 : CycleData E W := ⟨1,![4,23,19],![6,8,38]⟩
def cycle161_4 : CycleData E W := ⟨2,![5,16,12,6],![2,6,26,14]⟩
def cycle161_5 : CycleData E W := ⟨4,![11,17,18,22,21,15],![4,26,16,38,18,28]⟩
def data161 : PartitionData E W := ⟨6,![cycle161_0,cycle161_1,cycle161_2,cycle161_3,cycle161_4,cycle161_5]⟩
lemma valid_data161 : data161.Valid src161 dst161 Finset.univ := by decide +kernel

def src162 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,26,38,8,18,28,38]
def dst162 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle162_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle162_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle162_2 : CycleData E W := ⟨3,![11,4,20,21,15],![4,5,8,18,28]⟩
def cycle162_3 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle162_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle162_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data162 : PartitionData E W := ⟨6,![cycle162_0,cycle162_1,cycle162_2,cycle162_3,cycle162_4,cycle162_5]⟩
lemma valid_data162 : data162.Valid src162 dst162 Finset.univ := by decide +kernel

def src163 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,26,38,8,18,38,28]
def dst163 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle163_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle163_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle163_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle163_3 : CycleData E W := ⟨4,![5,20,21,19,16,10],![2,8,18,38,6,16]⟩
def cycle163_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle163_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data163 : PartitionData E W := ⟨6,![cycle163_0,cycle163_1,cycle163_2,cycle163_3,cycle163_4,cycle163_5]⟩
lemma valid_data163 : data163.Valid src163 dst163 Finset.univ := by decide +kernel

def src164 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,26,38,8,28,18,38]
def dst164 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle164_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle164_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle164_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle164_3 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle164_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle164_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data164 : PartitionData E W := ⟨6,![cycle164_0,cycle164_1,cycle164_2,cycle164_3,cycle164_4,cycle164_5]⟩
lemma valid_data164 : data164.Valid src164 dst164 Finset.univ := by decide +kernel

def src165 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,38,26,8,18,28,38]
def dst165 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle165_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle165_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle165_2 : CycleData E W := ⟨3,![11,4,20,21,15],![4,5,8,18,28]⟩
def cycle165_3 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle165_4 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def cycle165_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data165 : PartitionData E W := ⟨6,![cycle165_0,cycle165_1,cycle165_2,cycle165_3,cycle165_4,cycle165_5]⟩
lemma valid_data165 : data165.Valid src165 dst165 Finset.univ := by decide +kernel

def src166 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,38,26,8,18,38,28]
def dst166 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle166_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle166_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle166_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle166_3 : CycleData E W := ⟨3,![5,20,21,17,10],![2,8,18,38,16]⟩
def cycle166_4 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def cycle166_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data166 : PartitionData E W := ⟨6,![cycle166_0,cycle166_1,cycle166_2,cycle166_3,cycle166_4,cycle166_5]⟩
lemma valid_data166 : data166.Valid src166 dst166 Finset.univ := by decide +kernel

def src167 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,16,38,26,8,28,18,38]
def dst167 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle167_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle167_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle167_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle167_3 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle167_4 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def cycle167_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data167 : PartitionData E W := ⟨6,![cycle167_0,cycle167_1,cycle167_2,cycle167_3,cycle167_4,cycle167_5]⟩
lemma valid_data167 : data167.Valid src167 dst167 Finset.univ := by decide +kernel

def src168 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,26,16,38,8,18,28,38]
def dst168 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle168_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle168_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle168_2 : CycleData E W := ⟨3,![11,4,20,21,15],![4,5,8,18,28]⟩
def cycle168_3 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle168_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle168_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data168 : PartitionData E W := ⟨6,![cycle168_0,cycle168_1,cycle168_2,cycle168_3,cycle168_4,cycle168_5]⟩
lemma valid_data168 : data168.Valid src168 dst168 Finset.univ := by decide +kernel

def src169 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,26,16,38,8,18,38,28]
def dst169 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle169_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle169_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle169_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle169_3 : CycleData E W := ⟨3,![5,20,21,18,10],![2,8,18,38,16]⟩
def cycle169_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle169_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data169 : PartitionData E W := ⟨6,![cycle169_0,cycle169_1,cycle169_2,cycle169_3,cycle169_4,cycle169_5]⟩
lemma valid_data169 : data169.Valid src169 dst169 Finset.univ := by decide +kernel

def src170 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,26,28,6,26,16,38,8,28,18,38]
def dst170 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle170_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle170_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle170_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle170_3 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle170_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle170_5 : CycleData E W := ⟨3,![16,14,21,22,19],![6,26,28,18,38]⟩
def data170 : PartitionData E W := ⟨6,![cycle170_0,cycle170_1,cycle170_2,cycle170_3,cycle170_4,cycle170_5]⟩
lemma valid_data170 : data170.Valid src170 dst170 Finset.univ := by decide +kernel

def src171 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,26,38,8,18,28,38]
def dst171 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle171_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle171_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,6,5,8,18]⟩
def cycle171_2 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle171_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle171_4 : CycleData E W := ⟨3,![11,12,9,17,15],![4,5,14,16,26]⟩
def cycle171_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data171 : PartitionData E W := ⟨6,![cycle171_0,cycle171_1,cycle171_2,cycle171_3,cycle171_4,cycle171_5]⟩
lemma valid_data171 : data171.Valid src171 dst171 Finset.univ := by decide +kernel

def src172 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,26,38,8,18,38,28]
def dst172 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle172_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle172_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle172_2 : CycleData E W := ⟨3,![5,4,3,16,10],![2,8,5,6,16]⟩
def cycle172_3 : CycleData E W := ⟨2,![20,8,13,23],![8,18,14,28]⟩
def cycle172_4 : CycleData E W := ⟨3,![11,12,9,17,15],![4,5,14,16,26]⟩
def cycle172_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data172 : PartitionData E W := ⟨6,![cycle172_0,cycle172_1,cycle172_2,cycle172_3,cycle172_4,cycle172_5]⟩
lemma valid_data172 : data172.Valid src172 dst172 Finset.univ := by decide +kernel

def src173 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,26,38,8,28,18,38]
def dst173 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle173_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle173_1 : CycleData E W := ⟨2,![2,19,22,7],![3,6,38,18]⟩
def cycle173_2 : CycleData E W := ⟨3,![5,4,3,16,10],![2,8,5,6,16]⟩
def cycle173_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle173_4 : CycleData E W := ⟨3,![11,12,9,17,15],![4,5,14,16,26]⟩
def cycle173_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data173 : PartitionData E W := ⟨6,![cycle173_0,cycle173_1,cycle173_2,cycle173_3,cycle173_4,cycle173_5]⟩
lemma valid_data173 : data173.Valid src173 dst173 Finset.univ := by decide +kernel

def src174 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,38,26,8,18,28,38]
def dst174 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle174_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle174_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle174_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle174_3 : CycleData E W := ⟨3,![4,20,21,13,12],![5,8,18,28,14]⟩
def cycle174_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle174_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data174 : PartitionData E W := ⟨6,![cycle174_0,cycle174_1,cycle174_2,cycle174_3,cycle174_4,cycle174_5]⟩
lemma valid_data174 : data174.Valid src174 dst174 Finset.univ := by decide +kernel

def src175 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,38,26,8,18,38,28]
def dst175 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle175_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle175_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle175_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle175_3 : CycleData E W := ⟨2,![4,23,13,12],![5,8,28,14]⟩
def cycle175_4 : CycleData E W := ⟨3,![5,20,21,17,10],![2,8,18,38,16]⟩
def cycle175_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data175 : PartitionData E W := ⟨6,![cycle175_0,cycle175_1,cycle175_2,cycle175_3,cycle175_4,cycle175_5]⟩
lemma valid_data175 : data175.Valid src175 dst175 Finset.univ := by decide +kernel

def src176 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,16,38,26,8,28,18,38]
def dst176 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle176_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle176_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle176_2 : CycleData E W := ⟨2,![11,3,19,15],![4,5,6,26]⟩
def cycle176_3 : CycleData E W := ⟨2,![4,20,13,12],![5,8,28,14]⟩
def cycle176_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle176_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data176 : PartitionData E W := ⟨6,![cycle176_0,cycle176_1,cycle176_2,cycle176_3,cycle176_4,cycle176_5]⟩
lemma valid_data176 : data176.Valid src176 dst176 Finset.univ := by decide +kernel

def src177 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,26,16,38,8,18,28,38]
def dst177 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle177_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle177_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,6,5,8,18]⟩
def cycle177_2 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle177_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle177_4 : CycleData E W := ⟨3,![11,12,9,17,15],![4,5,14,16,26]⟩
def cycle177_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data177 : PartitionData E W := ⟨6,![cycle177_0,cycle177_1,cycle177_2,cycle177_3,cycle177_4,cycle177_5]⟩
lemma valid_data177 : data177.Valid src177 dst177 Finset.univ := by decide +kernel

def src178 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,26,16,38,8,18,38,28]
def dst178 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle178_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle178_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle178_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle178_3 : CycleData E W := ⟨3,![5,4,12,9,10],![2,8,5,14,16]⟩
def cycle178_4 : CycleData E W := ⟨2,![20,8,13,23],![8,18,14,28]⟩
def cycle178_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data178 : PartitionData E W := ⟨6,![cycle178_0,cycle178_1,cycle178_2,cycle178_3,cycle178_4,cycle178_5]⟩
lemma valid_data178 : data178.Valid src178 dst178 Finset.univ := by decide +kernel

def src179 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,5,14,28,26,6,26,16,38,8,28,18,38]
def dst179 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,5,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle179_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle179_1 : CycleData E W := ⟨2,![2,19,22,7],![3,6,38,18]⟩
def cycle179_2 : CycleData E W := ⟨2,![11,3,16,15],![4,5,6,26]⟩
def cycle179_3 : CycleData E W := ⟨3,![5,4,12,9,10],![2,8,5,14,16]⟩
def cycle179_4 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle179_5 : CycleData E W := ⟨3,![20,14,17,18,23],![8,28,26,16,38]⟩
def data179 : PartitionData E W := ⟨6,![cycle179_0,cycle179_1,cycle179_2,cycle179_3,cycle179_4,cycle179_5]⟩
lemma valid_data179 : data179.Valid src179 dst179 Finset.univ := by decide +kernel

def src180 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,26,38,8,18,28,38]
def dst180 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,26,38,6,18,28,38,8]
def cycle180_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle180_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,6,5,8,18]⟩
def cycle180_2 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle180_3 : CycleData E W := ⟨2,![11,8,21,15],![4,14,18,28]⟩
def cycle180_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle180_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data180 : PartitionData E W := ⟨6,![cycle180_0,cycle180_1,cycle180_2,cycle180_3,cycle180_4,cycle180_5]⟩
lemma valid_data180 : data180.Valid src180 dst180 Finset.univ := by decide +kernel

def src181 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,26,38,8,18,38,28]
def dst181 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,26,38,6,18,38,28,8]
def cycle181_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle181_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle181_2 : CycleData E W := ⟨3,![5,4,3,16,10],![2,8,5,6,16]⟩
def cycle181_3 : CycleData E W := ⟨3,![11,8,20,23,15],![4,14,18,8,28]⟩
def cycle181_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle181_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data181 : PartitionData E W := ⟨6,![cycle181_0,cycle181_1,cycle181_2,cycle181_3,cycle181_4,cycle181_5]⟩
lemma valid_data181 : data181.Valid src181 dst181 Finset.univ := by decide +kernel

def src182 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,26,38,8,28,18,38]
def dst182 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,26,38,6,28,18,38,8]
def cycle182_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle182_1 : CycleData E W := ⟨2,![2,19,22,7],![3,6,38,18]⟩
def cycle182_2 : CycleData E W := ⟨3,![5,4,3,16,10],![2,8,5,6,16]⟩
def cycle182_3 : CycleData E W := ⟨2,![11,8,21,15],![4,14,18,28]⟩
def cycle182_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle182_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data182 : PartitionData E W := ⟨6,![cycle182_0,cycle182_1,cycle182_2,cycle182_3,cycle182_4,cycle182_5]⟩
lemma valid_data182 : data182.Valid src182 dst182 Finset.univ := by decide +kernel

def src183 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,38,26,8,18,28,38]
def dst183 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,38,26,6,18,28,38,8]
def cycle183_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle183_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle183_2 : CycleData E W := ⟨1,![3,19,13],![5,6,26]⟩
def cycle183_3 : CycleData E W := ⟨4,![11,12,4,20,21,15],![4,14,5,8,18,28]⟩
def cycle183_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle183_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data183 : PartitionData E W := ⟨6,![cycle183_0,cycle183_1,cycle183_2,cycle183_3,cycle183_4,cycle183_5]⟩
lemma valid_data183 : data183.Valid src183 dst183 Finset.univ := by decide +kernel

def src184 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,38,26,8,18,38,28]
def dst184 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,38,26,6,18,38,28,8]
def cycle184_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle184_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle184_2 : CycleData E W := ⟨1,![3,19,13],![5,6,26]⟩
def cycle184_3 : CycleData E W := ⟨3,![11,12,4,23,15],![4,14,5,8,28]⟩
def cycle184_4 : CycleData E W := ⟨3,![5,20,21,17,10],![2,8,18,38,16]⟩
def cycle184_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data184 : PartitionData E W := ⟨6,![cycle184_0,cycle184_1,cycle184_2,cycle184_3,cycle184_4,cycle184_5]⟩
lemma valid_data184 : data184.Valid src184 dst184 Finset.univ := by decide +kernel

def src185 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,16,38,26,8,28,18,38]
def dst185 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,16,38,26,6,28,18,38,8]
def cycle185_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle185_1 : CycleData E W := ⟨3,![2,16,9,8,7],![3,6,16,14,18]⟩
def cycle185_2 : CycleData E W := ⟨1,![3,19,13],![5,6,26]⟩
def cycle185_3 : CycleData E W := ⟨3,![11,12,4,20,15],![4,14,5,8,28]⟩
def cycle185_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle185_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data185 : PartitionData E W := ⟨6,![cycle185_0,cycle185_1,cycle185_2,cycle185_3,cycle185_4,cycle185_5]⟩
lemma valid_data185 : data185.Valid src185 dst185 Finset.univ := by decide +kernel

def src186 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,26,16,38,8,18,28,38]
def dst186 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,26,16,38,6,18,28,38,8]
def cycle186_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle186_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,6,5,8,18]⟩
def cycle186_2 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle186_3 : CycleData E W := ⟨2,![11,8,21,15],![4,14,18,28]⟩
def cycle186_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle186_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data186 : PartitionData E W := ⟨6,![cycle186_0,cycle186_1,cycle186_2,cycle186_3,cycle186_4,cycle186_5]⟩
lemma valid_data186 : data186.Valid src186 dst186 Finset.univ := by decide +kernel

def src187 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,26,16,38,8,18,38,28]
def dst187 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,26,16,38,6,18,38,28,8]
def cycle187_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle187_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle187_2 : CycleData E W := ⟨1,![3,16,13],![5,6,26]⟩
def cycle187_3 : CycleData E W := ⟨3,![5,4,12,9,10],![2,8,5,14,16]⟩
def cycle187_4 : CycleData E W := ⟨3,![11,8,20,23,15],![4,14,18,8,28]⟩
def cycle187_5 : CycleData E W := ⟨2,![17,14,22,18],![16,26,28,38]⟩
def data187 : PartitionData E W := ⟨6,![cycle187_0,cycle187_1,cycle187_2,cycle187_3,cycle187_4,cycle187_5]⟩
lemma valid_data187 : data187.Valid src187 dst187 Finset.univ := by decide +kernel

def src188 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,26,28,6,26,16,38,8,28,18,38]
def dst188 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,26,28,4,26,16,38,6,28,18,38,8]
def cycle188_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle188_1 : CycleData E W := ⟨2,![2,19,22,7],![3,6,38,18]⟩
def cycle188_2 : CycleData E W := ⟨1,![3,16,13],![5,6,26]⟩
def cycle188_3 : CycleData E W := ⟨3,![5,4,12,9,10],![2,8,5,14,16]⟩
def cycle188_4 : CycleData E W := ⟨2,![11,8,21,15],![4,14,18,28]⟩
def cycle188_5 : CycleData E W := ⟨3,![20,14,17,18,23],![8,28,26,16,38]⟩
def data188 : PartitionData E W := ⟨6,![cycle188_0,cycle188_1,cycle188_2,cycle188_3,cycle188_4,cycle188_5]⟩
lemma valid_data188 : data188.Valid src188 dst188 Finset.univ := by decide +kernel

def src189 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,26,38,8,18,28,38]
def dst189 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,26,38,6,18,28,38,8]
def cycle189_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle189_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle189_2 : CycleData E W := ⟨2,![4,20,21,13],![5,8,18,28]⟩
def cycle189_3 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle189_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle189_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data189 : PartitionData E W := ⟨6,![cycle189_0,cycle189_1,cycle189_2,cycle189_3,cycle189_4,cycle189_5]⟩
lemma valid_data189 : data189.Valid src189 dst189 Finset.univ := by decide +kernel

def src190 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,26,38,8,18,38,28]
def dst190 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,26,38,6,18,38,28,8]
def cycle190_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle190_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle190_2 : CycleData E W := ⟨1,![4,23,13],![5,8,28]⟩
def cycle190_3 : CycleData E W := ⟨4,![5,20,21,19,16,10],![2,8,18,38,6,16]⟩
def cycle190_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle190_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data190 : PartitionData E W := ⟨6,![cycle190_0,cycle190_1,cycle190_2,cycle190_3,cycle190_4,cycle190_5]⟩
lemma valid_data190 : data190.Valid src190 dst190 Finset.univ := by decide +kernel

def src191 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,26,38,8,28,18,38]
def dst191 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,26,38,6,28,18,38,8]
def cycle191_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle191_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle191_2 : CycleData E W := ⟨1,![4,20,13],![5,8,28]⟩
def cycle191_3 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle191_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle191_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data191 : PartitionData E W := ⟨6,![cycle191_0,cycle191_1,cycle191_2,cycle191_3,cycle191_4,cycle191_5]⟩
lemma valid_data191 : data191.Valid src191 dst191 Finset.univ := by decide +kernel

def src192 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,38,26,8,18,28,38]
def dst192 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,38,26,6,18,28,38,8]
def cycle192_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle192_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle192_2 : CycleData E W := ⟨2,![4,20,21,13],![5,8,18,28]⟩
def cycle192_3 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle192_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle192_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data192 : PartitionData E W := ⟨6,![cycle192_0,cycle192_1,cycle192_2,cycle192_3,cycle192_4,cycle192_5]⟩
lemma valid_data192 : data192.Valid src192 dst192 Finset.univ := by decide +kernel

def src193 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,38,26,8,18,38,28]
def dst193 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,38,26,6,18,38,28,8]
def cycle193_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle193_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle193_2 : CycleData E W := ⟨1,![4,23,13],![5,8,28]⟩
def cycle193_3 : CycleData E W := ⟨3,![5,20,21,17,10],![2,8,18,38,16]⟩
def cycle193_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle193_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data193 : PartitionData E W := ⟨6,![cycle193_0,cycle193_1,cycle193_2,cycle193_3,cycle193_4,cycle193_5]⟩
lemma valid_data193 : data193.Valid src193 dst193 Finset.univ := by decide +kernel

def src194 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,16,38,26,8,28,18,38]
def dst194 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,16,38,26,6,28,18,38,8]
def cycle194_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle194_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle194_2 : CycleData E W := ⟨1,![4,20,13],![5,8,28]⟩
def cycle194_3 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle194_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle194_5 : CycleData E W := ⟨2,![21,14,18,22],![18,28,26,38]⟩
def data194 : PartitionData E W := ⟨6,![cycle194_0,cycle194_1,cycle194_2,cycle194_3,cycle194_4,cycle194_5]⟩
lemma valid_data194 : data194.Valid src194 dst194 Finset.univ := by decide +kernel

def src195 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,26,16,38,8,18,28,38]
def dst195 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,26,16,38,6,18,28,38,8]
def cycle195_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle195_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle195_2 : CycleData E W := ⟨2,![4,20,21,13],![5,8,18,28]⟩
def cycle195_3 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle195_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle195_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data195 : PartitionData E W := ⟨6,![cycle195_0,cycle195_1,cycle195_2,cycle195_3,cycle195_4,cycle195_5]⟩
lemma valid_data195 : data195.Valid src195 dst195 Finset.univ := by decide +kernel

def src196 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,26,16,38,8,18,38,28]
def dst196 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,26,16,38,6,18,38,28,8]
def cycle196_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle196_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle196_2 : CycleData E W := ⟨1,![4,23,13],![5,8,28]⟩
def cycle196_3 : CycleData E W := ⟨3,![5,20,21,18,10],![2,8,18,38,16]⟩
def cycle196_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle196_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data196 : PartitionData E W := ⟨6,![cycle196_0,cycle196_1,cycle196_2,cycle196_3,cycle196_4,cycle196_5]⟩
lemma valid_data196 : data196.Valid src196 dst196 Finset.univ := by decide +kernel

def src197 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,14,5,28,26,6,26,16,38,8,28,18,38]
def dst197 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,14,5,28,26,4,26,16,38,6,28,18,38,8]
def cycle197_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle197_1 : CycleData E W := ⟨3,![2,3,12,8,7],![3,6,5,14,18]⟩
def cycle197_2 : CycleData E W := ⟨1,![4,20,13],![5,8,28]⟩
def cycle197_3 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle197_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle197_5 : CycleData E W := ⟨3,![16,14,21,22,19],![6,26,28,18,38]⟩
def data197 : PartitionData E W := ⟨6,![cycle197_0,cycle197_1,cycle197_2,cycle197_3,cycle197_4,cycle197_5]⟩
lemma valid_data197 : data197.Valid src197 dst197 Finset.univ := by decide +kernel

def src198 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst198 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle198_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle198_1 : CycleData E W := ⟨3,![2,3,4,20,7],![3,6,5,8,18]⟩
def cycle198_2 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle198_3 : CycleData E W := ⟨1,![8,21,14],![14,18,28]⟩
def cycle198_4 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def cycle198_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data198 : PartitionData E W := ⟨6,![cycle198_0,cycle198_1,cycle198_2,cycle198_3,cycle198_4,cycle198_5]⟩
lemma valid_data198 : data198.Valid src198 dst198 Finset.univ := by decide +kernel

def src199 : E → W := ![2,4,3,6,5,8,2,3,18,14,16,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst199 : E → W := ![4,3,6,5,8,2,3,18,14,16,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle199_0 : CycleData E W := ⟨1,![0,1,6],![2,4,3]⟩
def cycle199_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle199_2 : CycleData E W := ⟨3,![5,4,3,16,10],![2,8,5,6,16]⟩
def cycle199_3 : CycleData E W := ⟨2,![20,8,14,23],![8,18,14,28]⟩
def cycle199_4 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def cycle199_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data199 : PartitionData E W := ⟨6,![cycle199_0,cycle199_1,cycle199_2,cycle199_3,cycle199_4,cycle199_5]⟩
lemma valid_data199 : data199.Valid src199 dst199 Finset.univ := by decide +kernel

def lookupB0 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data0 else (if j < 2 then data1 else data2)) else (if j < 4 then data3 else (if j < 5 then data4 else data5))) else (if j < 9 then (if j < 7 then data6 else (if j < 8 then data7 else data8)) else (if j < 10 then data9 else (if j < 11 then data10 else data11)))) else (if j < 18 then (if j < 15 then (if j < 13 then data12 else (if j < 14 then data13 else data14)) else (if j < 16 then data15 else (if j < 17 then data16 else data17))) else (if j < 21 then (if j < 19 then data18 else (if j < 20 then data19 else data20)) else (if j < 23 then (if j < 22 then data21 else data22) else (if j < 24 then data23 else data24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data25 else (if j < 27 then data26 else data27)) else (if j < 29 then data28 else (if j < 30 then data29 else data30))) else (if j < 34 then (if j < 32 then data31 else (if j < 33 then data32 else data33)) else (if j < 35 then data34 else (if j < 36 then data35 else data36)))) else (if j < 43 then (if j < 40 then (if j < 38 then data37 else (if j < 39 then data38 else data39)) else (if j < 41 then data40 else (if j < 42 then data41 else data42))) else (if j < 46 then (if j < 44 then data43 else (if j < 45 then data44 else data45)) else (if j < 48 then (if j < 47 then data46 else data47) else (if j < 49 then data48 else data49)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data50 else (if j < 52 then data51 else data52)) else (if j < 54 then data53 else (if j < 55 then data54 else data55))) else (if j < 59 then (if j < 57 then data56 else (if j < 58 then data57 else data58)) else (if j < 60 then data59 else (if j < 61 then data60 else data61)))) else (if j < 68 then (if j < 65 then (if j < 63 then data62 else (if j < 64 then data63 else data64)) else (if j < 66 then data65 else (if j < 67 then data66 else data67))) else (if j < 71 then (if j < 69 then data68 else (if j < 70 then data69 else data70)) else (if j < 73 then (if j < 72 then data71 else data72) else (if j < 74 then data73 else data74))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data75 else (if j < 77 then data76 else data77)) else (if j < 79 then data78 else (if j < 80 then data79 else data80))) else (if j < 84 then (if j < 82 then data81 else (if j < 83 then data82 else data83)) else (if j < 85 then data84 else (if j < 86 then data85 else data86)))) else (if j < 93 then (if j < 90 then (if j < 88 then data87 else (if j < 89 then data88 else data89)) else (if j < 91 then data90 else (if j < 92 then data91 else data92))) else (if j < 96 then (if j < 94 then data93 else (if j < 95 then data94 else data95)) else (if j < 98 then (if j < 97 then data96 else data97) else (if j < 99 then data98 else data99))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data100 else (if j < 102 then data101 else data102)) else (if j < 104 then data103 else (if j < 105 then data104 else data105))) else (if j < 109 then (if j < 107 then data106 else (if j < 108 then data107 else data108)) else (if j < 110 then data109 else (if j < 111 then data110 else data111)))) else (if j < 118 then (if j < 115 then (if j < 113 then data112 else (if j < 114 then data113 else data114)) else (if j < 116 then data115 else (if j < 117 then data116 else data117))) else (if j < 121 then (if j < 119 then data118 else (if j < 120 then data119 else data120)) else (if j < 123 then (if j < 122 then data121 else data122) else (if j < 124 then data123 else data124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data125 else (if j < 127 then data126 else data127)) else (if j < 129 then data128 else (if j < 130 then data129 else data130))) else (if j < 134 then (if j < 132 then data131 else (if j < 133 then data132 else data133)) else (if j < 135 then data134 else (if j < 136 then data135 else data136)))) else (if j < 143 then (if j < 140 then (if j < 138 then data137 else (if j < 139 then data138 else data139)) else (if j < 141 then data140 else (if j < 142 then data141 else data142))) else (if j < 146 then (if j < 144 then data143 else (if j < 145 then data144 else data145)) else (if j < 148 then (if j < 147 then data146 else data147) else (if j < 149 then data148 else data149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data150 else (if j < 152 then data151 else data152)) else (if j < 154 then data153 else (if j < 155 then data154 else data155))) else (if j < 159 then (if j < 157 then data156 else (if j < 158 then data157 else data158)) else (if j < 160 then data159 else (if j < 161 then data160 else data161)))) else (if j < 168 then (if j < 165 then (if j < 163 then data162 else (if j < 164 then data163 else data164)) else (if j < 166 then data165 else (if j < 167 then data166 else data167))) else (if j < 171 then (if j < 169 then data168 else (if j < 170 then data169 else data170)) else (if j < 173 then (if j < 172 then data171 else data172) else (if j < 174 then data173 else data174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data175 else (if j < 177 then data176 else data177)) else (if j < 179 then data178 else (if j < 180 then data179 else data180))) else (if j < 184 then (if j < 182 then data181 else (if j < 183 then data182 else data183)) else (if j < 185 then data184 else (if j < 186 then data185 else data186)))) else (if j < 193 then (if j < 190 then (if j < 188 then data187 else (if j < 189 then data188 else data189)) else (if j < 191 then data190 else (if j < 192 then data191 else data192))) else (if j < 196 then (if j < 194 then data193 else (if j < 195 then data194 else data195)) else (if j < 198 then (if j < 197 then data196 else data197) else (if j < 199 then data198 else data199))))))))

def srcTableB0 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src0 else (if j < 2 then src1 else src2)) else (if j < 4 then src3 else (if j < 5 then src4 else src5))) else (if j < 9 then (if j < 7 then src6 else (if j < 8 then src7 else src8)) else (if j < 10 then src9 else (if j < 11 then src10 else src11)))) else (if j < 18 then (if j < 15 then (if j < 13 then src12 else (if j < 14 then src13 else src14)) else (if j < 16 then src15 else (if j < 17 then src16 else src17))) else (if j < 21 then (if j < 19 then src18 else (if j < 20 then src19 else src20)) else (if j < 23 then (if j < 22 then src21 else src22) else (if j < 24 then src23 else src24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src25 else (if j < 27 then src26 else src27)) else (if j < 29 then src28 else (if j < 30 then src29 else src30))) else (if j < 34 then (if j < 32 then src31 else (if j < 33 then src32 else src33)) else (if j < 35 then src34 else (if j < 36 then src35 else src36)))) else (if j < 43 then (if j < 40 then (if j < 38 then src37 else (if j < 39 then src38 else src39)) else (if j < 41 then src40 else (if j < 42 then src41 else src42))) else (if j < 46 then (if j < 44 then src43 else (if j < 45 then src44 else src45)) else (if j < 48 then (if j < 47 then src46 else src47) else (if j < 49 then src48 else src49)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src50 else (if j < 52 then src51 else src52)) else (if j < 54 then src53 else (if j < 55 then src54 else src55))) else (if j < 59 then (if j < 57 then src56 else (if j < 58 then src57 else src58)) else (if j < 60 then src59 else (if j < 61 then src60 else src61)))) else (if j < 68 then (if j < 65 then (if j < 63 then src62 else (if j < 64 then src63 else src64)) else (if j < 66 then src65 else (if j < 67 then src66 else src67))) else (if j < 71 then (if j < 69 then src68 else (if j < 70 then src69 else src70)) else (if j < 73 then (if j < 72 then src71 else src72) else (if j < 74 then src73 else src74))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src75 else (if j < 77 then src76 else src77)) else (if j < 79 then src78 else (if j < 80 then src79 else src80))) else (if j < 84 then (if j < 82 then src81 else (if j < 83 then src82 else src83)) else (if j < 85 then src84 else (if j < 86 then src85 else src86)))) else (if j < 93 then (if j < 90 then (if j < 88 then src87 else (if j < 89 then src88 else src89)) else (if j < 91 then src90 else (if j < 92 then src91 else src92))) else (if j < 96 then (if j < 94 then src93 else (if j < 95 then src94 else src95)) else (if j < 98 then (if j < 97 then src96 else src97) else (if j < 99 then src98 else src99))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src100 else (if j < 102 then src101 else src102)) else (if j < 104 then src103 else (if j < 105 then src104 else src105))) else (if j < 109 then (if j < 107 then src106 else (if j < 108 then src107 else src108)) else (if j < 110 then src109 else (if j < 111 then src110 else src111)))) else (if j < 118 then (if j < 115 then (if j < 113 then src112 else (if j < 114 then src113 else src114)) else (if j < 116 then src115 else (if j < 117 then src116 else src117))) else (if j < 121 then (if j < 119 then src118 else (if j < 120 then src119 else src120)) else (if j < 123 then (if j < 122 then src121 else src122) else (if j < 124 then src123 else src124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src125 else (if j < 127 then src126 else src127)) else (if j < 129 then src128 else (if j < 130 then src129 else src130))) else (if j < 134 then (if j < 132 then src131 else (if j < 133 then src132 else src133)) else (if j < 135 then src134 else (if j < 136 then src135 else src136)))) else (if j < 143 then (if j < 140 then (if j < 138 then src137 else (if j < 139 then src138 else src139)) else (if j < 141 then src140 else (if j < 142 then src141 else src142))) else (if j < 146 then (if j < 144 then src143 else (if j < 145 then src144 else src145)) else (if j < 148 then (if j < 147 then src146 else src147) else (if j < 149 then src148 else src149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src150 else (if j < 152 then src151 else src152)) else (if j < 154 then src153 else (if j < 155 then src154 else src155))) else (if j < 159 then (if j < 157 then src156 else (if j < 158 then src157 else src158)) else (if j < 160 then src159 else (if j < 161 then src160 else src161)))) else (if j < 168 then (if j < 165 then (if j < 163 then src162 else (if j < 164 then src163 else src164)) else (if j < 166 then src165 else (if j < 167 then src166 else src167))) else (if j < 171 then (if j < 169 then src168 else (if j < 170 then src169 else src170)) else (if j < 173 then (if j < 172 then src171 else src172) else (if j < 174 then src173 else src174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src175 else (if j < 177 then src176 else src177)) else (if j < 179 then src178 else (if j < 180 then src179 else src180))) else (if j < 184 then (if j < 182 then src181 else (if j < 183 then src182 else src183)) else (if j < 185 then src184 else (if j < 186 then src185 else src186)))) else (if j < 193 then (if j < 190 then (if j < 188 then src187 else (if j < 189 then src188 else src189)) else (if j < 191 then src190 else (if j < 192 then src191 else src192))) else (if j < 196 then (if j < 194 then src193 else (if j < 195 then src194 else src195)) else (if j < 198 then (if j < 197 then src196 else src197) else (if j < 199 then src198 else src199))))))))

def dstTableB0 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst0 else (if j < 2 then dst1 else dst2)) else (if j < 4 then dst3 else (if j < 5 then dst4 else dst5))) else (if j < 9 then (if j < 7 then dst6 else (if j < 8 then dst7 else dst8)) else (if j < 10 then dst9 else (if j < 11 then dst10 else dst11)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst12 else (if j < 14 then dst13 else dst14)) else (if j < 16 then dst15 else (if j < 17 then dst16 else dst17))) else (if j < 21 then (if j < 19 then dst18 else (if j < 20 then dst19 else dst20)) else (if j < 23 then (if j < 22 then dst21 else dst22) else (if j < 24 then dst23 else dst24))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst25 else (if j < 27 then dst26 else dst27)) else (if j < 29 then dst28 else (if j < 30 then dst29 else dst30))) else (if j < 34 then (if j < 32 then dst31 else (if j < 33 then dst32 else dst33)) else (if j < 35 then dst34 else (if j < 36 then dst35 else dst36)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst37 else (if j < 39 then dst38 else dst39)) else (if j < 41 then dst40 else (if j < 42 then dst41 else dst42))) else (if j < 46 then (if j < 44 then dst43 else (if j < 45 then dst44 else dst45)) else (if j < 48 then (if j < 47 then dst46 else dst47) else (if j < 49 then dst48 else dst49)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst50 else (if j < 52 then dst51 else dst52)) else (if j < 54 then dst53 else (if j < 55 then dst54 else dst55))) else (if j < 59 then (if j < 57 then dst56 else (if j < 58 then dst57 else dst58)) else (if j < 60 then dst59 else (if j < 61 then dst60 else dst61)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst62 else (if j < 64 then dst63 else dst64)) else (if j < 66 then dst65 else (if j < 67 then dst66 else dst67))) else (if j < 71 then (if j < 69 then dst68 else (if j < 70 then dst69 else dst70)) else (if j < 73 then (if j < 72 then dst71 else dst72) else (if j < 74 then dst73 else dst74))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst75 else (if j < 77 then dst76 else dst77)) else (if j < 79 then dst78 else (if j < 80 then dst79 else dst80))) else (if j < 84 then (if j < 82 then dst81 else (if j < 83 then dst82 else dst83)) else (if j < 85 then dst84 else (if j < 86 then dst85 else dst86)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst87 else (if j < 89 then dst88 else dst89)) else (if j < 91 then dst90 else (if j < 92 then dst91 else dst92))) else (if j < 96 then (if j < 94 then dst93 else (if j < 95 then dst94 else dst95)) else (if j < 98 then (if j < 97 then dst96 else dst97) else (if j < 99 then dst98 else dst99))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst100 else (if j < 102 then dst101 else dst102)) else (if j < 104 then dst103 else (if j < 105 then dst104 else dst105))) else (if j < 109 then (if j < 107 then dst106 else (if j < 108 then dst107 else dst108)) else (if j < 110 then dst109 else (if j < 111 then dst110 else dst111)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst112 else (if j < 114 then dst113 else dst114)) else (if j < 116 then dst115 else (if j < 117 then dst116 else dst117))) else (if j < 121 then (if j < 119 then dst118 else (if j < 120 then dst119 else dst120)) else (if j < 123 then (if j < 122 then dst121 else dst122) else (if j < 124 then dst123 else dst124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst125 else (if j < 127 then dst126 else dst127)) else (if j < 129 then dst128 else (if j < 130 then dst129 else dst130))) else (if j < 134 then (if j < 132 then dst131 else (if j < 133 then dst132 else dst133)) else (if j < 135 then dst134 else (if j < 136 then dst135 else dst136)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst137 else (if j < 139 then dst138 else dst139)) else (if j < 141 then dst140 else (if j < 142 then dst141 else dst142))) else (if j < 146 then (if j < 144 then dst143 else (if j < 145 then dst144 else dst145)) else (if j < 148 then (if j < 147 then dst146 else dst147) else (if j < 149 then dst148 else dst149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst150 else (if j < 152 then dst151 else dst152)) else (if j < 154 then dst153 else (if j < 155 then dst154 else dst155))) else (if j < 159 then (if j < 157 then dst156 else (if j < 158 then dst157 else dst158)) else (if j < 160 then dst159 else (if j < 161 then dst160 else dst161)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst162 else (if j < 164 then dst163 else dst164)) else (if j < 166 then dst165 else (if j < 167 then dst166 else dst167))) else (if j < 171 then (if j < 169 then dst168 else (if j < 170 then dst169 else dst170)) else (if j < 173 then (if j < 172 then dst171 else dst172) else (if j < 174 then dst173 else dst174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst175 else (if j < 177 then dst176 else dst177)) else (if j < 179 then dst178 else (if j < 180 then dst179 else dst180))) else (if j < 184 then (if j < 182 then dst181 else (if j < 183 then dst182 else dst183)) else (if j < 185 then dst184 else (if j < 186 then dst185 else dst186)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst187 else (if j < 189 then dst188 else dst189)) else (if j < 191 then dst190 else (if j < 192 then dst191 else dst192))) else (if j < 196 then (if j < 194 then dst193 else (if j < 195 then dst194 else dst195)) else (if j < 198 then (if j < 197 then dst196 else dst197) else (if j < 199 then dst198 else dst199))))))))

def caseB0 (i : Fin 200) : Cases := ⟨0 + i.val,by have := i.isLt; omega⟩
lemma tableB0_valid (i : Fin 200) :
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
  · exact valid_data100
  · exact valid_data101
  · exact valid_data102
  · exact valid_data103
  · exact valid_data104
  · exact valid_data105
  · exact valid_data106
  · exact valid_data107
  · exact valid_data108
  · exact valid_data109
  · exact valid_data110
  · exact valid_data111
  · exact valid_data112
  · exact valid_data113
  · exact valid_data114
  · exact valid_data115
  · exact valid_data116
  · exact valid_data117
  · exact valid_data118
  · exact valid_data119
  · exact valid_data120
  · exact valid_data121
  · exact valid_data122
  · exact valid_data123
  · exact valid_data124
  · exact valid_data125
  · exact valid_data126
  · exact valid_data127
  · exact valid_data128
  · exact valid_data129
  · exact valid_data130
  · exact valid_data131
  · exact valid_data132
  · exact valid_data133
  · exact valid_data134
  · exact valid_data135
  · exact valid_data136
  · exact valid_data137
  · exact valid_data138
  · exact valid_data139
  · exact valid_data140
  · exact valid_data141
  · exact valid_data142
  · exact valid_data143
  · exact valid_data144
  · exact valid_data145
  · exact valid_data146
  · exact valid_data147
  · exact valid_data148
  · exact valid_data149
  · exact valid_data150
  · exact valid_data151
  · exact valid_data152
  · exact valid_data153
  · exact valid_data154
  · exact valid_data155
  · exact valid_data156
  · exact valid_data157
  · exact valid_data158
  · exact valid_data159
  · exact valid_data160
  · exact valid_data161
  · exact valid_data162
  · exact valid_data163
  · exact valid_data164
  · exact valid_data165
  · exact valid_data166
  · exact valid_data167
  · exact valid_data168
  · exact valid_data169
  · exact valid_data170
  · exact valid_data171
  · exact valid_data172
  · exact valid_data173
  · exact valid_data174
  · exact valid_data175
  · exact valid_data176
  · exact valid_data177
  · exact valid_data178
  · exact valid_data179
  · exact valid_data180
  · exact valid_data181
  · exact valid_data182
  · exact valid_data183
  · exact valid_data184
  · exact valid_data185
  · exact valid_data186
  · exact valid_data187
  · exact valid_data188
  · exact valid_data189
  · exact valid_data190
  · exact valid_data191
  · exact valid_data192
  · exact valid_data193
  · exact valid_data194
  · exact valid_data195
  · exact valid_data196
  · exact valid_data197
  · exact valid_data198
  · exact valid_data199

lemma srcB0_row : ∀ (i : Fin 200) (e : E),
    srcTableB0 i.val e = caseSource (caseB0 i) e := by decide +kernel

lemma dstB0_row : ∀ (i : Fin 200) (e : E),
    dstTableB0 i.val e = caseTarget (caseB0 i) e := by decide +kernel

lemma sizeB0 : ∀ i : Fin 200, (lookupB0 i.val).size ≤ 5 →
    (lookupB0 i.val).size = 2 ∧
      (⟨caseKey (caseB0 i),caseKey_lt (caseB0 i)⟩ : Fin 77760) ∈ good := by decide +kernel
lemma certificateB0 (i : Fin 200) : Certificate (caseB0 i) := by
  refine ⟨lookupB0 i.val,?_,sizeB0 i⟩
  have hv := tableB0_valid i
  rw [funext (srcB0_row i),funext (dstB0_row i)] at hv
  exact hv
lemma certificateInterval0 : FiniteIntervals.Covers CertificateAt 0 200 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 0 200 (fun i _ => certificateB0 i)
#print axioms certificateInterval0
end Erdos184Work.FiveRows2

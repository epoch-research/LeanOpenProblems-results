import Submission.FourRows8

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows8
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,13,22,6,14,7,15,22]
def dst0 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle0_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle0_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle0_2 : CycleData E W := ⟨2,![11,6,15,2],![5,12,14,6]⟩
def cycle0_3 : CycleData E W := ⟨2,![12,7,16,3],![5,13,14,7]⟩
def cycle0_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle0_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data0 : PartitionData E W := ⟨6,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,13,22,6,14,7,22,15]
def dst1 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle1_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,4]⟩
def cycle1_1 : CycleData E W := ⟨2,![11,6,15,2],![5,12,14,6]⟩
def cycle1_2 : CycleData E W := ⟨2,![12,7,16,3],![5,13,14,7]⟩
def cycle1_3 : CycleData E W := ⟨3,![5,10,14,17,4],![2,12,4,22,7]⟩
def cycle1_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data1 : PartitionData E W := ⟨5,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,13,22,6,14,22,7,15]
def dst2 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle2_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,6,4]⟩
def cycle2_1 : CycleData E W := ⟨2,![12,13,17,3],![5,13,22,7]⟩
def cycle2_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle2_3 : CycleData E W := ⟨2,![14,16,6,10],![4,22,14,12]⟩
def cycle2_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,13,14]⟩
def data2 : PartitionData E W := ⟨5,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,13,22,6,15,7,14,22]
def dst3 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle3_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle3_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle3_2 : CycleData E W := ⟨2,![12,8,15,2],![5,13,15,6]⟩
def cycle3_3 : CycleData E W := ⟨2,![11,6,17,3],![5,12,14,7]⟩
def cycle3_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle3_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data3 : PartitionData E W := ⟨6,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4,cycle3_5]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,22,13,6,14,7,15,22]
def dst4 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle4_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle4_1 : CycleData E W := ⟨2,![14,7,15,1],![4,13,14,6]⟩
def cycle4_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle4_3 : CycleData E W := ⟨2,![11,6,16,3],![5,12,14,7]⟩
def cycle4_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle4_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data4 : PartitionData E W := ⟨6,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4,cycle4_5]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,22,13,6,14,7,22,15]
def dst5 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle5_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,6,4]⟩
def cycle5_1 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle5_2 : CycleData E W := ⟨3,![9,19,15,16,4],![2,15,6,14,7]⟩
def cycle5_3 : CycleData E W := ⟨2,![14,7,6,10],![4,13,14,12]⟩
def cycle5_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data5 : PartitionData E W := ⟨5,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,22,13,6,14,22,7,15]
def dst6 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle6_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle6_1 : CycleData E W := ⟨2,![14,8,19,1],![4,13,15,6]⟩
def cycle6_2 : CycleData E W := ⟨2,![11,6,15,2],![5,12,14,6]⟩
def cycle6_3 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle6_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle6_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data6 : PartitionData E W := ⟨6,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4,cycle6_5]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,5,22,13,6,15,7,14,22]
def dst7 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle7_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle7_1 : CycleData E W := ⟨2,![14,8,15,1],![4,13,15,6]⟩
def cycle7_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle7_3 : CycleData E W := ⟨2,![11,6,17,3],![5,12,14,7]⟩
def cycle7_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle7_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data7 : PartitionData E W := ⟨6,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,22,5,13,6,14,7,15,22]
def dst8 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle8_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,12,14,6,4]⟩
def cycle8_1 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle8_2 : CycleData E W := ⟨2,![13,7,16,3],![5,13,14,7]⟩
def cycle8_3 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle8_4 : CycleData E W := ⟨3,![14,8,18,11,10],![4,13,15,22,12]⟩
def data8 : PartitionData E W := ⟨5,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,22,5,13,6,14,7,22,15]
def dst9 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle9_0 : CycleData E W := ⟨3,![4,16,15,1,0],![2,7,14,6,4]⟩
def cycle9_1 : CycleData E W := ⟨2,![13,8,19,2],![5,13,15,6]⟩
def cycle9_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle9_3 : CycleData E W := ⟨2,![9,18,11,5],![2,15,22,12]⟩
def cycle9_4 : CycleData E W := ⟨2,![14,7,6,10],![4,13,14,12]⟩
def data9 : PartitionData E W := ⟨5,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,22,5,13,6,14,22,7,15]
def dst10 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle10_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle10_1 : CycleData E W := ⟨2,![14,13,2,1],![4,13,5,6]⟩
def cycle10_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle10_3 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle10_4 : CycleData E W := ⟨1,![11,16,6],![12,22,14]⟩
def cycle10_5 : CycleData E W := ⟨2,![19,8,7,15],![6,15,13,14]⟩
def data10 : PartitionData E W := ⟨6,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4,cycle10_5]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,12,22,5,13,6,15,7,14,22]
def dst11 : E → W := ![4,6,5,7,2,12,14,13,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle11_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle11_1 : CycleData E W := ⟨2,![14,8,15,1],![4,13,15,6]⟩
def cycle11_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle11_3 : CycleData E W := ⟨2,![13,7,17,3],![5,13,14,7]⟩
def cycle11_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle11_5 : CycleData E W := ⟨1,![11,18,6],![12,22,14]⟩
def data11 : PartitionData E W := ⟨6,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4,cycle11_5]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,13,5,12,22,6,14,7,15,22]
def dst12 : E → W := ![4,6,5,7,2,12,14,13,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle12_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle12_1 : CycleData E W := ⟨2,![11,7,16,3],![5,13,14,7]⟩
def cycle12_2 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle12_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,12,14]⟩
def cycle12_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,13]⟩
def data12 : PartitionData E W := ⟨5,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,13,5,12,22,6,14,7,22,15]
def dst13 : E → W := ![4,6,5,7,2,12,14,13,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle13_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,4]⟩
def cycle13_1 : CycleData E W := ⟨2,![12,6,15,2],![5,12,14,6]⟩
def cycle13_2 : CycleData E W := ⟨2,![11,7,16,3],![5,13,14,7]⟩
def cycle13_3 : CycleData E W := ⟨2,![5,13,17,4],![2,12,22,7]⟩
def cycle13_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,13]⟩
def data13 : PartitionData E W := ⟨5,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,13,5,12,22,6,14,22,7,15]
def dst14 : E → W := ![4,6,5,7,2,12,14,13,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle14_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle14_1 : CycleData E W := ⟨3,![14,17,3,11,10],![4,22,7,5,13]⟩
def cycle14_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle14_3 : CycleData E W := ⟨1,![13,16,6],![12,22,14]⟩
def cycle14_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,13,14]⟩
def data14 : PartitionData E W := ⟨5,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,6,5,7,2,12,14,13,15,4,13,5,12,22,6,15,7,14,22]
def dst15 : E → W := ![4,6,5,7,2,12,14,13,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle15_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle15_1 : CycleData E W := ⟨2,![11,7,17,3],![5,13,14,7]⟩
def cycle15_2 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle15_3 : CycleData E W := ⟨1,![13,18,6],![12,22,14]⟩
def cycle15_4 : CycleData E W := ⟨3,![14,19,15,8,10],![4,22,6,15,13]⟩
def data15 : PartitionData E W := ⟨5,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,13,22,6,14,7,15,22]
def dst16 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle16_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle16_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle16_2 : CycleData E W := ⟨2,![12,8,15,2],![5,13,14,6]⟩
def cycle16_3 : CycleData E W := ⟨2,![11,6,17,3],![5,12,15,7]⟩
def cycle16_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle16_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data16 : PartitionData E W := ⟨6,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4,cycle16_5]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,13,22,6,14,7,22,15]
def dst17 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle17_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,6,4]⟩
def cycle17_1 : CycleData E W := ⟨2,![12,13,17,3],![5,13,22,7]⟩
def cycle17_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle17_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,15,12]⟩
def cycle17_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,13,14]⟩
def data17 : PartitionData E W := ⟨5,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,13,22,6,14,22,7,15]
def dst18 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle18_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle18_1 : CycleData E W := ⟨2,![11,6,19,2],![5,12,15,6]⟩
def cycle18_2 : CycleData E W := ⟨2,![12,7,18,3],![5,13,15,7]⟩
def cycle18_3 : CycleData E W := ⟨3,![5,10,14,17,4],![2,12,4,22,7]⟩
def cycle18_4 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data18 : PartitionData E W := ⟨5,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,13,22,6,15,7,14,22]
def dst19 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle19_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle19_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle19_2 : CycleData E W := ⟨2,![11,6,15,2],![5,12,15,6]⟩
def cycle19_3 : CycleData E W := ⟨2,![12,7,16,3],![5,13,15,7]⟩
def cycle19_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle19_5 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data19 : PartitionData E W := ⟨6,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4,cycle19_5]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,22,13,6,14,7,15,22]
def dst20 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle20_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle20_1 : CycleData E W := ⟨2,![14,8,15,1],![4,13,14,6]⟩
def cycle20_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle20_3 : CycleData E W := ⟨2,![11,6,17,3],![5,12,15,7]⟩
def cycle20_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle20_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data20 : PartitionData E W := ⟨6,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4,cycle20_5]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,22,13,6,14,7,22,15]
def dst21 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle21_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle21_1 : CycleData E W := ⟨2,![14,8,15,1],![4,13,14,6]⟩
def cycle21_2 : CycleData E W := ⟨2,![11,6,19,2],![5,12,15,6]⟩
def cycle21_3 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle21_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle21_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data21 : PartitionData E W := ⟨6,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4,cycle21_5]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,22,13,6,14,22,7,15]
def dst22 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle22_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,6,4]⟩
def cycle22_1 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle22_2 : CycleData E W := ⟨3,![9,15,19,18,4],![2,14,6,15,7]⟩
def cycle22_3 : CycleData E W := ⟨2,![14,7,6,10],![4,13,15,12]⟩
def cycle22_4 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data22 : PartitionData E W := ⟨5,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,5,22,13,6,15,7,14,22]
def dst23 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle23_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle23_1 : CycleData E W := ⟨2,![14,7,15,1],![4,13,15,6]⟩
def cycle23_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle23_3 : CycleData E W := ⟨2,![11,6,16,3],![5,12,15,7]⟩
def cycle23_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle23_5 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data23 : PartitionData E W := ⟨6,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4,cycle23_5]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,22,5,13,6,14,7,15,22]
def dst24 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle24_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle24_1 : CycleData E W := ⟨2,![14,8,15,1],![4,13,14,6]⟩
def cycle24_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle24_3 : CycleData E W := ⟨2,![13,7,17,3],![5,13,15,7]⟩
def cycle24_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle24_5 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def data24 : PartitionData E W := ⟨6,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4,cycle24_5]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,22,5,13,6,14,7,22,15]
def dst25 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle25_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle25_1 : CycleData E W := ⟨2,![14,13,2,1],![4,13,5,6]⟩
def cycle25_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle25_3 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle25_4 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle25_5 : CycleData E W := ⟨2,![19,7,8,15],![6,15,13,14]⟩
def data25 : PartitionData E W := ⟨6,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4,cycle25_5]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,22,5,13,6,14,22,7,15]
def dst26 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle26_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle26_1 : CycleData E W := ⟨2,![13,7,19,2],![5,13,15,6]⟩
def cycle26_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle26_3 : CycleData E W := ⟨2,![5,6,18,4],![2,12,15,7]⟩
def cycle26_4 : CycleData E W := ⟨3,![14,8,16,11,10],![4,13,14,22,12]⟩
def data26 : PartitionData E W := ⟨5,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,12,22,5,13,6,15,7,14,22]
def dst27 : E → W := ![4,6,5,7,2,12,15,13,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle27_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,12,15,6,4]⟩
def cycle27_1 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle27_2 : CycleData E W := ⟨2,![13,7,16,3],![5,13,15,7]⟩
def cycle27_3 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle27_4 : CycleData E W := ⟨3,![14,8,18,11,10],![4,13,14,22,12]⟩
def data27 : PartitionData E W := ⟨5,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,13,5,12,22,6,14,7,15,22]
def dst28 : E → W := ![4,6,5,7,2,12,15,13,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle28_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle28_1 : CycleData E W := ⟨2,![11,7,17,3],![5,13,15,7]⟩
def cycle28_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle28_3 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def cycle28_4 : CycleData E W := ⟨3,![14,19,15,8,10],![4,22,6,14,13]⟩
def data28 : PartitionData E W := ⟨5,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,13,5,12,22,6,14,7,22,15]
def dst29 : E → W := ![4,6,5,7,2,12,15,13,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle29_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle29_1 : CycleData E W := ⟨3,![14,17,3,11,10],![4,22,7,5,13]⟩
def cycle29_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle29_3 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def cycle29_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,13,14]⟩
def data29 : PartitionData E W := ⟨5,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,13,5,12,22,6,14,22,7,15]
def dst30 : E → W := ![4,6,5,7,2,12,15,13,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle30_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle30_1 : CycleData E W := ⟨2,![12,6,19,2],![5,12,15,6]⟩
def cycle30_2 : CycleData E W := ⟨2,![11,7,18,3],![5,13,15,7]⟩
def cycle30_3 : CycleData E W := ⟨2,![5,13,17,4],![2,12,22,7]⟩
def cycle30_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,13]⟩
def data30 : PartitionData E W := ⟨5,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,6,5,7,2,12,15,13,14,4,13,5,12,22,6,15,7,14,22]
def dst31 : E → W := ![4,6,5,7,2,12,15,13,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle31_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,6,4]⟩
def cycle31_1 : CycleData E W := ⟨2,![11,7,16,3],![5,13,15,7]⟩
def cycle31_2 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle31_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,12,15]⟩
def cycle31_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,14,13]⟩
def data31 : PartitionData E W := ⟨5,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,13,22,6,14,7,15,22]
def dst32 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle32_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle32_1 : CycleData E W := ⟨2,![11,7,16,3],![5,12,14,7]⟩
def cycle32_2 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle32_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,13,14]⟩
def cycle32_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,12]⟩
def data32 : PartitionData E W := ⟨5,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,13,22,6,14,7,22,15]
def dst33 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle33_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,4]⟩
def cycle33_1 : CycleData E W := ⟨2,![12,6,15,2],![5,13,14,6]⟩
def cycle33_2 : CycleData E W := ⟨2,![11,7,16,3],![5,12,14,7]⟩
def cycle33_3 : CycleData E W := ⟨2,![5,13,17,4],![2,13,22,7]⟩
def cycle33_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,12]⟩
def data33 : PartitionData E W := ⟨5,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,13,22,6,14,22,7,15]
def dst34 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle34_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle34_1 : CycleData E W := ⟨3,![14,17,3,11,10],![4,22,7,5,12]⟩
def cycle34_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle34_3 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def cycle34_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,12,14]⟩
def data34 : PartitionData E W := ⟨5,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,13,22,6,15,7,14,22]
def dst35 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle35_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle35_1 : CycleData E W := ⟨2,![11,7,17,3],![5,12,14,7]⟩
def cycle35_2 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle35_3 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def cycle35_4 : CycleData E W := ⟨3,![14,19,15,8,10],![4,22,6,15,12]⟩
def data35 : PartitionData E W := ⟨5,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def src36 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,22,13,6,14,7,15,22]
def dst36 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle36_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,13,14,6,4]⟩
def cycle36_1 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle36_2 : CycleData E W := ⟨2,![11,7,16,3],![5,12,14,7]⟩
def cycle36_3 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle36_4 : CycleData E W := ⟨3,![14,13,18,8,10],![4,13,22,15,12]⟩
def data36 : PartitionData E W := ⟨5,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4]⟩
lemma valid_data36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel

def src37 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,22,13,6,14,7,22,15]
def dst37 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle37_0 : CycleData E W := ⟨3,![4,16,15,1,0],![2,7,14,6,4]⟩
def cycle37_1 : CycleData E W := ⟨2,![11,8,19,2],![5,12,15,6]⟩
def cycle37_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle37_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,13]⟩
def cycle37_4 : CycleData E W := ⟨2,![14,6,7,10],![4,13,14,12]⟩
def data37 : PartitionData E W := ⟨5,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4]⟩
lemma valid_data37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel

def src38 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,22,13,6,14,22,7,15]
def dst38 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle38_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle38_1 : CycleData E W := ⟨2,![10,11,2,1],![4,12,5,6]⟩
def cycle38_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle38_3 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle38_4 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def cycle38_5 : CycleData E W := ⟨2,![19,8,7,15],![6,15,12,14]⟩
def data38 : PartitionData E W := ⟨6,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4,cycle38_5]⟩
lemma valid_data38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel

def src39 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,5,22,13,6,15,7,14,22]
def dst39 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle39_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle39_1 : CycleData E W := ⟨2,![10,8,15,1],![4,12,15,6]⟩
def cycle39_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle39_3 : CycleData E W := ⟨2,![11,7,17,3],![5,12,14,7]⟩
def cycle39_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle39_5 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def data39 : PartitionData E W := ⟨6,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4,cycle39_5]⟩
lemma valid_data39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel

def src40 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,22,5,13,6,14,7,15,22]
def dst40 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle40_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle40_1 : CycleData E W := ⟨2,![10,7,15,1],![4,12,14,6]⟩
def cycle40_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle40_3 : CycleData E W := ⟨2,![13,6,16,3],![5,13,14,7]⟩
def cycle40_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle40_5 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data40 : PartitionData E W := ⟨6,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4,cycle40_5]⟩
lemma valid_data40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel

def src41 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,22,5,13,6,14,7,22,15]
def dst41 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle41_0 : CycleData E W := ⟨3,![5,13,2,1,0],![2,13,5,6,4]⟩
def cycle41_1 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle41_2 : CycleData E W := ⟨3,![9,19,15,16,4],![2,15,6,14,7]⟩
def cycle41_3 : CycleData E W := ⟨2,![14,6,7,10],![4,13,14,12]⟩
def cycle41_4 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data41 : PartitionData E W := ⟨5,![cycle41_0,cycle41_1,cycle41_2,cycle41_3,cycle41_4]⟩
lemma valid_data41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel

def src42 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,22,5,13,6,14,22,7,15]
def dst42 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle42_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle42_1 : CycleData E W := ⟨2,![10,8,19,1],![4,12,15,6]⟩
def cycle42_2 : CycleData E W := ⟨2,![13,6,15,2],![5,13,14,6]⟩
def cycle42_3 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle42_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle42_5 : CycleData E W := ⟨1,![11,16,7],![12,22,14]⟩
def data42 : PartitionData E W := ⟨6,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4,cycle42_5]⟩
lemma valid_data42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel

def src43 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,12,22,5,13,6,15,7,14,22]
def dst43 : E → W := ![4,6,5,7,2,13,14,12,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle43_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle43_1 : CycleData E W := ⟨2,![10,8,15,1],![4,12,15,6]⟩
def cycle43_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle43_3 : CycleData E W := ⟨2,![13,6,17,3],![5,13,14,7]⟩
def cycle43_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle43_5 : CycleData E W := ⟨1,![11,18,7],![12,22,14]⟩
def data43 : PartitionData E W := ⟨6,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4,cycle43_5]⟩
lemma valid_data43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel

def src44 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,13,5,12,22,6,14,7,15,22]
def dst44 : E → W := ![4,6,5,7,2,13,14,12,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle44_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle44_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle44_2 : CycleData E W := ⟨2,![11,6,15,2],![5,13,14,6]⟩
def cycle44_3 : CycleData E W := ⟨2,![12,7,16,3],![5,12,14,7]⟩
def cycle44_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle44_5 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data44 : PartitionData E W := ⟨6,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4,cycle44_5]⟩
lemma valid_data44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel

def src45 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,13,5,12,22,6,14,7,22,15]
def dst45 : E → W := ![4,6,5,7,2,13,14,12,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle45_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,4]⟩
def cycle45_1 : CycleData E W := ⟨2,![11,6,15,2],![5,13,14,6]⟩
def cycle45_2 : CycleData E W := ⟨2,![12,7,16,3],![5,12,14,7]⟩
def cycle45_3 : CycleData E W := ⟨3,![5,10,14,17,4],![2,13,4,22,7]⟩
def cycle45_4 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data45 : PartitionData E W := ⟨5,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4]⟩
lemma valid_data45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel

def src46 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,13,5,12,22,6,14,22,7,15]
def dst46 : E → W := ![4,6,5,7,2,13,14,12,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle46_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,13,5,6,4]⟩
def cycle46_1 : CycleData E W := ⟨2,![12,13,17,3],![5,12,22,7]⟩
def cycle46_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle46_3 : CycleData E W := ⟨2,![14,16,6,10],![4,22,14,13]⟩
def cycle46_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,12,14]⟩
def data46 : PartitionData E W := ⟨5,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4]⟩
lemma valid_data46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel

def src47 : E → W := ![2,4,6,5,7,2,13,14,12,15,4,13,5,12,22,6,15,7,14,22]
def dst47 : E → W := ![4,6,5,7,2,13,14,12,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle47_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle47_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle47_2 : CycleData E W := ⟨2,![12,8,15,2],![5,12,15,6]⟩
def cycle47_3 : CycleData E W := ⟨2,![11,6,17,3],![5,13,14,7]⟩
def cycle47_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle47_5 : CycleData E W := ⟨1,![13,18,7],![12,22,14]⟩
def data47 : PartitionData E W := ⟨6,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4,cycle47_5]⟩
lemma valid_data47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel

def src48 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,13,22,6,14,7,15,22]
def dst48 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle48_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle48_1 : CycleData E W := ⟨2,![11,7,17,3],![5,12,15,7]⟩
def cycle48_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle48_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle48_4 : CycleData E W := ⟨3,![14,19,15,8,10],![4,22,6,14,12]⟩
def data48 : PartitionData E W := ⟨5,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4]⟩
lemma valid_data48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel

def src49 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,13,22,6,14,7,22,15]
def dst49 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle49_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle49_1 : CycleData E W := ⟨3,![14,17,3,11,10],![4,22,7,5,12]⟩
def cycle49_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle49_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle49_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,12,14]⟩
def data49 : PartitionData E W := ⟨5,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4]⟩
lemma valid_data49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel

def src50 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,13,22,6,14,22,7,15]
def dst50 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle50_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle50_1 : CycleData E W := ⟨2,![12,6,19,2],![5,13,15,6]⟩
def cycle50_2 : CycleData E W := ⟨2,![11,7,18,3],![5,12,15,7]⟩
def cycle50_3 : CycleData E W := ⟨2,![5,13,17,4],![2,13,22,7]⟩
def cycle50_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,12]⟩
def data50 : PartitionData E W := ⟨5,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4]⟩
lemma valid_data50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel

def src51 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,13,22,6,15,7,14,22]
def dst51 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle51_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,6,4]⟩
def cycle51_1 : CycleData E W := ⟨2,![11,7,16,3],![5,12,15,7]⟩
def cycle51_2 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle51_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,13,15]⟩
def cycle51_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,14,12]⟩
def data51 : PartitionData E W := ⟨5,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4]⟩
lemma valid_data51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel

def src52 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,22,13,6,14,7,15,22]
def dst52 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle52_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle52_1 : CycleData E W := ⟨2,![10,8,15,1],![4,12,14,6]⟩
def cycle52_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle52_3 : CycleData E W := ⟨2,![11,7,17,3],![5,12,15,7]⟩
def cycle52_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle52_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data52 : PartitionData E W := ⟨6,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5]⟩
lemma valid_data52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel

def src53 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,22,13,6,14,7,22,15]
def dst53 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle53_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle53_1 : CycleData E W := ⟨2,![10,11,2,1],![4,12,5,6]⟩
def cycle53_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle53_3 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle53_4 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle53_5 : CycleData E W := ⟨2,![19,7,8,15],![6,15,12,14]⟩
def data53 : PartitionData E W := ⟨6,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4,cycle53_5]⟩
lemma valid_data53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel

def src54 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,22,13,6,14,22,7,15]
def dst54 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle54_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle54_1 : CycleData E W := ⟨2,![11,7,19,2],![5,12,15,6]⟩
def cycle54_2 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle54_3 : CycleData E W := ⟨2,![5,6,18,4],![2,13,15,7]⟩
def cycle54_4 : CycleData E W := ⟨3,![14,13,16,8,10],![4,13,22,14,12]⟩
def data54 : PartitionData E W := ⟨5,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4]⟩
lemma valid_data54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel

def src55 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,5,22,13,6,15,7,14,22]
def dst55 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle55_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,13,15,6,4]⟩
def cycle55_1 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle55_2 : CycleData E W := ⟨2,![11,7,16,3],![5,12,15,7]⟩
def cycle55_3 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle55_4 : CycleData E W := ⟨3,![14,13,18,8,10],![4,13,22,14,12]⟩
def data55 : PartitionData E W := ⟨5,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4]⟩
lemma valid_data55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel

def src56 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,22,5,13,6,14,7,15,22]
def dst56 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle56_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle56_1 : CycleData E W := ⟨2,![10,8,15,1],![4,12,14,6]⟩
def cycle56_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle56_3 : CycleData E W := ⟨2,![13,6,17,3],![5,13,15,7]⟩
def cycle56_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle56_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data56 : PartitionData E W := ⟨6,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4,cycle56_5]⟩
lemma valid_data56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel

def src57 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,22,5,13,6,14,7,22,15]
def dst57 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle57_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle57_1 : CycleData E W := ⟨2,![10,8,15,1],![4,12,14,6]⟩
def cycle57_2 : CycleData E W := ⟨2,![13,6,19,2],![5,13,15,6]⟩
def cycle57_3 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle57_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle57_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data57 : PartitionData E W := ⟨6,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4,cycle57_5]⟩
lemma valid_data57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel

def src58 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,22,5,13,6,14,22,7,15]
def dst58 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle58_0 : CycleData E W := ⟨3,![5,13,2,1,0],![2,13,5,6,4]⟩
def cycle58_1 : CycleData E W := ⟨1,![12,17,3],![5,22,7]⟩
def cycle58_2 : CycleData E W := ⟨3,![9,15,19,18,4],![2,14,6,15,7]⟩
def cycle58_3 : CycleData E W := ⟨2,![14,6,7,10],![4,13,15,12]⟩
def cycle58_4 : CycleData E W := ⟨1,![11,16,8],![12,22,14]⟩
def data58 : PartitionData E W := ⟨5,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4]⟩
lemma valid_data58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel

def src59 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,12,22,5,13,6,15,7,14,22]
def dst59 : E → W := ![4,6,5,7,2,13,15,12,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle59_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle59_1 : CycleData E W := ⟨2,![10,7,15,1],![4,12,15,6]⟩
def cycle59_2 : CycleData E W := ⟨1,![12,19,2],![5,22,6]⟩
def cycle59_3 : CycleData E W := ⟨2,![13,6,16,3],![5,13,15,7]⟩
def cycle59_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle59_5 : CycleData E W := ⟨1,![11,18,8],![12,22,14]⟩
def data59 : PartitionData E W := ⟨6,![cycle59_0,cycle59_1,cycle59_2,cycle59_3,cycle59_4,cycle59_5]⟩
lemma valid_data59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel

def src60 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,13,5,12,22,6,14,7,15,22]
def dst60 : E → W := ![4,6,5,7,2,13,15,12,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle60_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle60_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle60_2 : CycleData E W := ⟨2,![12,8,15,2],![5,12,14,6]⟩
def cycle60_3 : CycleData E W := ⟨2,![11,6,17,3],![5,13,15,7]⟩
def cycle60_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle60_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data60 : PartitionData E W := ⟨6,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4,cycle60_5]⟩
lemma valid_data60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel

def src61 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,13,5,12,22,6,14,7,22,15]
def dst61 : E → W := ![4,6,5,7,2,13,15,12,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle61_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,13,5,6,4]⟩
def cycle61_1 : CycleData E W := ⟨2,![12,13,17,3],![5,12,22,7]⟩
def cycle61_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle61_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,15,13]⟩
def cycle61_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,12,14]⟩
def data61 : PartitionData E W := ⟨5,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4]⟩
lemma valid_data61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel

def src62 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,13,5,12,22,6,14,22,7,15]
def dst62 : E → W := ![4,6,5,7,2,13,15,12,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle62_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,4]⟩
def cycle62_1 : CycleData E W := ⟨2,![11,6,19,2],![5,13,15,6]⟩
def cycle62_2 : CycleData E W := ⟨2,![12,7,18,3],![5,12,15,7]⟩
def cycle62_3 : CycleData E W := ⟨3,![5,10,14,17,4],![2,13,4,22,7]⟩
def cycle62_4 : CycleData E W := ⟨1,![13,16,8],![12,22,14]⟩
def data62 : PartitionData E W := ⟨5,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4]⟩
lemma valid_data62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel

def src63 : E → W := ![2,4,6,5,7,2,13,15,12,14,4,13,5,12,22,6,15,7,14,22]
def dst63 : E → W := ![4,6,5,7,2,13,15,12,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle63_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle63_1 : CycleData E W := ⟨1,![14,19,1],![4,22,6]⟩
def cycle63_2 : CycleData E W := ⟨2,![11,6,15,2],![5,13,15,6]⟩
def cycle63_3 : CycleData E W := ⟨2,![12,7,16,3],![5,12,15,7]⟩
def cycle63_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle63_5 : CycleData E W := ⟨1,![13,18,8],![12,22,14]⟩
def data63 : PartitionData E W := ⟨6,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4,cycle63_5]⟩
lemma valid_data63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel

def src64 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,13,22,6,14,7,15,22]
def dst64 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle64_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,4]⟩
def cycle64_1 : CycleData E W := ⟨2,![11,6,16,2],![5,12,14,7]⟩
def cycle64_2 : CycleData E W := ⟨2,![12,7,15,3],![5,13,14,6]⟩
def cycle64_3 : CycleData E W := ⟨3,![5,10,14,19,4],![2,12,4,22,6]⟩
def cycle64_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data64 : PartitionData E W := ⟨5,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4]⟩
lemma valid_data64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel

def src65 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,13,22,6,14,7,22,15]
def dst65 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle65_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle65_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle65_2 : CycleData E W := ⟨2,![11,6,16,2],![5,12,14,7]⟩
def cycle65_3 : CycleData E W := ⟨2,![12,7,15,3],![5,13,14,6]⟩
def cycle65_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle65_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data65 : PartitionData E W := ⟨6,![cycle65_0,cycle65_1,cycle65_2,cycle65_3,cycle65_4,cycle65_5]⟩
lemma valid_data65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel

def src66 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,13,22,6,14,22,7,15]
def dst66 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle66_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle66_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle66_2 : CycleData E W := ⟨2,![12,8,18,2],![5,13,15,7]⟩
def cycle66_3 : CycleData E W := ⟨2,![11,6,15,3],![5,12,14,6]⟩
def cycle66_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle66_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data66 : PartitionData E W := ⟨6,![cycle66_0,cycle66_1,cycle66_2,cycle66_3,cycle66_4,cycle66_5]⟩
lemma valid_data66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel

def src67 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,13,22,6,15,7,14,22]
def dst67 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle67_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,7,4]⟩
def cycle67_1 : CycleData E W := ⟨2,![12,13,19,3],![5,13,22,6]⟩
def cycle67_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle67_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,14,12]⟩
def cycle67_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,13,15]⟩
def data67 : PartitionData E W := ⟨5,![cycle67_0,cycle67_1,cycle67_2,cycle67_3,cycle67_4]⟩
lemma valid_data67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel

def src68 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,22,13,6,14,7,15,22]
def dst68 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle68_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,7,4]⟩
def cycle68_1 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle68_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,15,7,14,6]⟩
def cycle68_3 : CycleData E W := ⟨2,![14,7,6,10],![4,13,14,12]⟩
def cycle68_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data68 : PartitionData E W := ⟨5,![cycle68_0,cycle68_1,cycle68_2,cycle68_3,cycle68_4]⟩
lemma valid_data68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel

def src69 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,22,13,6,14,7,22,15]
def dst69 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle69_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle69_1 : CycleData E W := ⟨2,![14,7,16,1],![4,13,14,7]⟩
def cycle69_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle69_3 : CycleData E W := ⟨2,![11,6,15,3],![5,12,14,6]⟩
def cycle69_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle69_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data69 : PartitionData E W := ⟨6,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4,cycle69_5]⟩
lemma valid_data69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel

def src70 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,22,13,6,14,22,7,15]
def dst70 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle70_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle70_1 : CycleData E W := ⟨2,![14,8,18,1],![4,13,15,7]⟩
def cycle70_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle70_3 : CycleData E W := ⟨2,![11,6,15,3],![5,12,14,6]⟩
def cycle70_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle70_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data70 : PartitionData E W := ⟨6,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4,cycle70_5]⟩
lemma valid_data70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel

def src71 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,5,22,13,6,15,7,14,22]
def dst71 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle71_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle71_1 : CycleData E W := ⟨2,![14,8,16,1],![4,13,15,7]⟩
def cycle71_2 : CycleData E W := ⟨2,![11,6,17,2],![5,12,14,7]⟩
def cycle71_3 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle71_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle71_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data71 : PartitionData E W := ⟨6,![cycle71_0,cycle71_1,cycle71_2,cycle71_3,cycle71_4,cycle71_5]⟩
lemma valid_data71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel

def src72 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,22,5,13,6,14,7,15,22]
def dst72 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle72_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,14,7,4]⟩
def cycle72_1 : CycleData E W := ⟨2,![13,8,17,2],![5,13,15,7]⟩
def cycle72_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle72_3 : CycleData E W := ⟨2,![9,18,11,5],![2,15,22,12]⟩
def cycle72_4 : CycleData E W := ⟨2,![14,7,6,10],![4,13,14,12]⟩
def data72 : PartitionData E W := ⟨5,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4]⟩
lemma valid_data72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel

def src73 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,22,5,13,6,14,7,22,15]
def dst73 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle73_0 : CycleData E W := ⟨3,![5,6,16,1,0],![2,12,14,7,4]⟩
def cycle73_1 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle73_2 : CycleData E W := ⟨2,![13,7,15,3],![5,13,14,6]⟩
def cycle73_3 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle73_4 : CycleData E W := ⟨3,![14,8,18,11,10],![4,13,15,22,12]⟩
def data73 : PartitionData E W := ⟨5,![cycle73_0,cycle73_1,cycle73_2,cycle73_3,cycle73_4]⟩
lemma valid_data73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel

def src74 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,22,5,13,6,14,22,7,15]
def dst74 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle74_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle74_1 : CycleData E W := ⟨2,![14,8,18,1],![4,13,15,7]⟩
def cycle74_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle74_3 : CycleData E W := ⟨2,![13,7,15,3],![5,13,14,6]⟩
def cycle74_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle74_5 : CycleData E W := ⟨1,![11,16,6],![12,22,14]⟩
def data74 : PartitionData E W := ⟨6,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4,cycle74_5]⟩
lemma valid_data74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel

def src75 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,12,22,5,13,6,15,7,14,22]
def dst75 : E → W := ![4,7,5,6,2,12,14,13,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle75_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle75_1 : CycleData E W := ⟨2,![14,13,2,1],![4,13,5,7]⟩
def cycle75_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle75_3 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle75_4 : CycleData E W := ⟨1,![11,18,6],![12,22,14]⟩
def cycle75_5 : CycleData E W := ⟨2,![17,7,8,16],![7,14,13,15]⟩
def data75 : PartitionData E W := ⟨6,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4,cycle75_5]⟩
lemma valid_data75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel

def src76 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,13,5,12,22,6,14,7,15,22]
def dst76 : E → W := ![4,7,5,6,2,12,14,13,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle76_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,4]⟩
def cycle76_1 : CycleData E W := ⟨2,![12,6,16,2],![5,12,14,7]⟩
def cycle76_2 : CycleData E W := ⟨2,![11,7,15,3],![5,13,14,6]⟩
def cycle76_3 : CycleData E W := ⟨2,![5,13,19,4],![2,12,22,6]⟩
def cycle76_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,13]⟩
def data76 : PartitionData E W := ⟨5,![cycle76_0,cycle76_1,cycle76_2,cycle76_3,cycle76_4]⟩
lemma valid_data76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel

def src77 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,13,5,12,22,6,14,7,22,15]
def dst77 : E → W := ![4,7,5,6,2,12,14,13,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle77_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle77_1 : CycleData E W := ⟨2,![11,7,15,3],![5,13,14,6]⟩
def cycle77_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle77_3 : CycleData E W := ⟨2,![17,13,6,16],![7,22,12,14]⟩
def cycle77_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,13]⟩
def data77 : PartitionData E W := ⟨5,![cycle77_0,cycle77_1,cycle77_2,cycle77_3,cycle77_4]⟩
lemma valid_data77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel

def src78 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,13,5,12,22,6,14,22,7,15]
def dst78 : E → W := ![4,7,5,6,2,12,14,13,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle78_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle78_1 : CycleData E W := ⟨2,![11,7,15,3],![5,13,14,6]⟩
def cycle78_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle78_3 : CycleData E W := ⟨1,![13,16,6],![12,22,14]⟩
def cycle78_4 : CycleData E W := ⟨3,![14,17,18,8,10],![4,22,7,15,13]⟩
def data78 : PartitionData E W := ⟨5,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4]⟩
lemma valid_data78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel

def src79 : E → W := ![2,4,7,5,6,2,12,14,13,15,4,13,5,12,22,6,15,7,14,22]
def dst79 : E → W := ![4,7,5,6,2,12,14,13,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle79_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle79_1 : CycleData E W := ⟨3,![14,19,3,11,10],![4,22,6,5,13]⟩
def cycle79_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle79_3 : CycleData E W := ⟨1,![13,18,6],![12,22,14]⟩
def cycle79_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,13,15]⟩
def data79 : PartitionData E W := ⟨5,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4]⟩
lemma valid_data79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel

def src80 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,13,22,6,14,7,15,22]
def dst80 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle80_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,7,4]⟩
def cycle80_1 : CycleData E W := ⟨2,![12,13,19,3],![5,13,22,6]⟩
def cycle80_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle80_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,15,12]⟩
def cycle80_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,13,14]⟩
def data80 : PartitionData E W := ⟨5,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4]⟩
lemma valid_data80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel

def src81 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,13,22,6,14,7,22,15]
def dst81 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle81_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle81_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle81_2 : CycleData E W := ⟨2,![12,8,16,2],![5,13,14,7]⟩
def cycle81_3 : CycleData E W := ⟨2,![11,6,19,3],![5,12,15,6]⟩
def cycle81_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle81_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data81 : PartitionData E W := ⟨6,![cycle81_0,cycle81_1,cycle81_2,cycle81_3,cycle81_4,cycle81_5]⟩
lemma valid_data81 : data81.Valid src81 dst81 Finset.univ := by decide +kernel

def src82 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,13,22,6,14,22,7,15]
def dst82 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle82_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle82_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle82_2 : CycleData E W := ⟨2,![11,6,18,2],![5,12,15,7]⟩
def cycle82_3 : CycleData E W := ⟨2,![12,7,19,3],![5,13,15,6]⟩
def cycle82_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle82_5 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data82 : PartitionData E W := ⟨6,![cycle82_0,cycle82_1,cycle82_2,cycle82_3,cycle82_4,cycle82_5]⟩
lemma valid_data82 : data82.Valid src82 dst82 Finset.univ := by decide +kernel

def src83 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,13,22,6,15,7,14,22]
def dst83 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle83_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,4]⟩
def cycle83_1 : CycleData E W := ⟨2,![11,6,16,2],![5,12,15,7]⟩
def cycle83_2 : CycleData E W := ⟨2,![12,7,15,3],![5,13,15,6]⟩
def cycle83_3 : CycleData E W := ⟨3,![5,10,14,19,4],![2,12,4,22,6]⟩
def cycle83_4 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data83 : PartitionData E W := ⟨5,![cycle83_0,cycle83_1,cycle83_2,cycle83_3,cycle83_4]⟩
lemma valid_data83 : data83.Valid src83 dst83 Finset.univ := by decide +kernel

def src84 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,22,13,6,14,7,15,22]
def dst84 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle84_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle84_1 : CycleData E W := ⟨2,![14,8,16,1],![4,13,14,7]⟩
def cycle84_2 : CycleData E W := ⟨2,![11,6,17,2],![5,12,15,7]⟩
def cycle84_3 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle84_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle84_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data84 : PartitionData E W := ⟨6,![cycle84_0,cycle84_1,cycle84_2,cycle84_3,cycle84_4,cycle84_5]⟩
lemma valid_data84 : data84.Valid src84 dst84 Finset.univ := by decide +kernel

def src85 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,22,13,6,14,7,22,15]
def dst85 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle85_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle85_1 : CycleData E W := ⟨2,![14,8,16,1],![4,13,14,7]⟩
def cycle85_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle85_3 : CycleData E W := ⟨2,![11,6,19,3],![5,12,15,6]⟩
def cycle85_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle85_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data85 : PartitionData E W := ⟨6,![cycle85_0,cycle85_1,cycle85_2,cycle85_3,cycle85_4,cycle85_5]⟩
lemma valid_data85 : data85.Valid src85 dst85 Finset.univ := by decide +kernel

def src86 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,22,13,6,14,22,7,15]
def dst86 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle86_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle86_1 : CycleData E W := ⟨2,![14,7,18,1],![4,13,15,7]⟩
def cycle86_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle86_3 : CycleData E W := ⟨2,![11,6,19,3],![5,12,15,6]⟩
def cycle86_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle86_5 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data86 : PartitionData E W := ⟨6,![cycle86_0,cycle86_1,cycle86_2,cycle86_3,cycle86_4,cycle86_5]⟩
lemma valid_data86 : data86.Valid src86 dst86 Finset.univ := by decide +kernel

def src87 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,5,22,13,6,15,7,14,22]
def dst87 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle87_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,12,5,7,4]⟩
def cycle87_1 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle87_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,14,7,15,6]⟩
def cycle87_3 : CycleData E W := ⟨2,![14,7,6,10],![4,13,15,12]⟩
def cycle87_4 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data87 : PartitionData E W := ⟨5,![cycle87_0,cycle87_1,cycle87_2,cycle87_3,cycle87_4]⟩
lemma valid_data87 : data87.Valid src87 dst87 Finset.univ := by decide +kernel

def src88 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,22,5,13,6,14,7,15,22]
def dst88 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle88_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle88_1 : CycleData E W := ⟨2,![14,13,2,1],![4,13,5,7]⟩
def cycle88_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle88_3 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle88_4 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle88_5 : CycleData E W := ⟨2,![17,7,8,16],![7,15,13,14]⟩
def data88 : PartitionData E W := ⟨6,![cycle88_0,cycle88_1,cycle88_2,cycle88_3,cycle88_4,cycle88_5]⟩
lemma valid_data88 : data88.Valid src88 dst88 Finset.univ := by decide +kernel

def src89 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,22,5,13,6,14,7,22,15]
def dst89 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle89_0 : CycleData E W := ⟨1,![5,10,0],![2,12,4]⟩
def cycle89_1 : CycleData E W := ⟨2,![14,8,16,1],![4,13,14,7]⟩
def cycle89_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle89_3 : CycleData E W := ⟨2,![13,7,19,3],![5,13,15,6]⟩
def cycle89_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle89_5 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def data89 : PartitionData E W := ⟨6,![cycle89_0,cycle89_1,cycle89_2,cycle89_3,cycle89_4,cycle89_5]⟩
lemma valid_data89 : data89.Valid src89 dst89 Finset.univ := by decide +kernel

def src90 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,22,5,13,6,14,22,7,15]
def dst90 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle90_0 : CycleData E W := ⟨3,![5,11,17,1,0],![2,12,22,7,4]⟩
def cycle90_1 : CycleData E W := ⟨2,![3,19,18,2],![5,6,15,7]⟩
def cycle90_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle90_3 : CycleData E W := ⟨2,![14,7,6,10],![4,13,15,12]⟩
def cycle90_4 : CycleData E W := ⟨2,![13,8,16,12],![5,13,14,22]⟩
def data90 : PartitionData E W := ⟨5,![cycle90_0,cycle90_1,cycle90_2,cycle90_3,cycle90_4]⟩
lemma valid_data90 : data90.Valid src90 dst90 Finset.univ := by decide +kernel

def src91 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,12,22,5,13,6,15,7,14,22]
def dst91 : E → W := ![4,7,5,6,2,12,15,13,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle91_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,15,7,4]⟩
def cycle91_1 : CycleData E W := ⟨2,![13,8,17,2],![5,13,14,7]⟩
def cycle91_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle91_3 : CycleData E W := ⟨2,![9,18,11,5],![2,14,22,12]⟩
def cycle91_4 : CycleData E W := ⟨2,![14,7,6,10],![4,13,15,12]⟩
def data91 : PartitionData E W := ⟨5,![cycle91_0,cycle91_1,cycle91_2,cycle91_3,cycle91_4]⟩
lemma valid_data91 : data91.Valid src91 dst91 Finset.univ := by decide +kernel

def src92 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,13,5,12,22,6,14,7,15,22]
def dst92 : E → W := ![4,7,5,6,2,12,15,13,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle92_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle92_1 : CycleData E W := ⟨3,![14,19,3,11,10],![4,22,6,5,13]⟩
def cycle92_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle92_3 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def cycle92_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,13,14]⟩
def data92 : PartitionData E W := ⟨5,![cycle92_0,cycle92_1,cycle92_2,cycle92_3,cycle92_4]⟩
lemma valid_data92 : data92.Valid src92 dst92 Finset.univ := by decide +kernel

def src93 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,13,5,12,22,6,14,7,22,15]
def dst93 : E → W := ![4,7,5,6,2,12,15,13,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle93_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle93_1 : CycleData E W := ⟨2,![11,7,19,3],![5,13,15,6]⟩
def cycle93_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle93_3 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def cycle93_4 : CycleData E W := ⟨3,![14,17,16,8,10],![4,22,7,14,13]⟩
def data93 : PartitionData E W := ⟨5,![cycle93_0,cycle93_1,cycle93_2,cycle93_3,cycle93_4]⟩
lemma valid_data93 : data93.Valid src93 dst93 Finset.univ := by decide +kernel

def src94 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,13,5,12,22,6,14,22,7,15]
def dst94 : E → W := ![4,7,5,6,2,12,15,13,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle94_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,12,5,7,4]⟩
def cycle94_1 : CycleData E W := ⟨2,![11,7,19,3],![5,13,15,6]⟩
def cycle94_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle94_3 : CycleData E W := ⟨2,![18,6,13,17],![7,15,12,22]⟩
def cycle94_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,13]⟩
def data94 : PartitionData E W := ⟨5,![cycle94_0,cycle94_1,cycle94_2,cycle94_3,cycle94_4]⟩
lemma valid_data94 : data94.Valid src94 dst94 Finset.univ := by decide +kernel

def src95 : E → W := ![2,4,7,5,6,2,12,15,13,14,4,13,5,12,22,6,15,7,14,22]
def dst95 : E → W := ![4,7,5,6,2,12,15,13,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle95_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,4]⟩
def cycle95_1 : CycleData E W := ⟨2,![12,6,16,2],![5,12,15,7]⟩
def cycle95_2 : CycleData E W := ⟨2,![11,7,15,3],![5,13,15,6]⟩
def cycle95_3 : CycleData E W := ⟨2,![5,13,19,4],![2,12,22,6]⟩
def cycle95_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,14,13]⟩
def data95 : PartitionData E W := ⟨5,![cycle95_0,cycle95_1,cycle95_2,cycle95_3,cycle95_4]⟩
lemma valid_data95 : data95.Valid src95 dst95 Finset.univ := by decide +kernel

def src96 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,13,22,6,14,7,15,22]
def dst96 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle96_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,4]⟩
def cycle96_1 : CycleData E W := ⟨2,![12,6,16,2],![5,13,14,7]⟩
def cycle96_2 : CycleData E W := ⟨2,![11,7,15,3],![5,12,14,6]⟩
def cycle96_3 : CycleData E W := ⟨2,![5,13,19,4],![2,13,22,6]⟩
def cycle96_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,12]⟩
def data96 : PartitionData E W := ⟨5,![cycle96_0,cycle96_1,cycle96_2,cycle96_3,cycle96_4]⟩
lemma valid_data96 : data96.Valid src96 dst96 Finset.univ := by decide +kernel

def src97 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,13,22,6,14,7,22,15]
def dst97 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle97_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle97_1 : CycleData E W := ⟨2,![11,7,15,3],![5,12,14,6]⟩
def cycle97_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle97_3 : CycleData E W := ⟨2,![17,13,6,16],![7,22,13,14]⟩
def cycle97_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,15,12]⟩
def data97 : PartitionData E W := ⟨5,![cycle97_0,cycle97_1,cycle97_2,cycle97_3,cycle97_4]⟩
lemma valid_data97 : data97.Valid src97 dst97 Finset.univ := by decide +kernel

def src98 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,13,22,6,14,22,7,15]
def dst98 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle98_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle98_1 : CycleData E W := ⟨2,![11,7,15,3],![5,12,14,6]⟩
def cycle98_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle98_3 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def cycle98_4 : CycleData E W := ⟨3,![14,17,18,8,10],![4,22,7,15,12]⟩
def data98 : PartitionData E W := ⟨5,![cycle98_0,cycle98_1,cycle98_2,cycle98_3,cycle98_4]⟩
lemma valid_data98 : data98.Valid src98 dst98 Finset.univ := by decide +kernel

def src99 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,13,22,6,15,7,14,22]
def dst99 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle99_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle99_1 : CycleData E W := ⟨3,![14,19,3,11,10],![4,22,6,5,12]⟩
def cycle99_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle99_3 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def cycle99_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,12,15]⟩
def data99 : PartitionData E W := ⟨5,![cycle99_0,cycle99_1,cycle99_2,cycle99_3,cycle99_4]⟩
lemma valid_data99 : data99.Valid src99 dst99 Finset.univ := by decide +kernel

def src100 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,22,13,6,14,7,15,22]
def dst100 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle100_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,14,7,4]⟩
def cycle100_1 : CycleData E W := ⟨2,![11,8,17,2],![5,12,15,7]⟩
def cycle100_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle100_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,13]⟩
def cycle100_4 : CycleData E W := ⟨2,![14,6,7,10],![4,13,14,12]⟩
def data100 : PartitionData E W := ⟨5,![cycle100_0,cycle100_1,cycle100_2,cycle100_3,cycle100_4]⟩
lemma valid_data100 : data100.Valid src100 dst100 Finset.univ := by decide +kernel

def src101 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,22,13,6,14,7,22,15]
def dst101 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle101_0 : CycleData E W := ⟨3,![5,6,16,1,0],![2,13,14,7,4]⟩
def cycle101_1 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle101_2 : CycleData E W := ⟨2,![11,7,15,3],![5,12,14,6]⟩
def cycle101_3 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle101_4 : CycleData E W := ⟨3,![14,13,18,8,10],![4,13,22,15,12]⟩
def data101 : PartitionData E W := ⟨5,![cycle101_0,cycle101_1,cycle101_2,cycle101_3,cycle101_4]⟩
lemma valid_data101 : data101.Valid src101 dst101 Finset.univ := by decide +kernel

def src102 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,22,13,6,14,22,7,15]
def dst102 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle102_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle102_1 : CycleData E W := ⟨2,![10,8,18,1],![4,12,15,7]⟩
def cycle102_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle102_3 : CycleData E W := ⟨2,![11,7,15,3],![5,12,14,6]⟩
def cycle102_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle102_5 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def data102 : PartitionData E W := ⟨6,![cycle102_0,cycle102_1,cycle102_2,cycle102_3,cycle102_4,cycle102_5]⟩
lemma valid_data102 : data102.Valid src102 dst102 Finset.univ := by decide +kernel

def src103 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,5,22,13,6,15,7,14,22]
def dst103 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle103_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle103_1 : CycleData E W := ⟨2,![10,11,2,1],![4,12,5,7]⟩
def cycle103_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle103_3 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle103_4 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def cycle103_5 : CycleData E W := ⟨2,![17,7,8,16],![7,14,12,15]⟩
def data103 : PartitionData E W := ⟨6,![cycle103_0,cycle103_1,cycle103_2,cycle103_3,cycle103_4,cycle103_5]⟩
lemma valid_data103 : data103.Valid src103 dst103 Finset.univ := by decide +kernel

def src104 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,22,5,13,6,14,7,15,22]
def dst104 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle104_0 : CycleData E W := ⟨3,![5,13,2,1,0],![2,13,5,7,4]⟩
def cycle104_1 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle104_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,15,7,14,6]⟩
def cycle104_3 : CycleData E W := ⟨2,![14,6,7,10],![4,13,14,12]⟩
def cycle104_4 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data104 : PartitionData E W := ⟨5,![cycle104_0,cycle104_1,cycle104_2,cycle104_3,cycle104_4]⟩
lemma valid_data104 : data104.Valid src104 dst104 Finset.univ := by decide +kernel

def src105 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,22,5,13,6,14,7,22,15]
def dst105 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle105_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle105_1 : CycleData E W := ⟨2,![10,7,16,1],![4,12,14,7]⟩
def cycle105_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle105_3 : CycleData E W := ⟨2,![13,6,15,3],![5,13,14,6]⟩
def cycle105_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle105_5 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data105 : PartitionData E W := ⟨6,![cycle105_0,cycle105_1,cycle105_2,cycle105_3,cycle105_4,cycle105_5]⟩
lemma valid_data105 : data105.Valid src105 dst105 Finset.univ := by decide +kernel

def src106 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,22,5,13,6,14,22,7,15]
def dst106 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle106_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle106_1 : CycleData E W := ⟨2,![10,8,18,1],![4,12,15,7]⟩
def cycle106_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle106_3 : CycleData E W := ⟨2,![13,6,15,3],![5,13,14,6]⟩
def cycle106_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle106_5 : CycleData E W := ⟨1,![11,16,7],![12,22,14]⟩
def data106 : PartitionData E W := ⟨6,![cycle106_0,cycle106_1,cycle106_2,cycle106_3,cycle106_4,cycle106_5]⟩
lemma valid_data106 : data106.Valid src106 dst106 Finset.univ := by decide +kernel

def src107 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,12,22,5,13,6,15,7,14,22]
def dst107 : E → W := ![4,7,5,6,2,13,14,12,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle107_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle107_1 : CycleData E W := ⟨2,![10,8,16,1],![4,12,15,7]⟩
def cycle107_2 : CycleData E W := ⟨2,![13,6,17,2],![5,13,14,7]⟩
def cycle107_3 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle107_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle107_5 : CycleData E W := ⟨1,![11,18,7],![12,22,14]⟩
def data107 : PartitionData E W := ⟨6,![cycle107_0,cycle107_1,cycle107_2,cycle107_3,cycle107_4,cycle107_5]⟩
lemma valid_data107 : data107.Valid src107 dst107 Finset.univ := by decide +kernel

def src108 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,13,5,12,22,6,14,7,15,22]
def dst108 : E → W := ![4,7,5,6,2,13,14,12,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle108_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,4]⟩
def cycle108_1 : CycleData E W := ⟨2,![11,6,16,2],![5,13,14,7]⟩
def cycle108_2 : CycleData E W := ⟨2,![12,7,15,3],![5,12,14,6]⟩
def cycle108_3 : CycleData E W := ⟨3,![5,10,14,19,4],![2,13,4,22,6]⟩
def cycle108_4 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data108 : PartitionData E W := ⟨5,![cycle108_0,cycle108_1,cycle108_2,cycle108_3,cycle108_4]⟩
lemma valid_data108 : data108.Valid src108 dst108 Finset.univ := by decide +kernel

def src109 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,13,5,12,22,6,14,7,22,15]
def dst109 : E → W := ![4,7,5,6,2,13,14,12,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle109_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle109_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle109_2 : CycleData E W := ⟨2,![11,6,16,2],![5,13,14,7]⟩
def cycle109_3 : CycleData E W := ⟨2,![12,7,15,3],![5,12,14,6]⟩
def cycle109_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle109_5 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data109 : PartitionData E W := ⟨6,![cycle109_0,cycle109_1,cycle109_2,cycle109_3,cycle109_4,cycle109_5]⟩
lemma valid_data109 : data109.Valid src109 dst109 Finset.univ := by decide +kernel

def src110 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,13,5,12,22,6,14,22,7,15]
def dst110 : E → W := ![4,7,5,6,2,13,14,12,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle110_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle110_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle110_2 : CycleData E W := ⟨2,![12,8,18,2],![5,12,15,7]⟩
def cycle110_3 : CycleData E W := ⟨2,![11,6,15,3],![5,13,14,6]⟩
def cycle110_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle110_5 : CycleData E W := ⟨1,![13,16,7],![12,22,14]⟩
def data110 : PartitionData E W := ⟨6,![cycle110_0,cycle110_1,cycle110_2,cycle110_3,cycle110_4,cycle110_5]⟩
lemma valid_data110 : data110.Valid src110 dst110 Finset.univ := by decide +kernel

def src111 : E → W := ![2,4,7,5,6,2,13,14,12,15,4,13,5,12,22,6,15,7,14,22]
def dst111 : E → W := ![4,7,5,6,2,13,14,12,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle111_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,13,5,7,4]⟩
def cycle111_1 : CycleData E W := ⟨2,![12,13,19,3],![5,12,22,6]⟩
def cycle111_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle111_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,14,13]⟩
def cycle111_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,12,15]⟩
def data111 : PartitionData E W := ⟨5,![cycle111_0,cycle111_1,cycle111_2,cycle111_3,cycle111_4]⟩
lemma valid_data111 : data111.Valid src111 dst111 Finset.univ := by decide +kernel

def src112 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,13,22,6,14,7,15,22]
def dst112 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle112_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle112_1 : CycleData E W := ⟨3,![14,19,3,11,10],![4,22,6,5,12]⟩
def cycle112_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle112_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle112_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,12,14]⟩
def data112 : PartitionData E W := ⟨5,![cycle112_0,cycle112_1,cycle112_2,cycle112_3,cycle112_4]⟩
lemma valid_data112 : data112.Valid src112 dst112 Finset.univ := by decide +kernel

def src113 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,13,22,6,14,7,22,15]
def dst113 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle113_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle113_1 : CycleData E W := ⟨2,![11,7,19,3],![5,12,15,6]⟩
def cycle113_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle113_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle113_4 : CycleData E W := ⟨3,![14,17,16,8,10],![4,22,7,14,12]⟩
def data113 : PartitionData E W := ⟨5,![cycle113_0,cycle113_1,cycle113_2,cycle113_3,cycle113_4]⟩
lemma valid_data113 : data113.Valid src113 dst113 Finset.univ := by decide +kernel

def src114 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,13,22,6,14,22,7,15]
def dst114 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle114_0 : CycleData E W := ⟨3,![5,12,2,1,0],![2,13,5,7,4]⟩
def cycle114_1 : CycleData E W := ⟨2,![11,7,19,3],![5,12,15,6]⟩
def cycle114_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle114_3 : CycleData E W := ⟨2,![18,6,13,17],![7,15,13,22]⟩
def cycle114_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,12]⟩
def data114 : PartitionData E W := ⟨5,![cycle114_0,cycle114_1,cycle114_2,cycle114_3,cycle114_4]⟩
lemma valid_data114 : data114.Valid src114 dst114 Finset.univ := by decide +kernel

def src115 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,13,22,6,15,7,14,22]
def dst115 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle115_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,4]⟩
def cycle115_1 : CycleData E W := ⟨2,![12,6,16,2],![5,13,15,7]⟩
def cycle115_2 : CycleData E W := ⟨2,![11,7,15,3],![5,12,15,6]⟩
def cycle115_3 : CycleData E W := ⟨2,![5,13,19,4],![2,13,22,6]⟩
def cycle115_4 : CycleData E W := ⟨2,![14,18,8,10],![4,22,14,12]⟩
def data115 : PartitionData E W := ⟨5,![cycle115_0,cycle115_1,cycle115_2,cycle115_3,cycle115_4]⟩
lemma valid_data115 : data115.Valid src115 dst115 Finset.univ := by decide +kernel

def src116 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,22,13,6,14,7,15,22]
def dst116 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle116_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle116_1 : CycleData E W := ⟨2,![10,11,2,1],![4,12,5,7]⟩
def cycle116_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle116_3 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle116_4 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle116_5 : CycleData E W := ⟨2,![17,7,8,16],![7,15,12,14]⟩
def data116 : PartitionData E W := ⟨6,![cycle116_0,cycle116_1,cycle116_2,cycle116_3,cycle116_4,cycle116_5]⟩
lemma valid_data116 : data116.Valid src116 dst116 Finset.univ := by decide +kernel

def src117 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,22,13,6,14,7,22,15]
def dst117 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle117_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle117_1 : CycleData E W := ⟨2,![10,8,16,1],![4,12,14,7]⟩
def cycle117_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle117_3 : CycleData E W := ⟨2,![11,7,19,3],![5,12,15,6]⟩
def cycle117_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle117_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data117 : PartitionData E W := ⟨6,![cycle117_0,cycle117_1,cycle117_2,cycle117_3,cycle117_4,cycle117_5]⟩
lemma valid_data117 : data117.Valid src117 dst117 Finset.univ := by decide +kernel

def src118 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,22,13,6,14,22,7,15]
def dst118 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle118_0 : CycleData E W := ⟨3,![5,13,17,1,0],![2,13,22,7,4]⟩
def cycle118_1 : CycleData E W := ⟨2,![3,19,18,2],![5,6,15,7]⟩
def cycle118_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle118_3 : CycleData E W := ⟨2,![14,6,7,10],![4,13,15,12]⟩
def cycle118_4 : CycleData E W := ⟨2,![12,16,8,11],![5,22,14,12]⟩
def data118 : PartitionData E W := ⟨5,![cycle118_0,cycle118_1,cycle118_2,cycle118_3,cycle118_4]⟩
lemma valid_data118 : data118.Valid src118 dst118 Finset.univ := by decide +kernel

def src119 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,5,22,13,6,15,7,14,22]
def dst119 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle119_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,15,7,4]⟩
def cycle119_1 : CycleData E W := ⟨2,![11,8,17,2],![5,12,14,7]⟩
def cycle119_2 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle119_3 : CycleData E W := ⟨2,![9,18,13,5],![2,14,22,13]⟩
def cycle119_4 : CycleData E W := ⟨2,![14,6,7,10],![4,13,15,12]⟩
def data119 : PartitionData E W := ⟨5,![cycle119_0,cycle119_1,cycle119_2,cycle119_3,cycle119_4]⟩
lemma valid_data119 : data119.Valid src119 dst119 Finset.univ := by decide +kernel

def src120 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,22,5,13,6,14,7,15,22]
def dst120 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle120_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle120_1 : CycleData E W := ⟨2,![10,8,16,1],![4,12,14,7]⟩
def cycle120_2 : CycleData E W := ⟨2,![13,6,17,2],![5,13,15,7]⟩
def cycle120_3 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle120_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle120_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data120 : PartitionData E W := ⟨6,![cycle120_0,cycle120_1,cycle120_2,cycle120_3,cycle120_4,cycle120_5]⟩
lemma valid_data120 : data120.Valid src120 dst120 Finset.univ := by decide +kernel

def src121 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,22,5,13,6,14,7,22,15]
def dst121 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle121_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle121_1 : CycleData E W := ⟨2,![10,8,16,1],![4,12,14,7]⟩
def cycle121_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle121_3 : CycleData E W := ⟨2,![13,6,19,3],![5,13,15,6]⟩
def cycle121_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle121_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data121 : PartitionData E W := ⟨6,![cycle121_0,cycle121_1,cycle121_2,cycle121_3,cycle121_4,cycle121_5]⟩
lemma valid_data121 : data121.Valid src121 dst121 Finset.univ := by decide +kernel

def src122 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,22,5,13,6,14,22,7,15]
def dst122 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle122_0 : CycleData E W := ⟨1,![5,14,0],![2,13,4]⟩
def cycle122_1 : CycleData E W := ⟨2,![10,7,18,1],![4,12,15,7]⟩
def cycle122_2 : CycleData E W := ⟨1,![12,17,2],![5,22,7]⟩
def cycle122_3 : CycleData E W := ⟨2,![13,6,19,3],![5,13,15,6]⟩
def cycle122_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle122_5 : CycleData E W := ⟨1,![11,16,8],![12,22,14]⟩
def data122 : PartitionData E W := ⟨6,![cycle122_0,cycle122_1,cycle122_2,cycle122_3,cycle122_4,cycle122_5]⟩
lemma valid_data122 : data122.Valid src122 dst122 Finset.univ := by decide +kernel

def src123 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,12,22,5,13,6,15,7,14,22]
def dst123 : E → W := ![4,7,5,6,2,13,15,12,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle123_0 : CycleData E W := ⟨3,![5,13,2,1,0],![2,13,5,7,4]⟩
def cycle123_1 : CycleData E W := ⟨1,![12,19,3],![5,22,6]⟩
def cycle123_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,14,7,15,6]⟩
def cycle123_3 : CycleData E W := ⟨2,![14,6,7,10],![4,13,15,12]⟩
def cycle123_4 : CycleData E W := ⟨1,![11,18,8],![12,22,14]⟩
def data123 : PartitionData E W := ⟨5,![cycle123_0,cycle123_1,cycle123_2,cycle123_3,cycle123_4]⟩
lemma valid_data123 : data123.Valid src123 dst123 Finset.univ := by decide +kernel

def src124 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,13,5,12,22,6,14,7,15,22]
def dst124 : E → W := ![4,7,5,6,2,13,15,12,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle124_0 : CycleData E W := ⟨3,![5,11,2,1,0],![2,13,5,7,4]⟩
def cycle124_1 : CycleData E W := ⟨2,![12,13,19,3],![5,12,22,6]⟩
def cycle124_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle124_3 : CycleData E W := ⟨2,![14,18,6,10],![4,22,15,13]⟩
def cycle124_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,12,14]⟩
def data124 : PartitionData E W := ⟨5,![cycle124_0,cycle124_1,cycle124_2,cycle124_3,cycle124_4]⟩
lemma valid_data124 : data124.Valid src124 dst124 Finset.univ := by decide +kernel

def src125 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,13,5,12,22,6,14,7,22,15]
def dst125 : E → W := ![4,7,5,6,2,13,15,12,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle125_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle125_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle125_2 : CycleData E W := ⟨2,![12,8,16,2],![5,12,14,7]⟩
def cycle125_3 : CycleData E W := ⟨2,![11,6,19,3],![5,13,15,6]⟩
def cycle125_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle125_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data125 : PartitionData E W := ⟨6,![cycle125_0,cycle125_1,cycle125_2,cycle125_3,cycle125_4,cycle125_5]⟩
lemma valid_data125 : data125.Valid src125 dst125 Finset.univ := by decide +kernel

def src126 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,13,5,12,22,6,14,22,7,15]
def dst126 : E → W := ![4,7,5,6,2,13,15,12,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle126_0 : CycleData E W := ⟨1,![5,10,0],![2,13,4]⟩
def cycle126_1 : CycleData E W := ⟨1,![14,17,1],![4,22,7]⟩
def cycle126_2 : CycleData E W := ⟨2,![11,6,18,2],![5,13,15,7]⟩
def cycle126_3 : CycleData E W := ⟨2,![12,7,19,3],![5,12,15,6]⟩
def cycle126_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle126_5 : CycleData E W := ⟨1,![13,16,8],![12,22,14]⟩
def data126 : PartitionData E W := ⟨6,![cycle126_0,cycle126_1,cycle126_2,cycle126_3,cycle126_4,cycle126_5]⟩
lemma valid_data126 : data126.Valid src126 dst126 Finset.univ := by decide +kernel

def src127 : E → W := ![2,4,7,5,6,2,13,15,12,14,4,13,5,12,22,6,15,7,14,22]
def dst127 : E → W := ![4,7,5,6,2,13,15,12,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle127_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,4]⟩
def cycle127_1 : CycleData E W := ⟨2,![11,6,16,2],![5,13,15,7]⟩
def cycle127_2 : CycleData E W := ⟨2,![12,7,15,3],![5,12,15,6]⟩
def cycle127_3 : CycleData E W := ⟨3,![5,10,14,19,4],![2,13,4,22,6]⟩
def cycle127_4 : CycleData E W := ⟨1,![13,18,8],![12,22,14]⟩
def data127 : PartitionData E W := ⟨5,![cycle127_0,cycle127_1,cycle127_2,cycle127_3,cycle127_4]⟩
lemma valid_data127 : data127.Valid src127 dst127 Finset.univ := by decide +kernel

def src128 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,13,22,6,14,7,15,22]
def dst128 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle128_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle128_1 : CycleData E W := ⟨2,![12,7,15,1],![5,13,14,6]⟩
def cycle128_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle128_3 : CycleData E W := ⟨2,![10,6,16,3],![4,12,14,7]⟩
def cycle128_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle128_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data128 : PartitionData E W := ⟨6,![cycle128_0,cycle128_1,cycle128_2,cycle128_3,cycle128_4,cycle128_5]⟩
lemma valid_data128 : data128.Valid src128 dst128 Finset.univ := by decide +kernel

def src129 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,13,22,6,14,7,22,15]
def dst129 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle129_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle129_1 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle129_2 : CycleData E W := ⟨3,![9,19,15,16,4],![2,15,6,14,7]⟩
def cycle129_3 : CycleData E W := ⟨2,![12,7,6,11],![5,13,14,12]⟩
def cycle129_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data129 : PartitionData E W := ⟨5,![cycle129_0,cycle129_1,cycle129_2,cycle129_3,cycle129_4]⟩
lemma valid_data129 : data129.Valid src129 dst129 Finset.univ := by decide +kernel

def src130 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,13,22,6,14,22,7,15]
def dst130 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle130_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle130_1 : CycleData E W := ⟨2,![12,8,19,1],![5,13,15,6]⟩
def cycle130_2 : CycleData E W := ⟨2,![10,6,15,2],![4,12,14,6]⟩
def cycle130_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle130_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle130_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data130 : PartitionData E W := ⟨6,![cycle130_0,cycle130_1,cycle130_2,cycle130_3,cycle130_4,cycle130_5]⟩
lemma valid_data130 : data130.Valid src130 dst130 Finset.univ := by decide +kernel

def src131 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,13,22,6,15,7,14,22]
def dst131 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle131_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle131_1 : CycleData E W := ⟨2,![12,8,15,1],![5,13,15,6]⟩
def cycle131_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle131_3 : CycleData E W := ⟨2,![10,6,17,3],![4,12,14,7]⟩
def cycle131_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle131_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data131 : PartitionData E W := ⟨6,![cycle131_0,cycle131_1,cycle131_2,cycle131_3,cycle131_4,cycle131_5]⟩
lemma valid_data131 : data131.Valid src131 dst131 Finset.univ := by decide +kernel

def src132 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,22,13,6,14,7,15,22]
def dst132 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle132_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle132_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle132_2 : CycleData E W := ⟨2,![10,6,15,2],![4,12,14,6]⟩
def cycle132_3 : CycleData E W := ⟨2,![14,7,16,3],![4,13,14,7]⟩
def cycle132_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle132_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data132 : PartitionData E W := ⟨6,![cycle132_0,cycle132_1,cycle132_2,cycle132_3,cycle132_4,cycle132_5]⟩
lemma valid_data132 : data132.Valid src132 dst132 Finset.univ := by decide +kernel

def src133 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,22,13,6,14,7,22,15]
def dst133 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle133_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,5]⟩
def cycle133_1 : CycleData E W := ⟨2,![10,6,15,2],![4,12,14,6]⟩
def cycle133_2 : CycleData E W := ⟨2,![14,7,16,3],![4,13,14,7]⟩
def cycle133_3 : CycleData E W := ⟨3,![5,11,12,17,4],![2,12,5,22,7]⟩
def cycle133_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data133 : PartitionData E W := ⟨5,![cycle133_0,cycle133_1,cycle133_2,cycle133_3,cycle133_4]⟩
lemma valid_data133 : data133.Valid src133 dst133 Finset.univ := by decide +kernel

def src134 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,22,13,6,14,22,7,15]
def dst134 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle134_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle134_1 : CycleData E W := ⟨2,![14,13,17,3],![4,13,22,7]⟩
def cycle134_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle134_3 : CycleData E W := ⟨2,![12,16,6,11],![5,22,14,12]⟩
def cycle134_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,13,14]⟩
def data134 : PartitionData E W := ⟨5,![cycle134_0,cycle134_1,cycle134_2,cycle134_3,cycle134_4]⟩
lemma valid_data134 : data134.Valid src134 dst134 Finset.univ := by decide +kernel

def src135 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,5,22,13,6,15,7,14,22]
def dst135 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle135_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle135_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle135_2 : CycleData E W := ⟨2,![14,8,15,2],![4,13,15,6]⟩
def cycle135_3 : CycleData E W := ⟨2,![10,6,17,3],![4,12,14,7]⟩
def cycle135_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle135_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data135 : PartitionData E W := ⟨6,![cycle135_0,cycle135_1,cycle135_2,cycle135_3,cycle135_4,cycle135_5]⟩
lemma valid_data135 : data135.Valid src135 dst135 Finset.univ := by decide +kernel

def src136 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,22,5,13,6,14,7,15,22]
def dst136 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle136_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle136_1 : CycleData E W := ⟨2,![14,7,16,3],![4,13,14,7]⟩
def cycle136_2 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle136_3 : CycleData E W := ⟨2,![19,11,6,15],![6,22,12,14]⟩
def cycle136_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,15,22]⟩
def data136 : PartitionData E W := ⟨5,![cycle136_0,cycle136_1,cycle136_2,cycle136_3,cycle136_4]⟩
lemma valid_data136 : data136.Valid src136 dst136 Finset.univ := by decide +kernel

def src137 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,22,5,13,6,14,7,22,15]
def dst137 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle137_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,5]⟩
def cycle137_1 : CycleData E W := ⟨2,![10,6,15,2],![4,12,14,6]⟩
def cycle137_2 : CycleData E W := ⟨2,![14,7,16,3],![4,13,14,7]⟩
def cycle137_3 : CycleData E W := ⟨2,![5,11,17,4],![2,12,22,7]⟩
def cycle137_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,15,22]⟩
def data137 : PartitionData E W := ⟨5,![cycle137_0,cycle137_1,cycle137_2,cycle137_3,cycle137_4]⟩
lemma valid_data137 : data137.Valid src137 dst137 Finset.univ := by decide +kernel

def src138 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,22,5,13,6,14,22,7,15]
def dst138 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle138_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle138_1 : CycleData E W := ⟨3,![14,13,12,17,3],![4,13,5,22,7]⟩
def cycle138_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle138_3 : CycleData E W := ⟨1,![11,16,6],![12,22,14]⟩
def cycle138_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,13,14]⟩
def data138 : PartitionData E W := ⟨5,![cycle138_0,cycle138_1,cycle138_2,cycle138_3,cycle138_4]⟩
lemma valid_data138 : data138.Valid src138 dst138 Finset.univ := by decide +kernel

def src139 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,12,22,5,13,6,15,7,14,22]
def dst139 : E → W := ![5,6,4,7,2,12,14,13,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle139_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle139_1 : CycleData E W := ⟨2,![14,7,17,3],![4,13,14,7]⟩
def cycle139_2 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle139_3 : CycleData E W := ⟨1,![11,18,6],![12,22,14]⟩
def cycle139_4 : CycleData E W := ⟨3,![13,8,15,19,12],![5,13,15,6,22]⟩
def data139 : PartitionData E W := ⟨5,![cycle139_0,cycle139_1,cycle139_2,cycle139_3,cycle139_4]⟩
lemma valid_data139 : data139.Valid src139 dst139 Finset.univ := by decide +kernel

def src140 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,13,5,12,22,6,14,7,15,22]
def dst140 : E → W := ![5,6,4,7,2,12,14,13,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle140_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,12,14,6,5]⟩
def cycle140_1 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle140_2 : CycleData E W := ⟨2,![10,7,16,3],![4,13,14,7]⟩
def cycle140_3 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle140_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,12,22,15,13]⟩
def data140 : PartitionData E W := ⟨5,![cycle140_0,cycle140_1,cycle140_2,cycle140_3,cycle140_4]⟩
lemma valid_data140 : data140.Valid src140 dst140 Finset.univ := by decide +kernel

def src141 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,13,5,12,22,6,14,7,22,15]
def dst141 : E → W := ![5,6,4,7,2,12,14,13,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle141_0 : CycleData E W := ⟨3,![4,16,15,1,0],![2,7,14,6,5]⟩
def cycle141_1 : CycleData E W := ⟨2,![10,8,19,2],![4,13,15,6]⟩
def cycle141_2 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle141_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,12]⟩
def cycle141_4 : CycleData E W := ⟨2,![12,6,7,11],![5,12,14,13]⟩
def data141 : PartitionData E W := ⟨5,![cycle141_0,cycle141_1,cycle141_2,cycle141_3,cycle141_4]⟩
lemma valid_data141 : data141.Valid src141 dst141 Finset.univ := by decide +kernel

def src142 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,13,5,12,22,6,14,22,7,15]
def dst142 : E → W := ![5,6,4,7,2,12,14,13,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle142_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle142_1 : CycleData E W := ⟨2,![11,7,15,1],![5,13,14,6]⟩
def cycle142_2 : CycleData E W := ⟨2,![10,8,19,2],![4,13,15,6]⟩
def cycle142_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle142_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle142_5 : CycleData E W := ⟨1,![13,16,6],![12,22,14]⟩
def data142 : PartitionData E W := ⟨6,![cycle142_0,cycle142_1,cycle142_2,cycle142_3,cycle142_4,cycle142_5]⟩
lemma valid_data142 : data142.Valid src142 dst142 Finset.univ := by decide +kernel

def src143 : E → W := ![2,5,6,4,7,2,12,14,13,15,4,13,5,12,22,6,15,7,14,22]
def dst143 : E → W := ![5,6,4,7,2,12,14,13,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle143_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle143_1 : CycleData E W := ⟨2,![11,8,15,1],![5,13,15,6]⟩
def cycle143_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle143_3 : CycleData E W := ⟨2,![10,7,17,3],![4,13,14,7]⟩
def cycle143_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle143_5 : CycleData E W := ⟨1,![13,18,6],![12,22,14]⟩
def data143 : PartitionData E W := ⟨6,![cycle143_0,cycle143_1,cycle143_2,cycle143_3,cycle143_4,cycle143_5]⟩
lemma valid_data143 : data143.Valid src143 dst143 Finset.univ := by decide +kernel

def src144 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,13,22,6,14,7,15,22]
def dst144 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle144_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle144_1 : CycleData E W := ⟨2,![12,8,15,1],![5,13,14,6]⟩
def cycle144_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle144_3 : CycleData E W := ⟨2,![10,6,17,3],![4,12,15,7]⟩
def cycle144_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle144_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data144 : PartitionData E W := ⟨6,![cycle144_0,cycle144_1,cycle144_2,cycle144_3,cycle144_4,cycle144_5]⟩
lemma valid_data144 : data144.Valid src144 dst144 Finset.univ := by decide +kernel

def src145 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,13,22,6,14,7,22,15]
def dst145 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle145_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle145_1 : CycleData E W := ⟨2,![12,8,15,1],![5,13,14,6]⟩
def cycle145_2 : CycleData E W := ⟨2,![10,6,19,2],![4,12,15,6]⟩
def cycle145_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle145_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle145_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data145 : PartitionData E W := ⟨6,![cycle145_0,cycle145_1,cycle145_2,cycle145_3,cycle145_4,cycle145_5]⟩
lemma valid_data145 : data145.Valid src145 dst145 Finset.univ := by decide +kernel

def src146 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,13,22,6,14,22,7,15]
def dst146 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle146_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle146_1 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle146_2 : CycleData E W := ⟨3,![9,15,19,18,4],![2,14,6,15,7]⟩
def cycle146_3 : CycleData E W := ⟨2,![12,7,6,11],![5,13,15,12]⟩
def cycle146_4 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data146 : PartitionData E W := ⟨5,![cycle146_0,cycle146_1,cycle146_2,cycle146_3,cycle146_4]⟩
lemma valid_data146 : data146.Valid src146 dst146 Finset.univ := by decide +kernel

def src147 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,13,22,6,15,7,14,22]
def dst147 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle147_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle147_1 : CycleData E W := ⟨2,![12,7,15,1],![5,13,15,6]⟩
def cycle147_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle147_3 : CycleData E W := ⟨2,![10,6,16,3],![4,12,15,7]⟩
def cycle147_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle147_5 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data147 : PartitionData E W := ⟨6,![cycle147_0,cycle147_1,cycle147_2,cycle147_3,cycle147_4,cycle147_5]⟩
lemma valid_data147 : data147.Valid src147 dst147 Finset.univ := by decide +kernel

def src148 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,22,13,6,14,7,15,22]
def dst148 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle148_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle148_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle148_2 : CycleData E W := ⟨2,![14,8,15,2],![4,13,14,6]⟩
def cycle148_3 : CycleData E W := ⟨2,![10,6,17,3],![4,12,15,7]⟩
def cycle148_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle148_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data148 : PartitionData E W := ⟨6,![cycle148_0,cycle148_1,cycle148_2,cycle148_3,cycle148_4,cycle148_5]⟩
lemma valid_data148 : data148.Valid src148 dst148 Finset.univ := by decide +kernel

def src149 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,22,13,6,14,7,22,15]
def dst149 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle149_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle149_1 : CycleData E W := ⟨2,![14,13,17,3],![4,13,22,7]⟩
def cycle149_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle149_3 : CycleData E W := ⟨2,![12,18,6,11],![5,22,15,12]⟩
def cycle149_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,13,14]⟩
def data149 : PartitionData E W := ⟨5,![cycle149_0,cycle149_1,cycle149_2,cycle149_3,cycle149_4]⟩
lemma valid_data149 : data149.Valid src149 dst149 Finset.univ := by decide +kernel

def src150 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,22,13,6,14,22,7,15]
def dst150 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle150_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle150_1 : CycleData E W := ⟨2,![10,6,19,2],![4,12,15,6]⟩
def cycle150_2 : CycleData E W := ⟨2,![14,7,18,3],![4,13,15,7]⟩
def cycle150_3 : CycleData E W := ⟨3,![5,11,12,17,4],![2,12,5,22,7]⟩
def cycle150_4 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data150 : PartitionData E W := ⟨5,![cycle150_0,cycle150_1,cycle150_2,cycle150_3,cycle150_4]⟩
lemma valid_data150 : data150.Valid src150 dst150 Finset.univ := by decide +kernel

def src151 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,5,22,13,6,15,7,14,22]
def dst151 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle151_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle151_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle151_2 : CycleData E W := ⟨2,![10,6,15,2],![4,12,15,6]⟩
def cycle151_3 : CycleData E W := ⟨2,![14,7,16,3],![4,13,15,7]⟩
def cycle151_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle151_5 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data151 : PartitionData E W := ⟨6,![cycle151_0,cycle151_1,cycle151_2,cycle151_3,cycle151_4,cycle151_5]⟩
lemma valid_data151 : data151.Valid src151 dst151 Finset.univ := by decide +kernel

def src152 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,22,5,13,6,14,7,15,22]
def dst152 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle152_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle152_1 : CycleData E W := ⟨2,![14,7,17,3],![4,13,15,7]⟩
def cycle152_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle152_3 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle152_4 : CycleData E W := ⟨3,![13,8,15,19,12],![5,13,14,6,22]⟩
def data152 : PartitionData E W := ⟨5,![cycle152_0,cycle152_1,cycle152_2,cycle152_3,cycle152_4]⟩
lemma valid_data152 : data152.Valid src152 dst152 Finset.univ := by decide +kernel

def src153 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,22,5,13,6,14,7,22,15]
def dst153 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle153_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle153_1 : CycleData E W := ⟨3,![14,13,12,17,3],![4,13,5,22,7]⟩
def cycle153_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle153_3 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle153_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,13,14]⟩
def data153 : PartitionData E W := ⟨5,![cycle153_0,cycle153_1,cycle153_2,cycle153_3,cycle153_4]⟩
lemma valid_data153 : data153.Valid src153 dst153 Finset.univ := by decide +kernel

def src154 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,22,5,13,6,14,22,7,15]
def dst154 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle154_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle154_1 : CycleData E W := ⟨2,![10,6,19,2],![4,12,15,6]⟩
def cycle154_2 : CycleData E W := ⟨2,![14,7,18,3],![4,13,15,7]⟩
def cycle154_3 : CycleData E W := ⟨2,![5,11,17,4],![2,12,22,7]⟩
def cycle154_4 : CycleData E W := ⟨2,![13,8,16,12],![5,13,14,22]⟩
def data154 : PartitionData E W := ⟨5,![cycle154_0,cycle154_1,cycle154_2,cycle154_3,cycle154_4]⟩
lemma valid_data154 : data154.Valid src154 dst154 Finset.univ := by decide +kernel

def src155 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,12,22,5,13,6,15,7,14,22]
def dst155 : E → W := ![5,6,4,7,2,12,15,13,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle155_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,6,5]⟩
def cycle155_1 : CycleData E W := ⟨2,![14,7,16,3],![4,13,15,7]⟩
def cycle155_2 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle155_3 : CycleData E W := ⟨2,![19,11,6,15],![6,22,12,15]⟩
def cycle155_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,14,22]⟩
def data155 : PartitionData E W := ⟨5,![cycle155_0,cycle155_1,cycle155_2,cycle155_3,cycle155_4]⟩
lemma valid_data155 : data155.Valid src155 dst155 Finset.univ := by decide +kernel

def src156 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,13,5,12,22,6,14,7,15,22]
def dst156 : E → W := ![5,6,4,7,2,12,15,13,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle156_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle156_1 : CycleData E W := ⟨2,![11,8,15,1],![5,13,14,6]⟩
def cycle156_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle156_3 : CycleData E W := ⟨2,![10,7,17,3],![4,13,15,7]⟩
def cycle156_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle156_5 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def data156 : PartitionData E W := ⟨6,![cycle156_0,cycle156_1,cycle156_2,cycle156_3,cycle156_4,cycle156_5]⟩
lemma valid_data156 : data156.Valid src156 dst156 Finset.univ := by decide +kernel

def src157 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,13,5,12,22,6,14,7,22,15]
def dst157 : E → W := ![5,6,4,7,2,12,15,13,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle157_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle157_1 : CycleData E W := ⟨2,![11,8,15,1],![5,13,14,6]⟩
def cycle157_2 : CycleData E W := ⟨2,![10,7,19,2],![4,13,15,6]⟩
def cycle157_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle157_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle157_5 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def data157 : PartitionData E W := ⟨6,![cycle157_0,cycle157_1,cycle157_2,cycle157_3,cycle157_4,cycle157_5]⟩
lemma valid_data157 : data157.Valid src157 dst157 Finset.univ := by decide +kernel

def src158 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,13,5,12,22,6,14,22,7,15]
def dst158 : E → W := ![5,6,4,7,2,12,15,13,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle158_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle158_1 : CycleData E W := ⟨2,![10,7,19,2],![4,13,15,6]⟩
def cycle158_2 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle158_3 : CycleData E W := ⟨2,![5,6,18,4],![2,12,15,7]⟩
def cycle158_4 : CycleData E W := ⟨3,![12,13,16,8,11],![5,12,22,14,13]⟩
def data158 : PartitionData E W := ⟨5,![cycle158_0,cycle158_1,cycle158_2,cycle158_3,cycle158_4]⟩
lemma valid_data158 : data158.Valid src158 dst158 Finset.univ := by decide +kernel

def src159 : E → W := ![2,5,6,4,7,2,12,15,13,14,4,13,5,12,22,6,15,7,14,22]
def dst159 : E → W := ![5,6,4,7,2,12,15,13,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle159_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,12,15,6,5]⟩
def cycle159_1 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle159_2 : CycleData E W := ⟨2,![10,7,16,3],![4,13,15,7]⟩
def cycle159_3 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle159_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,12,22,14,13]⟩
def data159 : PartitionData E W := ⟨5,![cycle159_0,cycle159_1,cycle159_2,cycle159_3,cycle159_4]⟩
lemma valid_data159 : data159.Valid src159 dst159 Finset.univ := by decide +kernel

def src160 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,13,22,6,14,7,15,22]
def dst160 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle160_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,13,14,6,5]⟩
def cycle160_1 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle160_2 : CycleData E W := ⟨2,![10,7,16,3],![4,12,14,7]⟩
def cycle160_3 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle160_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,13,22,15,12]⟩
def data160 : PartitionData E W := ⟨5,![cycle160_0,cycle160_1,cycle160_2,cycle160_3,cycle160_4]⟩
lemma valid_data160 : data160.Valid src160 dst160 Finset.univ := by decide +kernel

def src161 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,13,22,6,14,7,22,15]
def dst161 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle161_0 : CycleData E W := ⟨3,![4,16,15,1,0],![2,7,14,6,5]⟩
def cycle161_1 : CycleData E W := ⟨2,![10,8,19,2],![4,12,15,6]⟩
def cycle161_2 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle161_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,13]⟩
def cycle161_4 : CycleData E W := ⟨2,![12,6,7,11],![5,13,14,12]⟩
def data161 : PartitionData E W := ⟨5,![cycle161_0,cycle161_1,cycle161_2,cycle161_3,cycle161_4]⟩
lemma valid_data161 : data161.Valid src161 dst161 Finset.univ := by decide +kernel

def src162 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,13,22,6,14,22,7,15]
def dst162 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle162_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle162_1 : CycleData E W := ⟨2,![11,7,15,1],![5,12,14,6]⟩
def cycle162_2 : CycleData E W := ⟨2,![10,8,19,2],![4,12,15,6]⟩
def cycle162_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle162_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle162_5 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def data162 : PartitionData E W := ⟨6,![cycle162_0,cycle162_1,cycle162_2,cycle162_3,cycle162_4,cycle162_5]⟩
lemma valid_data162 : data162.Valid src162 dst162 Finset.univ := by decide +kernel

def src163 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,13,22,6,15,7,14,22]
def dst163 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle163_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle163_1 : CycleData E W := ⟨2,![11,8,15,1],![5,12,15,6]⟩
def cycle163_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle163_3 : CycleData E W := ⟨2,![10,7,17,3],![4,12,14,7]⟩
def cycle163_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle163_5 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def data163 : PartitionData E W := ⟨6,![cycle163_0,cycle163_1,cycle163_2,cycle163_3,cycle163_4,cycle163_5]⟩
lemma valid_data163 : data163.Valid src163 dst163 Finset.univ := by decide +kernel

def src164 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,22,13,6,14,7,15,22]
def dst164 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle164_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle164_1 : CycleData E W := ⟨2,![10,7,16,3],![4,12,14,7]⟩
def cycle164_2 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle164_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,13,14]⟩
def cycle164_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,15,12]⟩
def data164 : PartitionData E W := ⟨5,![cycle164_0,cycle164_1,cycle164_2,cycle164_3,cycle164_4]⟩
lemma valid_data164 : data164.Valid src164 dst164 Finset.univ := by decide +kernel

def src165 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,22,13,6,14,7,22,15]
def dst165 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle165_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,5]⟩
def cycle165_1 : CycleData E W := ⟨2,![14,6,15,2],![4,13,14,6]⟩
def cycle165_2 : CycleData E W := ⟨2,![10,7,16,3],![4,12,14,7]⟩
def cycle165_3 : CycleData E W := ⟨2,![5,13,17,4],![2,13,22,7]⟩
def cycle165_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,15,12]⟩
def data165 : PartitionData E W := ⟨5,![cycle165_0,cycle165_1,cycle165_2,cycle165_3,cycle165_4]⟩
lemma valid_data165 : data165.Valid src165 dst165 Finset.univ := by decide +kernel

def src166 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,22,13,6,14,22,7,15]
def dst166 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle166_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle166_1 : CycleData E W := ⟨3,![10,11,12,17,3],![4,12,5,22,7]⟩
def cycle166_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle166_3 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def cycle166_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,12,14]⟩
def data166 : PartitionData E W := ⟨5,![cycle166_0,cycle166_1,cycle166_2,cycle166_3,cycle166_4]⟩
lemma valid_data166 : data166.Valid src166 dst166 Finset.univ := by decide +kernel

def src167 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,5,22,13,6,15,7,14,22]
def dst167 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle167_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle167_1 : CycleData E W := ⟨2,![10,7,17,3],![4,12,14,7]⟩
def cycle167_2 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle167_3 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def cycle167_4 : CycleData E W := ⟨3,![12,19,15,8,11],![5,22,6,15,12]⟩
def data167 : PartitionData E W := ⟨5,![cycle167_0,cycle167_1,cycle167_2,cycle167_3,cycle167_4]⟩
lemma valid_data167 : data167.Valid src167 dst167 Finset.univ := by decide +kernel

def src168 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,22,5,13,6,14,7,15,22]
def dst168 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle168_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle168_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle168_2 : CycleData E W := ⟨2,![14,6,15,2],![4,13,14,6]⟩
def cycle168_3 : CycleData E W := ⟨2,![10,7,16,3],![4,12,14,7]⟩
def cycle168_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle168_5 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data168 : PartitionData E W := ⟨6,![cycle168_0,cycle168_1,cycle168_2,cycle168_3,cycle168_4,cycle168_5]⟩
lemma valid_data168 : data168.Valid src168 dst168 Finset.univ := by decide +kernel

def src169 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,22,5,13,6,14,7,22,15]
def dst169 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle169_0 : CycleData E W := ⟨2,![9,19,1,0],![2,15,6,5]⟩
def cycle169_1 : CycleData E W := ⟨2,![14,6,15,2],![4,13,14,6]⟩
def cycle169_2 : CycleData E W := ⟨2,![10,7,16,3],![4,12,14,7]⟩
def cycle169_3 : CycleData E W := ⟨3,![5,13,12,17,4],![2,13,5,22,7]⟩
def cycle169_4 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data169 : PartitionData E W := ⟨5,![cycle169_0,cycle169_1,cycle169_2,cycle169_3,cycle169_4]⟩
lemma valid_data169 : data169.Valid src169 dst169 Finset.univ := by decide +kernel

def src170 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,22,5,13,6,14,22,7,15]
def dst170 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle170_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle170_1 : CycleData E W := ⟨2,![10,11,17,3],![4,12,22,7]⟩
def cycle170_2 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle170_3 : CycleData E W := ⟨2,![13,6,16,12],![5,13,14,22]⟩
def cycle170_4 : CycleData E W := ⟨2,![19,8,7,15],![6,15,12,14]⟩
def data170 : PartitionData E W := ⟨5,![cycle170_0,cycle170_1,cycle170_2,cycle170_3,cycle170_4]⟩
lemma valid_data170 : data170.Valid src170 dst170 Finset.univ := by decide +kernel

def src171 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,12,22,5,13,6,15,7,14,22]
def dst171 : E → W := ![5,6,4,7,2,13,14,12,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle171_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle171_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle171_2 : CycleData E W := ⟨2,![10,8,15,2],![4,12,15,6]⟩
def cycle171_3 : CycleData E W := ⟨2,![14,6,17,3],![4,13,14,7]⟩
def cycle171_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle171_5 : CycleData E W := ⟨1,![11,18,7],![12,22,14]⟩
def data171 : PartitionData E W := ⟨6,![cycle171_0,cycle171_1,cycle171_2,cycle171_3,cycle171_4,cycle171_5]⟩
lemma valid_data171 : data171.Valid src171 dst171 Finset.univ := by decide +kernel

def src172 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,13,5,12,22,6,14,7,15,22]
def dst172 : E → W := ![5,6,4,7,2,13,14,12,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle172_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle172_1 : CycleData E W := ⟨2,![12,7,15,1],![5,12,14,6]⟩
def cycle172_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle172_3 : CycleData E W := ⟨2,![10,6,16,3],![4,13,14,7]⟩
def cycle172_4 : CycleData E W := ⟨1,![9,17,4],![2,15,7]⟩
def cycle172_5 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data172 : PartitionData E W := ⟨6,![cycle172_0,cycle172_1,cycle172_2,cycle172_3,cycle172_4,cycle172_5]⟩
lemma valid_data172 : data172.Valid src172 dst172 Finset.univ := by decide +kernel

def src173 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,13,5,12,22,6,14,7,22,15]
def dst173 : E → W := ![5,6,4,7,2,13,14,12,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle173_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,13,4,6,5]⟩
def cycle173_1 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle173_2 : CycleData E W := ⟨3,![9,19,15,16,4],![2,15,6,14,7]⟩
def cycle173_3 : CycleData E W := ⟨2,![12,7,6,11],![5,12,14,13]⟩
def cycle173_4 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data173 : PartitionData E W := ⟨5,![cycle173_0,cycle173_1,cycle173_2,cycle173_3,cycle173_4]⟩
lemma valid_data173 : data173.Valid src173 dst173 Finset.univ := by decide +kernel

def src174 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,13,5,12,22,6,14,22,7,15]
def dst174 : E → W := ![5,6,4,7,2,13,14,12,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle174_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle174_1 : CycleData E W := ⟨2,![12,8,19,1],![5,12,15,6]⟩
def cycle174_2 : CycleData E W := ⟨2,![10,6,15,2],![4,13,14,6]⟩
def cycle174_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle174_4 : CycleData E W := ⟨1,![9,18,4],![2,15,7]⟩
def cycle174_5 : CycleData E W := ⟨1,![13,16,7],![12,22,14]⟩
def data174 : PartitionData E W := ⟨6,![cycle174_0,cycle174_1,cycle174_2,cycle174_3,cycle174_4,cycle174_5]⟩
lemma valid_data174 : data174.Valid src174 dst174 Finset.univ := by decide +kernel

def src175 : E → W := ![2,5,6,4,7,2,13,14,12,15,4,13,5,12,22,6,15,7,14,22]
def dst175 : E → W := ![5,6,4,7,2,13,14,12,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle175_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle175_1 : CycleData E W := ⟨2,![12,8,15,1],![5,12,15,6]⟩
def cycle175_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle175_3 : CycleData E W := ⟨2,![10,6,17,3],![4,13,14,7]⟩
def cycle175_4 : CycleData E W := ⟨1,![9,16,4],![2,15,7]⟩
def cycle175_5 : CycleData E W := ⟨1,![13,18,7],![12,22,14]⟩
def data175 : PartitionData E W := ⟨6,![cycle175_0,cycle175_1,cycle175_2,cycle175_3,cycle175_4,cycle175_5]⟩
lemma valid_data175 : data175.Valid src175 dst175 Finset.univ := by decide +kernel

def src176 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,13,22,6,14,7,15,22]
def dst176 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle176_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle176_1 : CycleData E W := ⟨2,![11,8,15,1],![5,12,14,6]⟩
def cycle176_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle176_3 : CycleData E W := ⟨2,![10,7,17,3],![4,12,15,7]⟩
def cycle176_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle176_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data176 : PartitionData E W := ⟨6,![cycle176_0,cycle176_1,cycle176_2,cycle176_3,cycle176_4,cycle176_5]⟩
lemma valid_data176 : data176.Valid src176 dst176 Finset.univ := by decide +kernel

def src177 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,13,22,6,14,7,22,15]
def dst177 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle177_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle177_1 : CycleData E W := ⟨2,![11,8,15,1],![5,12,14,6]⟩
def cycle177_2 : CycleData E W := ⟨2,![10,7,19,2],![4,12,15,6]⟩
def cycle177_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle177_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle177_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data177 : PartitionData E W := ⟨6,![cycle177_0,cycle177_1,cycle177_2,cycle177_3,cycle177_4,cycle177_5]⟩
lemma valid_data177 : data177.Valid src177 dst177 Finset.univ := by decide +kernel

def src178 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,13,22,6,14,22,7,15]
def dst178 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle178_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle178_1 : CycleData E W := ⟨2,![10,7,19,2],![4,12,15,6]⟩
def cycle178_2 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle178_3 : CycleData E W := ⟨2,![5,6,18,4],![2,13,15,7]⟩
def cycle178_4 : CycleData E W := ⟨3,![12,13,16,8,11],![5,13,22,14,12]⟩
def data178 : PartitionData E W := ⟨5,![cycle178_0,cycle178_1,cycle178_2,cycle178_3,cycle178_4]⟩
lemma valid_data178 : data178.Valid src178 dst178 Finset.univ := by decide +kernel

def src179 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,13,22,6,15,7,14,22]
def dst179 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle179_0 : CycleData E W := ⟨3,![5,6,15,1,0],![2,13,15,6,5]⟩
def cycle179_1 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle179_2 : CycleData E W := ⟨2,![10,7,16,3],![4,12,15,7]⟩
def cycle179_3 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle179_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,13,22,14,12]⟩
def data179 : PartitionData E W := ⟨5,![cycle179_0,cycle179_1,cycle179_2,cycle179_3,cycle179_4]⟩
lemma valid_data179 : data179.Valid src179 dst179 Finset.univ := by decide +kernel

def src180 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,22,13,6,14,7,15,22]
def dst180 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle180_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle180_1 : CycleData E W := ⟨2,![10,7,17,3],![4,12,15,7]⟩
def cycle180_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle180_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle180_4 : CycleData E W := ⟨3,![12,19,15,8,11],![5,22,6,14,12]⟩
def data180 : PartitionData E W := ⟨5,![cycle180_0,cycle180_1,cycle180_2,cycle180_3,cycle180_4]⟩
lemma valid_data180 : data180.Valid src180 dst180 Finset.univ := by decide +kernel

def src181 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,22,13,6,14,7,22,15]
def dst181 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle181_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle181_1 : CycleData E W := ⟨3,![10,11,12,17,3],![4,12,5,22,7]⟩
def cycle181_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle181_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle181_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,12,14]⟩
def data181 : PartitionData E W := ⟨5,![cycle181_0,cycle181_1,cycle181_2,cycle181_3,cycle181_4]⟩
lemma valid_data181 : data181.Valid src181 dst181 Finset.univ := by decide +kernel

def src182 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,22,13,6,14,22,7,15]
def dst182 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle182_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle182_1 : CycleData E W := ⟨2,![14,6,19,2],![4,13,15,6]⟩
def cycle182_2 : CycleData E W := ⟨2,![10,7,18,3],![4,12,15,7]⟩
def cycle182_3 : CycleData E W := ⟨2,![5,13,17,4],![2,13,22,7]⟩
def cycle182_4 : CycleData E W := ⟨2,![12,16,8,11],![5,22,14,12]⟩
def data182 : PartitionData E W := ⟨5,![cycle182_0,cycle182_1,cycle182_2,cycle182_3,cycle182_4]⟩
lemma valid_data182 : data182.Valid src182 dst182 Finset.univ := by decide +kernel

def src183 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,5,22,13,6,15,7,14,22]
def dst183 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle183_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle183_1 : CycleData E W := ⟨2,![10,7,16,3],![4,12,15,7]⟩
def cycle183_2 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle183_3 : CycleData E W := ⟨2,![19,13,6,15],![6,22,13,15]⟩
def cycle183_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,14,12]⟩
def data183 : PartitionData E W := ⟨5,![cycle183_0,cycle183_1,cycle183_2,cycle183_3,cycle183_4]⟩
lemma valid_data183 : data183.Valid src183 dst183 Finset.univ := by decide +kernel

def src184 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,22,5,13,6,14,7,15,22]
def dst184 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle184_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle184_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle184_2 : CycleData E W := ⟨2,![10,8,15,2],![4,12,14,6]⟩
def cycle184_3 : CycleData E W := ⟨2,![14,6,17,3],![4,13,15,7]⟩
def cycle184_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle184_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data184 : PartitionData E W := ⟨6,![cycle184_0,cycle184_1,cycle184_2,cycle184_3,cycle184_4,cycle184_5]⟩
lemma valid_data184 : data184.Valid src184 dst184 Finset.univ := by decide +kernel

def src185 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,22,5,13,6,14,7,22,15]
def dst185 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle185_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,6,5]⟩
def cycle185_1 : CycleData E W := ⟨2,![10,11,17,3],![4,12,22,7]⟩
def cycle185_2 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle185_3 : CycleData E W := ⟨2,![13,6,18,12],![5,13,15,22]⟩
def cycle185_4 : CycleData E W := ⟨2,![19,7,8,15],![6,15,12,14]⟩
def data185 : PartitionData E W := ⟨5,![cycle185_0,cycle185_1,cycle185_2,cycle185_3,cycle185_4]⟩
lemma valid_data185 : data185.Valid src185 dst185 Finset.univ := by decide +kernel

def src186 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,22,5,13,6,14,22,7,15]
def dst186 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle186_0 : CycleData E W := ⟨2,![9,15,1,0],![2,14,6,5]⟩
def cycle186_1 : CycleData E W := ⟨2,![14,6,19,2],![4,13,15,6]⟩
def cycle186_2 : CycleData E W := ⟨2,![10,7,18,3],![4,12,15,7]⟩
def cycle186_3 : CycleData E W := ⟨3,![5,13,12,17,4],![2,13,5,22,7]⟩
def cycle186_4 : CycleData E W := ⟨1,![11,16,8],![12,22,14]⟩
def data186 : PartitionData E W := ⟨5,![cycle186_0,cycle186_1,cycle186_2,cycle186_3,cycle186_4]⟩
lemma valid_data186 : data186.Valid src186 dst186 Finset.univ := by decide +kernel

def src187 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,12,22,5,13,6,15,7,14,22]
def dst187 : E → W := ![5,6,4,7,2,13,15,12,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle187_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle187_1 : CycleData E W := ⟨1,![12,19,1],![5,22,6]⟩
def cycle187_2 : CycleData E W := ⟨2,![14,6,15,2],![4,13,15,6]⟩
def cycle187_3 : CycleData E W := ⟨2,![10,7,16,3],![4,12,15,7]⟩
def cycle187_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle187_5 : CycleData E W := ⟨1,![11,18,8],![12,22,14]⟩
def data187 : PartitionData E W := ⟨6,![cycle187_0,cycle187_1,cycle187_2,cycle187_3,cycle187_4,cycle187_5]⟩
lemma valid_data187 : data187.Valid src187 dst187 Finset.univ := by decide +kernel

def src188 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,13,5,12,22,6,14,7,15,22]
def dst188 : E → W := ![5,6,4,7,2,13,15,12,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle188_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle188_1 : CycleData E W := ⟨2,![12,8,15,1],![5,12,14,6]⟩
def cycle188_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle188_3 : CycleData E W := ⟨2,![10,6,17,3],![4,13,15,7]⟩
def cycle188_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle188_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data188 : PartitionData E W := ⟨6,![cycle188_0,cycle188_1,cycle188_2,cycle188_3,cycle188_4,cycle188_5]⟩
lemma valid_data188 : data188.Valid src188 dst188 Finset.univ := by decide +kernel

def src189 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,13,5,12,22,6,14,7,22,15]
def dst189 : E → W := ![5,6,4,7,2,13,15,12,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle189_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle189_1 : CycleData E W := ⟨2,![12,8,15,1],![5,12,14,6]⟩
def cycle189_2 : CycleData E W := ⟨2,![10,6,19,2],![4,13,15,6]⟩
def cycle189_3 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle189_4 : CycleData E W := ⟨1,![9,16,4],![2,14,7]⟩
def cycle189_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data189 : PartitionData E W := ⟨6,![cycle189_0,cycle189_1,cycle189_2,cycle189_3,cycle189_4,cycle189_5]⟩
lemma valid_data189 : data189.Valid src189 dst189 Finset.univ := by decide +kernel

def src190 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,13,5,12,22,6,14,22,7,15]
def dst190 : E → W := ![5,6,4,7,2,13,15,12,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle190_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,13,4,6,5]⟩
def cycle190_1 : CycleData E W := ⟨1,![14,17,3],![4,22,7]⟩
def cycle190_2 : CycleData E W := ⟨3,![9,15,19,18,4],![2,14,6,15,7]⟩
def cycle190_3 : CycleData E W := ⟨2,![12,7,6,11],![5,12,15,13]⟩
def cycle190_4 : CycleData E W := ⟨1,![13,16,8],![12,22,14]⟩
def data190 : PartitionData E W := ⟨5,![cycle190_0,cycle190_1,cycle190_2,cycle190_3,cycle190_4]⟩
lemma valid_data190 : data190.Valid src190 dst190 Finset.univ := by decide +kernel

def src191 : E → W := ![2,5,6,4,7,2,13,15,12,14,4,13,5,12,22,6,15,7,14,22]
def dst191 : E → W := ![5,6,4,7,2,13,15,12,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle191_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle191_1 : CycleData E W := ⟨2,![12,7,15,1],![5,12,15,6]⟩
def cycle191_2 : CycleData E W := ⟨1,![14,19,2],![4,22,6]⟩
def cycle191_3 : CycleData E W := ⟨2,![10,6,16,3],![4,13,15,7]⟩
def cycle191_4 : CycleData E W := ⟨1,![9,17,4],![2,14,7]⟩
def cycle191_5 : CycleData E W := ⟨1,![13,18,8],![12,22,14]⟩
def data191 : PartitionData E W := ⟨6,![cycle191_0,cycle191_1,cycle191_2,cycle191_3,cycle191_4,cycle191_5]⟩
lemma valid_data191 : data191.Valid src191 dst191 Finset.univ := by decide +kernel

def src192 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,13,22,6,14,7,15,22]
def dst192 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle192_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle192_1 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle192_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,15,7,14,6]⟩
def cycle192_3 : CycleData E W := ⟨2,![12,7,6,11],![5,13,14,12]⟩
def cycle192_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data192 : PartitionData E W := ⟨5,![cycle192_0,cycle192_1,cycle192_2,cycle192_3,cycle192_4]⟩
lemma valid_data192 : data192.Valid src192 dst192 Finset.univ := by decide +kernel

def src193 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,13,22,6,14,7,22,15]
def dst193 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle193_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle193_1 : CycleData E W := ⟨2,![12,7,16,1],![5,13,14,7]⟩
def cycle193_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle193_3 : CycleData E W := ⟨2,![10,6,15,3],![4,12,14,6]⟩
def cycle193_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle193_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data193 : PartitionData E W := ⟨6,![cycle193_0,cycle193_1,cycle193_2,cycle193_3,cycle193_4,cycle193_5]⟩
lemma valid_data193 : data193.Valid src193 dst193 Finset.univ := by decide +kernel

def src194 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,13,22,6,14,22,7,15]
def dst194 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle194_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle194_1 : CycleData E W := ⟨2,![12,8,18,1],![5,13,15,7]⟩
def cycle194_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle194_3 : CycleData E W := ⟨2,![10,6,15,3],![4,12,14,6]⟩
def cycle194_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle194_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data194 : PartitionData E W := ⟨6,![cycle194_0,cycle194_1,cycle194_2,cycle194_3,cycle194_4,cycle194_5]⟩
lemma valid_data194 : data194.Valid src194 dst194 Finset.univ := by decide +kernel

def src195 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,13,22,6,15,7,14,22]
def dst195 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle195_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle195_1 : CycleData E W := ⟨2,![12,8,16,1],![5,13,15,7]⟩
def cycle195_2 : CycleData E W := ⟨2,![10,6,17,2],![4,12,14,7]⟩
def cycle195_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle195_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle195_5 : CycleData E W := ⟨1,![13,18,7],![13,22,14]⟩
def data195 : PartitionData E W := ⟨6,![cycle195_0,cycle195_1,cycle195_2,cycle195_3,cycle195_4,cycle195_5]⟩
lemma valid_data195 : data195.Valid src195 dst195 Finset.univ := by decide +kernel

def src196 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,22,13,6,14,7,15,22]
def dst196 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle196_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,5]⟩
def cycle196_1 : CycleData E W := ⟨2,![10,6,16,2],![4,12,14,7]⟩
def cycle196_2 : CycleData E W := ⟨2,![14,7,15,3],![4,13,14,6]⟩
def cycle196_3 : CycleData E W := ⟨3,![5,11,12,19,4],![2,12,5,22,6]⟩
def cycle196_4 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data196 : PartitionData E W := ⟨5,![cycle196_0,cycle196_1,cycle196_2,cycle196_3,cycle196_4]⟩
lemma valid_data196 : data196.Valid src196 dst196 Finset.univ := by decide +kernel

def src197 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,22,13,6,14,7,22,15]
def dst197 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle197_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle197_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle197_2 : CycleData E W := ⟨2,![10,6,16,2],![4,12,14,7]⟩
def cycle197_3 : CycleData E W := ⟨2,![14,7,15,3],![4,13,14,6]⟩
def cycle197_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle197_5 : CycleData E W := ⟨1,![13,18,8],![13,22,15]⟩
def data197 : PartitionData E W := ⟨6,![cycle197_0,cycle197_1,cycle197_2,cycle197_3,cycle197_4,cycle197_5]⟩
lemma valid_data197 : data197.Valid src197 dst197 Finset.univ := by decide +kernel

def src198 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,22,13,6,14,22,7,15]
def dst198 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle198_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle198_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle198_2 : CycleData E W := ⟨2,![14,8,18,2],![4,13,15,7]⟩
def cycle198_3 : CycleData E W := ⟨2,![10,6,15,3],![4,12,14,6]⟩
def cycle198_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle198_5 : CycleData E W := ⟨1,![13,16,7],![13,22,14]⟩
def data198 : PartitionData E W := ⟨6,![cycle198_0,cycle198_1,cycle198_2,cycle198_3,cycle198_4,cycle198_5]⟩
lemma valid_data198 : data198.Valid src198 dst198 Finset.univ := by decide +kernel

def src199 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,5,22,13,6,15,7,14,22]
def dst199 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle199_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle199_1 : CycleData E W := ⟨2,![14,13,19,3],![4,13,22,6]⟩
def cycle199_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle199_3 : CycleData E W := ⟨2,![12,18,6,11],![5,22,14,12]⟩
def cycle199_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,13,15]⟩
def data199 : PartitionData E W := ⟨5,![cycle199_0,cycle199_1,cycle199_2,cycle199_3,cycle199_4]⟩
lemma valid_data199 : data199.Valid src199 dst199 Finset.univ := by decide +kernel

def src200 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,22,5,13,6,14,7,15,22]
def dst200 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle200_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,5]⟩
def cycle200_1 : CycleData E W := ⟨2,![10,6,16,2],![4,12,14,7]⟩
def cycle200_2 : CycleData E W := ⟨2,![14,7,15,3],![4,13,14,6]⟩
def cycle200_3 : CycleData E W := ⟨2,![5,11,19,4],![2,12,22,6]⟩
def cycle200_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,15,22]⟩
def data200 : PartitionData E W := ⟨5,![cycle200_0,cycle200_1,cycle200_2,cycle200_3,cycle200_4]⟩
lemma valid_data200 : data200.Valid src200 dst200 Finset.univ := by decide +kernel

def src201 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,22,5,13,6,14,7,22,15]
def dst201 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle201_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle201_1 : CycleData E W := ⟨2,![14,7,15,3],![4,13,14,6]⟩
def cycle201_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle201_3 : CycleData E W := ⟨2,![17,11,6,16],![7,22,12,14]⟩
def cycle201_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,15,22]⟩
def data201 : PartitionData E W := ⟨5,![cycle201_0,cycle201_1,cycle201_2,cycle201_3,cycle201_4]⟩
lemma valid_data201 : data201.Valid src201 dst201 Finset.univ := by decide +kernel

def src202 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,22,5,13,6,14,22,7,15]
def dst202 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle202_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle202_1 : CycleData E W := ⟨2,![14,7,15,3],![4,13,14,6]⟩
def cycle202_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle202_3 : CycleData E W := ⟨1,![11,16,6],![12,22,14]⟩
def cycle202_4 : CycleData E W := ⟨3,![13,8,18,17,12],![5,13,15,7,22]⟩
def data202 : PartitionData E W := ⟨5,![cycle202_0,cycle202_1,cycle202_2,cycle202_3,cycle202_4]⟩
lemma valid_data202 : data202.Valid src202 dst202 Finset.univ := by decide +kernel

def src203 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,12,22,5,13,6,15,7,14,22]
def dst203 : E → W := ![5,7,4,6,2,12,14,13,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle203_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle203_1 : CycleData E W := ⟨3,![14,13,12,19,3],![4,13,5,22,6]⟩
def cycle203_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle203_3 : CycleData E W := ⟨1,![11,18,6],![12,22,14]⟩
def cycle203_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,13,15]⟩
def data203 : PartitionData E W := ⟨5,![cycle203_0,cycle203_1,cycle203_2,cycle203_3,cycle203_4]⟩
lemma valid_data203 : data203.Valid src203 dst203 Finset.univ := by decide +kernel

def src204 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,13,5,12,22,6,14,7,15,22]
def dst204 : E → W := ![5,7,4,6,2,12,14,13,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle204_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,14,7,5]⟩
def cycle204_1 : CycleData E W := ⟨2,![10,8,17,2],![4,13,15,7]⟩
def cycle204_2 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle204_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,12]⟩
def cycle204_4 : CycleData E W := ⟨2,![12,6,7,11],![5,12,14,13]⟩
def data204 : PartitionData E W := ⟨5,![cycle204_0,cycle204_1,cycle204_2,cycle204_3,cycle204_4]⟩
lemma valid_data204 : data204.Valid src204 dst204 Finset.univ := by decide +kernel

def src205 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,13,5,12,22,6,14,7,22,15]
def dst205 : E → W := ![5,7,4,6,2,12,14,13,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle205_0 : CycleData E W := ⟨3,![5,6,16,1,0],![2,12,14,7,5]⟩
def cycle205_1 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle205_2 : CycleData E W := ⟨2,![10,7,15,3],![4,13,14,6]⟩
def cycle205_3 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle205_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,12,22,15,13]⟩
def data205 : PartitionData E W := ⟨5,![cycle205_0,cycle205_1,cycle205_2,cycle205_3,cycle205_4]⟩
lemma valid_data205 : data205.Valid src205 dst205 Finset.univ := by decide +kernel

def src206 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,13,5,12,22,6,14,22,7,15]
def dst206 : E → W := ![5,7,4,6,2,12,14,13,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle206_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle206_1 : CycleData E W := ⟨2,![11,8,18,1],![5,13,15,7]⟩
def cycle206_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle206_3 : CycleData E W := ⟨2,![10,7,15,3],![4,13,14,6]⟩
def cycle206_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle206_5 : CycleData E W := ⟨1,![13,16,6],![12,22,14]⟩
def data206 : PartitionData E W := ⟨6,![cycle206_0,cycle206_1,cycle206_2,cycle206_3,cycle206_4,cycle206_5]⟩
lemma valid_data206 : data206.Valid src206 dst206 Finset.univ := by decide +kernel

def src207 : E → W := ![2,5,7,4,6,2,12,14,13,15,4,13,5,12,22,6,15,7,14,22]
def dst207 : E → W := ![5,7,4,6,2,12,14,13,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle207_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle207_1 : CycleData E W := ⟨2,![11,8,16,1],![5,13,15,7]⟩
def cycle207_2 : CycleData E W := ⟨2,![10,7,17,2],![4,13,14,7]⟩
def cycle207_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle207_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle207_5 : CycleData E W := ⟨1,![13,18,6],![12,22,14]⟩
def data207 : PartitionData E W := ⟨6,![cycle207_0,cycle207_1,cycle207_2,cycle207_3,cycle207_4,cycle207_5]⟩
lemma valid_data207 : data207.Valid src207 dst207 Finset.univ := by decide +kernel

def src208 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,13,22,6,14,7,15,22]
def dst208 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle208_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle208_1 : CycleData E W := ⟨2,![12,8,16,1],![5,13,14,7]⟩
def cycle208_2 : CycleData E W := ⟨2,![10,6,17,2],![4,12,15,7]⟩
def cycle208_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle208_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle208_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data208 : PartitionData E W := ⟨6,![cycle208_0,cycle208_1,cycle208_2,cycle208_3,cycle208_4,cycle208_5]⟩
lemma valid_data208 : data208.Valid src208 dst208 Finset.univ := by decide +kernel

def src209 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,13,22,6,14,7,22,15]
def dst209 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle209_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle209_1 : CycleData E W := ⟨2,![12,8,16,1],![5,13,14,7]⟩
def cycle209_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle209_3 : CycleData E W := ⟨2,![10,6,19,3],![4,12,15,6]⟩
def cycle209_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle209_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data209 : PartitionData E W := ⟨6,![cycle209_0,cycle209_1,cycle209_2,cycle209_3,cycle209_4,cycle209_5]⟩
lemma valid_data209 : data209.Valid src209 dst209 Finset.univ := by decide +kernel

def src210 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,13,22,6,14,22,7,15]
def dst210 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle210_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle210_1 : CycleData E W := ⟨2,![12,7,18,1],![5,13,15,7]⟩
def cycle210_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle210_3 : CycleData E W := ⟨2,![10,6,19,3],![4,12,15,6]⟩
def cycle210_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle210_5 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data210 : PartitionData E W := ⟨6,![cycle210_0,cycle210_1,cycle210_2,cycle210_3,cycle210_4,cycle210_5]⟩
lemma valid_data210 : data210.Valid src210 dst210 Finset.univ := by decide +kernel

def src211 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,13,22,6,15,7,14,22]
def dst211 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle211_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle211_1 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle211_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,14,7,15,6]⟩
def cycle211_3 : CycleData E W := ⟨2,![12,7,6,11],![5,13,15,12]⟩
def cycle211_4 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data211 : PartitionData E W := ⟨5,![cycle211_0,cycle211_1,cycle211_2,cycle211_3,cycle211_4]⟩
lemma valid_data211 : data211.Valid src211 dst211 Finset.univ := by decide +kernel

def src212 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,22,13,6,14,7,15,22]
def dst212 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle212_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle212_1 : CycleData E W := ⟨2,![14,13,19,3],![4,13,22,6]⟩
def cycle212_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle212_3 : CycleData E W := ⟨2,![12,18,6,11],![5,22,15,12]⟩
def cycle212_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,13,14]⟩
def data212 : PartitionData E W := ⟨5,![cycle212_0,cycle212_1,cycle212_2,cycle212_3,cycle212_4]⟩
lemma valid_data212 : data212.Valid src212 dst212 Finset.univ := by decide +kernel

def src213 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,22,13,6,14,7,22,15]
def dst213 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle213_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle213_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle213_2 : CycleData E W := ⟨2,![14,8,16,2],![4,13,14,7]⟩
def cycle213_3 : CycleData E W := ⟨2,![10,6,19,3],![4,12,15,6]⟩
def cycle213_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle213_5 : CycleData E W := ⟨1,![13,18,7],![13,22,15]⟩
def data213 : PartitionData E W := ⟨6,![cycle213_0,cycle213_1,cycle213_2,cycle213_3,cycle213_4,cycle213_5]⟩
lemma valid_data213 : data213.Valid src213 dst213 Finset.univ := by decide +kernel

def src214 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,22,13,6,14,22,7,15]
def dst214 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle214_0 : CycleData E W := ⟨1,![5,11,0],![2,12,5]⟩
def cycle214_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle214_2 : CycleData E W := ⟨2,![10,6,18,2],![4,12,15,7]⟩
def cycle214_3 : CycleData E W := ⟨2,![14,7,19,3],![4,13,15,6]⟩
def cycle214_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle214_5 : CycleData E W := ⟨1,![13,16,8],![13,22,14]⟩
def data214 : PartitionData E W := ⟨6,![cycle214_0,cycle214_1,cycle214_2,cycle214_3,cycle214_4,cycle214_5]⟩
lemma valid_data214 : data214.Valid src214 dst214 Finset.univ := by decide +kernel

def src215 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,5,22,13,6,15,7,14,22]
def dst215 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle215_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,5]⟩
def cycle215_1 : CycleData E W := ⟨2,![10,6,16,2],![4,12,15,7]⟩
def cycle215_2 : CycleData E W := ⟨2,![14,7,15,3],![4,13,15,6]⟩
def cycle215_3 : CycleData E W := ⟨3,![5,11,12,19,4],![2,12,5,22,6]⟩
def cycle215_4 : CycleData E W := ⟨1,![13,18,8],![13,22,14]⟩
def data215 : PartitionData E W := ⟨5,![cycle215_0,cycle215_1,cycle215_2,cycle215_3,cycle215_4]⟩
lemma valid_data215 : data215.Valid src215 dst215 Finset.univ := by decide +kernel

def src216 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,22,5,13,6,14,7,15,22]
def dst216 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle216_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle216_1 : CycleData E W := ⟨3,![14,13,12,19,3],![4,13,5,22,6]⟩
def cycle216_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle216_3 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle216_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,13,14]⟩
def data216 : PartitionData E W := ⟨5,![cycle216_0,cycle216_1,cycle216_2,cycle216_3,cycle216_4]⟩
lemma valid_data216 : data216.Valid src216 dst216 Finset.univ := by decide +kernel

def src217 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,22,5,13,6,14,7,22,15]
def dst217 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle217_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle217_1 : CycleData E W := ⟨2,![14,7,19,3],![4,13,15,6]⟩
def cycle217_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle217_3 : CycleData E W := ⟨1,![11,18,6],![12,22,15]⟩
def cycle217_4 : CycleData E W := ⟨3,![13,8,16,17,12],![5,13,14,7,22]⟩
def data217 : PartitionData E W := ⟨5,![cycle217_0,cycle217_1,cycle217_2,cycle217_3,cycle217_4]⟩
lemma valid_data217 : data217.Valid src217 dst217 Finset.univ := by decide +kernel

def src218 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,22,5,13,6,14,22,7,15]
def dst218 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle218_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,12,4,7,5]⟩
def cycle218_1 : CycleData E W := ⟨2,![14,7,19,3],![4,13,15,6]⟩
def cycle218_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle218_3 : CycleData E W := ⟨2,![18,6,11,17],![7,15,12,22]⟩
def cycle218_4 : CycleData E W := ⟨2,![13,8,16,12],![5,13,14,22]⟩
def data218 : PartitionData E W := ⟨5,![cycle218_0,cycle218_1,cycle218_2,cycle218_3,cycle218_4]⟩
lemma valid_data218 : data218.Valid src218 dst218 Finset.univ := by decide +kernel

def src219 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,12,22,5,13,6,15,7,14,22]
def dst219 : E → W := ![5,7,4,6,2,12,15,13,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle219_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,5]⟩
def cycle219_1 : CycleData E W := ⟨2,![10,6,16,2],![4,12,15,7]⟩
def cycle219_2 : CycleData E W := ⟨2,![14,7,15,3],![4,13,15,6]⟩
def cycle219_3 : CycleData E W := ⟨2,![5,11,19,4],![2,12,22,6]⟩
def cycle219_4 : CycleData E W := ⟨2,![13,8,18,12],![5,13,14,22]⟩
def data219 : PartitionData E W := ⟨5,![cycle219_0,cycle219_1,cycle219_2,cycle219_3,cycle219_4]⟩
lemma valid_data219 : data219.Valid src219 dst219 Finset.univ := by decide +kernel

def src220 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,13,5,12,22,6,14,7,15,22]
def dst220 : E → W := ![5,7,4,6,2,12,15,13,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle220_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle220_1 : CycleData E W := ⟨2,![11,8,16,1],![5,13,14,7]⟩
def cycle220_2 : CycleData E W := ⟨2,![10,7,17,2],![4,13,15,7]⟩
def cycle220_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle220_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle220_5 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def data220 : PartitionData E W := ⟨6,![cycle220_0,cycle220_1,cycle220_2,cycle220_3,cycle220_4,cycle220_5]⟩
lemma valid_data220 : data220.Valid src220 dst220 Finset.univ := by decide +kernel

def src221 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,13,5,12,22,6,14,7,22,15]
def dst221 : E → W := ![5,7,4,6,2,12,15,13,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle221_0 : CycleData E W := ⟨1,![5,12,0],![2,12,5]⟩
def cycle221_1 : CycleData E W := ⟨2,![11,8,16,1],![5,13,14,7]⟩
def cycle221_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle221_3 : CycleData E W := ⟨2,![10,7,19,3],![4,13,15,6]⟩
def cycle221_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle221_5 : CycleData E W := ⟨1,![13,18,6],![12,22,15]⟩
def data221 : PartitionData E W := ⟨6,![cycle221_0,cycle221_1,cycle221_2,cycle221_3,cycle221_4,cycle221_5]⟩
lemma valid_data221 : data221.Valid src221 dst221 Finset.univ := by decide +kernel

def src222 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,13,5,12,22,6,14,22,7,15]
def dst222 : E → W := ![5,7,4,6,2,12,15,13,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle222_0 : CycleData E W := ⟨3,![5,13,17,1,0],![2,12,22,7,5]⟩
def cycle222_1 : CycleData E W := ⟨2,![3,19,18,2],![4,6,15,7]⟩
def cycle222_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle222_3 : CycleData E W := ⟨2,![12,6,7,11],![5,12,15,13]⟩
def cycle222_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,13]⟩
def data222 : PartitionData E W := ⟨5,![cycle222_0,cycle222_1,cycle222_2,cycle222_3,cycle222_4]⟩
lemma valid_data222 : data222.Valid src222 dst222 Finset.univ := by decide +kernel

def src223 : E → W := ![2,5,7,4,6,2,12,15,13,14,4,13,5,12,22,6,15,7,14,22]
def dst223 : E → W := ![5,7,4,6,2,12,15,13,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle223_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,15,7,5]⟩
def cycle223_1 : CycleData E W := ⟨2,![10,8,17,2],![4,13,14,7]⟩
def cycle223_2 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle223_3 : CycleData E W := ⟨2,![9,18,13,5],![2,14,22,12]⟩
def cycle223_4 : CycleData E W := ⟨2,![12,6,7,11],![5,12,15,13]⟩
def data223 : PartitionData E W := ⟨5,![cycle223_0,cycle223_1,cycle223_2,cycle223_3,cycle223_4]⟩
lemma valid_data223 : data223.Valid src223 dst223 Finset.univ := by decide +kernel

def src224 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,13,22,6,14,7,15,22]
def dst224 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,13,22,4,14,7,15,22,6]
def cycle224_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,14,7,5]⟩
def cycle224_1 : CycleData E W := ⟨2,![10,8,17,2],![4,12,15,7]⟩
def cycle224_2 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle224_3 : CycleData E W := ⟨2,![9,18,13,5],![2,15,22,13]⟩
def cycle224_4 : CycleData E W := ⟨2,![12,6,7,11],![5,13,14,12]⟩
def data224 : PartitionData E W := ⟨5,![cycle224_0,cycle224_1,cycle224_2,cycle224_3,cycle224_4]⟩
lemma valid_data224 : data224.Valid src224 dst224 Finset.univ := by decide +kernel

def src225 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,13,22,6,14,7,22,15]
def dst225 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,13,22,4,14,7,22,15,6]
def cycle225_0 : CycleData E W := ⟨3,![5,6,16,1,0],![2,13,14,7,5]⟩
def cycle225_1 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle225_2 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle225_3 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle225_4 : CycleData E W := ⟨3,![12,13,18,8,11],![5,13,22,15,12]⟩
def data225 : PartitionData E W := ⟨5,![cycle225_0,cycle225_1,cycle225_2,cycle225_3,cycle225_4]⟩
lemma valid_data225 : data225.Valid src225 dst225 Finset.univ := by decide +kernel

def src226 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,13,22,6,14,22,7,15]
def dst226 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,13,22,4,14,22,7,15,6]
def cycle226_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle226_1 : CycleData E W := ⟨2,![11,8,18,1],![5,12,15,7]⟩
def cycle226_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle226_3 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle226_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle226_5 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def data226 : PartitionData E W := ⟨6,![cycle226_0,cycle226_1,cycle226_2,cycle226_3,cycle226_4,cycle226_5]⟩
lemma valid_data226 : data226.Valid src226 dst226 Finset.univ := by decide +kernel

def src227 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,13,22,6,15,7,14,22]
def dst227 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,13,22,4,15,7,14,22,6]
def cycle227_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle227_1 : CycleData E W := ⟨2,![11,8,16,1],![5,12,15,7]⟩
def cycle227_2 : CycleData E W := ⟨2,![10,7,17,2],![4,12,14,7]⟩
def cycle227_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle227_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle227_5 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def data227 : PartitionData E W := ⟨6,![cycle227_0,cycle227_1,cycle227_2,cycle227_3,cycle227_4,cycle227_5]⟩
lemma valid_data227 : data227.Valid src227 dst227 Finset.univ := by decide +kernel

def src228 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,22,13,6,14,7,15,22]
def dst228 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,22,13,4,14,7,15,22,6]
def cycle228_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,5]⟩
def cycle228_1 : CycleData E W := ⟨2,![14,6,16,2],![4,13,14,7]⟩
def cycle228_2 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle228_3 : CycleData E W := ⟨2,![5,13,19,4],![2,13,22,6]⟩
def cycle228_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,15,12]⟩
def data228 : PartitionData E W := ⟨5,![cycle228_0,cycle228_1,cycle228_2,cycle228_3,cycle228_4]⟩
lemma valid_data228 : data228.Valid src228 dst228 Finset.univ := by decide +kernel

def src229 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,22,13,6,14,7,22,15]
def dst229 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,22,13,4,14,7,22,15,6]
def cycle229_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle229_1 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle229_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle229_3 : CycleData E W := ⟨2,![17,13,6,16],![7,22,13,14]⟩
def cycle229_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,15,12]⟩
def data229 : PartitionData E W := ⟨5,![cycle229_0,cycle229_1,cycle229_2,cycle229_3,cycle229_4]⟩
lemma valid_data229 : data229.Valid src229 dst229 Finset.univ := by decide +kernel

def src230 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,22,13,6,14,22,7,15]
def dst230 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,22,13,4,14,22,7,15,6]
def cycle230_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle230_1 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle230_2 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle230_3 : CycleData E W := ⟨1,![13,16,6],![13,22,14]⟩
def cycle230_4 : CycleData E W := ⟨3,![12,17,18,8,11],![5,22,7,15,12]⟩
def data230 : PartitionData E W := ⟨5,![cycle230_0,cycle230_1,cycle230_2,cycle230_3,cycle230_4]⟩
lemma valid_data230 : data230.Valid src230 dst230 Finset.univ := by decide +kernel

def src231 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,5,22,13,6,15,7,14,22]
def dst231 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,5,22,13,4,15,7,14,22,6]
def cycle231_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle231_1 : CycleData E W := ⟨3,![10,11,12,19,3],![4,12,5,22,6]⟩
def cycle231_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle231_3 : CycleData E W := ⟨1,![13,18,6],![13,22,14]⟩
def cycle231_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,12,15]⟩
def data231 : PartitionData E W := ⟨5,![cycle231_0,cycle231_1,cycle231_2,cycle231_3,cycle231_4]⟩
lemma valid_data231 : data231.Valid src231 dst231 Finset.univ := by decide +kernel

def src232 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,22,5,13,6,14,7,15,22]
def dst232 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,22,5,13,4,14,7,15,22,6]
def cycle232_0 : CycleData E W := ⟨2,![9,17,1,0],![2,15,7,5]⟩
def cycle232_1 : CycleData E W := ⟨2,![14,6,16,2],![4,13,14,7]⟩
def cycle232_2 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle232_3 : CycleData E W := ⟨3,![5,13,12,19,4],![2,13,5,22,6]⟩
def cycle232_4 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data232 : PartitionData E W := ⟨5,![cycle232_0,cycle232_1,cycle232_2,cycle232_3,cycle232_4]⟩
lemma valid_data232 : data232.Valid src232 dst232 Finset.univ := by decide +kernel

def src233 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,22,5,13,6,14,7,22,15]
def dst233 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,22,5,13,4,14,7,22,15,6]
def cycle233_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle233_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle233_2 : CycleData E W := ⟨2,![14,6,16,2],![4,13,14,7]⟩
def cycle233_3 : CycleData E W := ⟨2,![10,7,15,3],![4,12,14,6]⟩
def cycle233_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle233_5 : CycleData E W := ⟨1,![11,18,8],![12,22,15]⟩
def data233 : PartitionData E W := ⟨6,![cycle233_0,cycle233_1,cycle233_2,cycle233_3,cycle233_4,cycle233_5]⟩
lemma valid_data233 : data233.Valid src233 dst233 Finset.univ := by decide +kernel

def src234 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,22,5,13,6,14,22,7,15]
def dst234 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,22,5,13,4,14,22,7,15,6]
def cycle234_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle234_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle234_2 : CycleData E W := ⟨2,![10,8,18,2],![4,12,15,7]⟩
def cycle234_3 : CycleData E W := ⟨2,![14,6,15,3],![4,13,14,6]⟩
def cycle234_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle234_5 : CycleData E W := ⟨1,![11,16,7],![12,22,14]⟩
def data234 : PartitionData E W := ⟨6,![cycle234_0,cycle234_1,cycle234_2,cycle234_3,cycle234_4,cycle234_5]⟩
lemma valid_data234 : data234.Valid src234 dst234 Finset.univ := by decide +kernel

def src235 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,12,22,5,13,6,15,7,14,22]
def dst235 : E → W := ![5,7,4,6,2,13,14,12,15,2,12,22,5,13,4,15,7,14,22,6]
def cycle235_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle235_1 : CycleData E W := ⟨2,![10,11,19,3],![4,12,22,6]⟩
def cycle235_2 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle235_3 : CycleData E W := ⟨2,![13,6,18,12],![5,13,14,22]⟩
def cycle235_4 : CycleData E W := ⟨2,![17,7,8,16],![7,14,12,15]⟩
def data235 : PartitionData E W := ⟨5,![cycle235_0,cycle235_1,cycle235_2,cycle235_3,cycle235_4]⟩
lemma valid_data235 : data235.Valid src235 dst235 Finset.univ := by decide +kernel

def src236 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,13,5,12,22,6,14,7,15,22]
def dst236 : E → W := ![5,7,4,6,2,13,14,12,15,2,13,5,12,22,4,14,7,15,22,6]
def cycle236_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,13,4,7,5]⟩
def cycle236_1 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle236_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,15,7,14,6]⟩
def cycle236_3 : CycleData E W := ⟨2,![12,7,6,11],![5,12,14,13]⟩
def cycle236_4 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data236 : PartitionData E W := ⟨5,![cycle236_0,cycle236_1,cycle236_2,cycle236_3,cycle236_4]⟩
lemma valid_data236 : data236.Valid src236 dst236 Finset.univ := by decide +kernel

def src237 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,13,5,12,22,6,14,7,22,15]
def dst237 : E → W := ![5,7,4,6,2,13,14,12,15,2,13,5,12,22,4,14,7,22,15,6]
def cycle237_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle237_1 : CycleData E W := ⟨2,![12,7,16,1],![5,12,14,7]⟩
def cycle237_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle237_3 : CycleData E W := ⟨2,![10,6,15,3],![4,13,14,6]⟩
def cycle237_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle237_5 : CycleData E W := ⟨1,![13,18,8],![12,22,15]⟩
def data237 : PartitionData E W := ⟨6,![cycle237_0,cycle237_1,cycle237_2,cycle237_3,cycle237_4,cycle237_5]⟩
lemma valid_data237 : data237.Valid src237 dst237 Finset.univ := by decide +kernel

def src238 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,13,5,12,22,6,14,22,7,15]
def dst238 : E → W := ![5,7,4,6,2,13,14,12,15,2,13,5,12,22,4,14,22,7,15,6]
def cycle238_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle238_1 : CycleData E W := ⟨2,![12,8,18,1],![5,12,15,7]⟩
def cycle238_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle238_3 : CycleData E W := ⟨2,![10,6,15,3],![4,13,14,6]⟩
def cycle238_4 : CycleData E W := ⟨1,![9,19,4],![2,15,6]⟩
def cycle238_5 : CycleData E W := ⟨1,![13,16,7],![12,22,14]⟩
def data238 : PartitionData E W := ⟨6,![cycle238_0,cycle238_1,cycle238_2,cycle238_3,cycle238_4,cycle238_5]⟩
lemma valid_data238 : data238.Valid src238 dst238 Finset.univ := by decide +kernel

def src239 : E → W := ![2,5,7,4,6,2,13,14,12,15,4,13,5,12,22,6,15,7,14,22]
def dst239 : E → W := ![5,7,4,6,2,13,14,12,15,2,13,5,12,22,4,15,7,14,22,6]
def cycle239_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle239_1 : CycleData E W := ⟨2,![12,8,16,1],![5,12,15,7]⟩
def cycle239_2 : CycleData E W := ⟨2,![10,6,17,2],![4,13,14,7]⟩
def cycle239_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle239_4 : CycleData E W := ⟨1,![9,15,4],![2,15,6]⟩
def cycle239_5 : CycleData E W := ⟨1,![13,18,7],![12,22,14]⟩
def data239 : PartitionData E W := ⟨6,![cycle239_0,cycle239_1,cycle239_2,cycle239_3,cycle239_4,cycle239_5]⟩
lemma valid_data239 : data239.Valid src239 dst239 Finset.univ := by decide +kernel

def src240 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,13,22,6,14,7,15,22]
def dst240 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,13,22,4,14,7,15,22,6]
def cycle240_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle240_1 : CycleData E W := ⟨2,![11,8,16,1],![5,12,14,7]⟩
def cycle240_2 : CycleData E W := ⟨2,![10,7,17,2],![4,12,15,7]⟩
def cycle240_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle240_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle240_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data240 : PartitionData E W := ⟨6,![cycle240_0,cycle240_1,cycle240_2,cycle240_3,cycle240_4,cycle240_5]⟩
lemma valid_data240 : data240.Valid src240 dst240 Finset.univ := by decide +kernel

def src241 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,13,22,6,14,7,22,15]
def dst241 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,13,22,4,14,7,22,15,6]
def cycle241_0 : CycleData E W := ⟨1,![5,12,0],![2,13,5]⟩
def cycle241_1 : CycleData E W := ⟨2,![11,8,16,1],![5,12,14,7]⟩
def cycle241_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle241_3 : CycleData E W := ⟨2,![10,7,19,3],![4,12,15,6]⟩
def cycle241_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle241_5 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def data241 : PartitionData E W := ⟨6,![cycle241_0,cycle241_1,cycle241_2,cycle241_3,cycle241_4,cycle241_5]⟩
lemma valid_data241 : data241.Valid src241 dst241 Finset.univ := by decide +kernel

def src242 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,13,22,6,14,22,7,15]
def dst242 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,13,22,4,14,22,7,15,6]
def cycle242_0 : CycleData E W := ⟨3,![5,13,17,1,0],![2,13,22,7,5]⟩
def cycle242_1 : CycleData E W := ⟨2,![3,19,18,2],![4,6,15,7]⟩
def cycle242_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle242_3 : CycleData E W := ⟨2,![12,6,7,11],![5,13,15,12]⟩
def cycle242_4 : CycleData E W := ⟨2,![14,16,8,10],![4,22,14,12]⟩
def data242 : PartitionData E W := ⟨5,![cycle242_0,cycle242_1,cycle242_2,cycle242_3,cycle242_4]⟩
lemma valid_data242 : data242.Valid src242 dst242 Finset.univ := by decide +kernel

def src243 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,13,22,6,15,7,14,22]
def dst243 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,13,22,4,15,7,14,22,6]
def cycle243_0 : CycleData E W := ⟨3,![4,15,16,1,0],![2,6,15,7,5]⟩
def cycle243_1 : CycleData E W := ⟨2,![10,8,17,2],![4,12,14,7]⟩
def cycle243_2 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle243_3 : CycleData E W := ⟨2,![9,18,13,5],![2,14,22,13]⟩
def cycle243_4 : CycleData E W := ⟨2,![12,6,7,11],![5,13,15,12]⟩
def data243 : PartitionData E W := ⟨5,![cycle243_0,cycle243_1,cycle243_2,cycle243_3,cycle243_4]⟩
lemma valid_data243 : data243.Valid src243 dst243 Finset.univ := by decide +kernel

def src244 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,22,13,6,14,7,15,22]
def dst244 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,22,13,4,14,7,15,22,6]
def cycle244_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle244_1 : CycleData E W := ⟨3,![10,11,12,19,3],![4,12,5,22,6]⟩
def cycle244_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle244_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle244_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,12,14]⟩
def data244 : PartitionData E W := ⟨5,![cycle244_0,cycle244_1,cycle244_2,cycle244_3,cycle244_4]⟩
lemma valid_data244 : data244.Valid src244 dst244 Finset.univ := by decide +kernel

def src245 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,22,13,6,14,7,22,15]
def dst245 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,22,13,4,14,7,22,15,6]
def cycle245_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle245_1 : CycleData E W := ⟨2,![10,7,19,3],![4,12,15,6]⟩
def cycle245_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle245_3 : CycleData E W := ⟨1,![13,18,6],![13,22,15]⟩
def cycle245_4 : CycleData E W := ⟨3,![12,17,16,8,11],![5,22,7,14,12]⟩
def data245 : PartitionData E W := ⟨5,![cycle245_0,cycle245_1,cycle245_2,cycle245_3,cycle245_4]⟩
lemma valid_data245 : data245.Valid src245 dst245 Finset.univ := by decide +kernel

def src246 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,22,13,6,14,22,7,15]
def dst246 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,22,13,4,14,22,7,15,6]
def cycle246_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle246_1 : CycleData E W := ⟨2,![10,7,19,3],![4,12,15,6]⟩
def cycle246_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle246_3 : CycleData E W := ⟨2,![18,6,13,17],![7,15,13,22]⟩
def cycle246_4 : CycleData E W := ⟨2,![12,16,8,11],![5,22,14,12]⟩
def data246 : PartitionData E W := ⟨5,![cycle246_0,cycle246_1,cycle246_2,cycle246_3,cycle246_4]⟩
lemma valid_data246 : data246.Valid src246 dst246 Finset.univ := by decide +kernel

def src247 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,5,22,13,6,15,7,14,22]
def dst247 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,5,22,13,4,15,7,14,22,6]
def cycle247_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,5]⟩
def cycle247_1 : CycleData E W := ⟨2,![14,6,16,2],![4,13,15,7]⟩
def cycle247_2 : CycleData E W := ⟨2,![10,7,15,3],![4,12,15,6]⟩
def cycle247_3 : CycleData E W := ⟨2,![5,13,19,4],![2,13,22,6]⟩
def cycle247_4 : CycleData E W := ⟨2,![12,18,8,11],![5,22,14,12]⟩
def data247 : PartitionData E W := ⟨5,![cycle247_0,cycle247_1,cycle247_2,cycle247_3,cycle247_4]⟩
lemma valid_data247 : data247.Valid src247 dst247 Finset.univ := by decide +kernel

def src248 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,22,5,13,6,14,7,15,22]
def dst248 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,22,5,13,4,14,7,15,22,6]
def cycle248_0 : CycleData E W := ⟨3,![5,14,2,1,0],![2,13,4,7,5]⟩
def cycle248_1 : CycleData E W := ⟨2,![10,11,19,3],![4,12,22,6]⟩
def cycle248_2 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle248_3 : CycleData E W := ⟨2,![13,6,18,12],![5,13,15,22]⟩
def cycle248_4 : CycleData E W := ⟨2,![17,7,8,16],![7,15,12,14]⟩
def data248 : PartitionData E W := ⟨5,![cycle248_0,cycle248_1,cycle248_2,cycle248_3,cycle248_4]⟩
lemma valid_data248 : data248.Valid src248 dst248 Finset.univ := by decide +kernel

def src249 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,22,5,13,6,14,7,22,15]
def dst249 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,22,5,13,4,14,7,22,15,6]
def cycle249_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle249_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle249_2 : CycleData E W := ⟨2,![10,8,16,2],![4,12,14,7]⟩
def cycle249_3 : CycleData E W := ⟨2,![14,6,19,3],![4,13,15,6]⟩
def cycle249_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle249_5 : CycleData E W := ⟨1,![11,18,7],![12,22,15]⟩
def data249 : PartitionData E W := ⟨6,![cycle249_0,cycle249_1,cycle249_2,cycle249_3,cycle249_4,cycle249_5]⟩
lemma valid_data249 : data249.Valid src249 dst249 Finset.univ := by decide +kernel

def src250 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,22,5,13,6,14,22,7,15]
def dst250 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,22,5,13,4,14,22,7,15,6]
def cycle250_0 : CycleData E W := ⟨1,![5,13,0],![2,13,5]⟩
def cycle250_1 : CycleData E W := ⟨1,![12,17,1],![5,22,7]⟩
def cycle250_2 : CycleData E W := ⟨2,![14,6,18,2],![4,13,15,7]⟩
def cycle250_3 : CycleData E W := ⟨2,![10,7,19,3],![4,12,15,6]⟩
def cycle250_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle250_5 : CycleData E W := ⟨1,![11,16,8],![12,22,14]⟩
def data250 : PartitionData E W := ⟨6,![cycle250_0,cycle250_1,cycle250_2,cycle250_3,cycle250_4,cycle250_5]⟩
lemma valid_data250 : data250.Valid src250 dst250 Finset.univ := by decide +kernel

def src251 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,12,22,5,13,6,15,7,14,22]
def dst251 : E → W := ![5,7,4,6,2,13,15,12,14,2,12,22,5,13,4,15,7,14,22,6]
def cycle251_0 : CycleData E W := ⟨2,![9,17,1,0],![2,14,7,5]⟩
def cycle251_1 : CycleData E W := ⟨2,![14,6,16,2],![4,13,15,7]⟩
def cycle251_2 : CycleData E W := ⟨2,![10,7,15,3],![4,12,15,6]⟩
def cycle251_3 : CycleData E W := ⟨3,![5,13,12,19,4],![2,13,5,22,6]⟩
def cycle251_4 : CycleData E W := ⟨1,![11,18,8],![12,22,14]⟩
def data251 : PartitionData E W := ⟨5,![cycle251_0,cycle251_1,cycle251_2,cycle251_3,cycle251_4]⟩
lemma valid_data251 : data251.Valid src251 dst251 Finset.univ := by decide +kernel

def src252 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,13,5,12,22,6,14,7,15,22]
def dst252 : E → W := ![5,7,4,6,2,13,15,12,14,2,13,5,12,22,4,14,7,15,22,6]
def cycle252_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle252_1 : CycleData E W := ⟨2,![12,8,16,1],![5,12,14,7]⟩
def cycle252_2 : CycleData E W := ⟨2,![10,6,17,2],![4,13,15,7]⟩
def cycle252_3 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle252_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle252_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data252 : PartitionData E W := ⟨6,![cycle252_0,cycle252_1,cycle252_2,cycle252_3,cycle252_4,cycle252_5]⟩
lemma valid_data252 : data252.Valid src252 dst252 Finset.univ := by decide +kernel

def src253 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,13,5,12,22,6,14,7,22,15]
def dst253 : E → W := ![5,7,4,6,2,13,15,12,14,2,13,5,12,22,4,14,7,22,15,6]
def cycle253_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle253_1 : CycleData E W := ⟨2,![12,8,16,1],![5,12,14,7]⟩
def cycle253_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle253_3 : CycleData E W := ⟨2,![10,6,19,3],![4,13,15,6]⟩
def cycle253_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle253_5 : CycleData E W := ⟨1,![13,18,7],![12,22,15]⟩
def data253 : PartitionData E W := ⟨6,![cycle253_0,cycle253_1,cycle253_2,cycle253_3,cycle253_4,cycle253_5]⟩
lemma valid_data253 : data253.Valid src253 dst253 Finset.univ := by decide +kernel

def src254 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,13,5,12,22,6,14,22,7,15]
def dst254 : E → W := ![5,7,4,6,2,13,15,12,14,2,13,5,12,22,4,14,22,7,15,6]
def cycle254_0 : CycleData E W := ⟨1,![5,11,0],![2,13,5]⟩
def cycle254_1 : CycleData E W := ⟨2,![12,7,18,1],![5,12,15,7]⟩
def cycle254_2 : CycleData E W := ⟨1,![14,17,2],![4,22,7]⟩
def cycle254_3 : CycleData E W := ⟨2,![10,6,19,3],![4,13,15,6]⟩
def cycle254_4 : CycleData E W := ⟨1,![9,15,4],![2,14,6]⟩
def cycle254_5 : CycleData E W := ⟨1,![13,16,8],![12,22,14]⟩
def data254 : PartitionData E W := ⟨6,![cycle254_0,cycle254_1,cycle254_2,cycle254_3,cycle254_4,cycle254_5]⟩
lemma valid_data254 : data254.Valid src254 dst254 Finset.univ := by decide +kernel

def src255 : E → W := ![2,5,7,4,6,2,13,15,12,14,4,13,5,12,22,6,15,7,14,22]
def dst255 : E → W := ![5,7,4,6,2,13,15,12,14,2,13,5,12,22,4,15,7,14,22,6]
def cycle255_0 : CycleData E W := ⟨3,![5,10,2,1,0],![2,13,4,7,5]⟩
def cycle255_1 : CycleData E W := ⟨1,![14,19,3],![4,22,6]⟩
def cycle255_2 : CycleData E W := ⟨3,![9,17,16,15,4],![2,14,7,15,6]⟩
def cycle255_3 : CycleData E W := ⟨2,![12,7,6,11],![5,12,15,13]⟩
def cycle255_4 : CycleData E W := ⟨1,![13,18,8],![12,22,14]⟩
def data255 : PartitionData E W := ⟨5,![cycle255_0,cycle255_1,cycle255_2,cycle255_3,cycle255_4]⟩
lemma valid_data255 : data255.Valid src255 dst255 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
  if k < 128 then
    if k < 64 then
      if k < 32 then
        if k < 16 then
          if k < 8 then
            if k < 4 then
              if k < 2 then
                if k < 1 then
                  data0
                else
                  data1
              else
                if k < 3 then
                  data2
                else
                  data3
            else
              if k < 6 then
                if k < 5 then
                  data4
                else
                  data5
              else
                if k < 7 then
                  data6
                else
                  data7
          else
            if k < 12 then
              if k < 10 then
                if k < 9 then
                  data8
                else
                  data9
              else
                if k < 11 then
                  data10
                else
                  data11
            else
              if k < 14 then
                if k < 13 then
                  data12
                else
                  data13
              else
                if k < 15 then
                  data14
                else
                  data15
        else
          if k < 24 then
            if k < 20 then
              if k < 18 then
                if k < 17 then
                  data16
                else
                  data17
              else
                if k < 19 then
                  data18
                else
                  data19
            else
              if k < 22 then
                if k < 21 then
                  data20
                else
                  data21
              else
                if k < 23 then
                  data22
                else
                  data23
          else
            if k < 28 then
              if k < 26 then
                if k < 25 then
                  data24
                else
                  data25
              else
                if k < 27 then
                  data26
                else
                  data27
            else
              if k < 30 then
                if k < 29 then
                  data28
                else
                  data29
              else
                if k < 31 then
                  data30
                else
                  data31
      else
        if k < 48 then
          if k < 40 then
            if k < 36 then
              if k < 34 then
                if k < 33 then
                  data32
                else
                  data33
              else
                if k < 35 then
                  data34
                else
                  data35
            else
              if k < 38 then
                if k < 37 then
                  data36
                else
                  data37
              else
                if k < 39 then
                  data38
                else
                  data39
          else
            if k < 44 then
              if k < 42 then
                if k < 41 then
                  data40
                else
                  data41
              else
                if k < 43 then
                  data42
                else
                  data43
            else
              if k < 46 then
                if k < 45 then
                  data44
                else
                  data45
              else
                if k < 47 then
                  data46
                else
                  data47
        else
          if k < 56 then
            if k < 52 then
              if k < 50 then
                if k < 49 then
                  data48
                else
                  data49
              else
                if k < 51 then
                  data50
                else
                  data51
            else
              if k < 54 then
                if k < 53 then
                  data52
                else
                  data53
              else
                if k < 55 then
                  data54
                else
                  data55
          else
            if k < 60 then
              if k < 58 then
                if k < 57 then
                  data56
                else
                  data57
              else
                if k < 59 then
                  data58
                else
                  data59
            else
              if k < 62 then
                if k < 61 then
                  data60
                else
                  data61
              else
                if k < 63 then
                  data62
                else
                  data63
    else
      if k < 96 then
        if k < 80 then
          if k < 72 then
            if k < 68 then
              if k < 66 then
                if k < 65 then
                  data64
                else
                  data65
              else
                if k < 67 then
                  data66
                else
                  data67
            else
              if k < 70 then
                if k < 69 then
                  data68
                else
                  data69
              else
                if k < 71 then
                  data70
                else
                  data71
          else
            if k < 76 then
              if k < 74 then
                if k < 73 then
                  data72
                else
                  data73
              else
                if k < 75 then
                  data74
                else
                  data75
            else
              if k < 78 then
                if k < 77 then
                  data76
                else
                  data77
              else
                if k < 79 then
                  data78
                else
                  data79
        else
          if k < 88 then
            if k < 84 then
              if k < 82 then
                if k < 81 then
                  data80
                else
                  data81
              else
                if k < 83 then
                  data82
                else
                  data83
            else
              if k < 86 then
                if k < 85 then
                  data84
                else
                  data85
              else
                if k < 87 then
                  data86
                else
                  data87
          else
            if k < 92 then
              if k < 90 then
                if k < 89 then
                  data88
                else
                  data89
              else
                if k < 91 then
                  data90
                else
                  data91
            else
              if k < 94 then
                if k < 93 then
                  data92
                else
                  data93
              else
                if k < 95 then
                  data94
                else
                  data95
      else
        if k < 112 then
          if k < 104 then
            if k < 100 then
              if k < 98 then
                if k < 97 then
                  data96
                else
                  data97
              else
                if k < 99 then
                  data98
                else
                  data99
            else
              if k < 102 then
                if k < 101 then
                  data100
                else
                  data101
              else
                if k < 103 then
                  data102
                else
                  data103
          else
            if k < 108 then
              if k < 106 then
                if k < 105 then
                  data104
                else
                  data105
              else
                if k < 107 then
                  data106
                else
                  data107
            else
              if k < 110 then
                if k < 109 then
                  data108
                else
                  data109
              else
                if k < 111 then
                  data110
                else
                  data111
        else
          if k < 120 then
            if k < 116 then
              if k < 114 then
                if k < 113 then
                  data112
                else
                  data113
              else
                if k < 115 then
                  data114
                else
                  data115
            else
              if k < 118 then
                if k < 117 then
                  data116
                else
                  data117
              else
                if k < 119 then
                  data118
                else
                  data119
          else
            if k < 124 then
              if k < 122 then
                if k < 121 then
                  data120
                else
                  data121
              else
                if k < 123 then
                  data122
                else
                  data123
            else
              if k < 126 then
                if k < 125 then
                  data124
                else
                  data125
              else
                if k < 127 then
                  data126
                else
                  data127
  else
    if k < 192 then
      if k < 160 then
        if k < 144 then
          if k < 136 then
            if k < 132 then
              if k < 130 then
                if k < 129 then
                  data128
                else
                  data129
              else
                if k < 131 then
                  data130
                else
                  data131
            else
              if k < 134 then
                if k < 133 then
                  data132
                else
                  data133
              else
                if k < 135 then
                  data134
                else
                  data135
          else
            if k < 140 then
              if k < 138 then
                if k < 137 then
                  data136
                else
                  data137
              else
                if k < 139 then
                  data138
                else
                  data139
            else
              if k < 142 then
                if k < 141 then
                  data140
                else
                  data141
              else
                if k < 143 then
                  data142
                else
                  data143
        else
          if k < 152 then
            if k < 148 then
              if k < 146 then
                if k < 145 then
                  data144
                else
                  data145
              else
                if k < 147 then
                  data146
                else
                  data147
            else
              if k < 150 then
                if k < 149 then
                  data148
                else
                  data149
              else
                if k < 151 then
                  data150
                else
                  data151
          else
            if k < 156 then
              if k < 154 then
                if k < 153 then
                  data152
                else
                  data153
              else
                if k < 155 then
                  data154
                else
                  data155
            else
              if k < 158 then
                if k < 157 then
                  data156
                else
                  data157
              else
                if k < 159 then
                  data158
                else
                  data159
      else
        if k < 176 then
          if k < 168 then
            if k < 164 then
              if k < 162 then
                if k < 161 then
                  data160
                else
                  data161
              else
                if k < 163 then
                  data162
                else
                  data163
            else
              if k < 166 then
                if k < 165 then
                  data164
                else
                  data165
              else
                if k < 167 then
                  data166
                else
                  data167
          else
            if k < 172 then
              if k < 170 then
                if k < 169 then
                  data168
                else
                  data169
              else
                if k < 171 then
                  data170
                else
                  data171
            else
              if k < 174 then
                if k < 173 then
                  data172
                else
                  data173
              else
                if k < 175 then
                  data174
                else
                  data175
        else
          if k < 184 then
            if k < 180 then
              if k < 178 then
                if k < 177 then
                  data176
                else
                  data177
              else
                if k < 179 then
                  data178
                else
                  data179
            else
              if k < 182 then
                if k < 181 then
                  data180
                else
                  data181
              else
                if k < 183 then
                  data182
                else
                  data183
          else
            if k < 188 then
              if k < 186 then
                if k < 185 then
                  data184
                else
                  data185
              else
                if k < 187 then
                  data186
                else
                  data187
            else
              if k < 190 then
                if k < 189 then
                  data188
                else
                  data189
              else
                if k < 191 then
                  data190
                else
                  data191
    else
      if k < 224 then
        if k < 208 then
          if k < 200 then
            if k < 196 then
              if k < 194 then
                if k < 193 then
                  data192
                else
                  data193
              else
                if k < 195 then
                  data194
                else
                  data195
            else
              if k < 198 then
                if k < 197 then
                  data196
                else
                  data197
              else
                if k < 199 then
                  data198
                else
                  data199
          else
            if k < 204 then
              if k < 202 then
                if k < 201 then
                  data200
                else
                  data201
              else
                if k < 203 then
                  data202
                else
                  data203
            else
              if k < 206 then
                if k < 205 then
                  data204
                else
                  data205
              else
                if k < 207 then
                  data206
                else
                  data207
        else
          if k < 216 then
            if k < 212 then
              if k < 210 then
                if k < 209 then
                  data208
                else
                  data209
              else
                if k < 211 then
                  data210
                else
                  data211
            else
              if k < 214 then
                if k < 213 then
                  data212
                else
                  data213
              else
                if k < 215 then
                  data214
                else
                  data215
          else
            if k < 220 then
              if k < 218 then
                if k < 217 then
                  data216
                else
                  data217
              else
                if k < 219 then
                  data218
                else
                  data219
            else
              if k < 222 then
                if k < 221 then
                  data220
                else
                  data221
              else
                if k < 223 then
                  data222
                else
                  data223
      else
        if k < 240 then
          if k < 232 then
            if k < 228 then
              if k < 226 then
                if k < 225 then
                  data224
                else
                  data225
              else
                if k < 227 then
                  data226
                else
                  data227
            else
              if k < 230 then
                if k < 229 then
                  data228
                else
                  data229
              else
                if k < 231 then
                  data230
                else
                  data231
          else
            if k < 236 then
              if k < 234 then
                if k < 233 then
                  data232
                else
                  data233
              else
                if k < 235 then
                  data234
                else
                  data235
            else
              if k < 238 then
                if k < 237 then
                  data236
                else
                  data237
              else
                if k < 239 then
                  data238
                else
                  data239
        else
          if k < 248 then
            if k < 244 then
              if k < 242 then
                if k < 241 then
                  data240
                else
                  data241
              else
                if k < 243 then
                  data242
                else
                  data243
            else
              if k < 246 then
                if k < 245 then
                  data244
                else
                  data245
              else
                if k < 247 then
                  data246
                else
                  data247
          else
            if k < 252 then
              if k < 250 then
                if k < 249 then
                  data248
                else
                  data249
              else
                if k < 251 then
                  data250
                else
                  data251
            else
              if k < 254 then
                if k < 253 then
                  data252
                else
                  data253
              else
                if k < 255 then
                  data254
                else
                  data255

def srcTable (k : ℕ) : E → W :=
  if k < 128 then
    if k < 64 then
      if k < 32 then
        if k < 16 then
          if k < 8 then
            if k < 4 then
              if k < 2 then
                if k < 1 then
                  src0
                else
                  src1
              else
                if k < 3 then
                  src2
                else
                  src3
            else
              if k < 6 then
                if k < 5 then
                  src4
                else
                  src5
              else
                if k < 7 then
                  src6
                else
                  src7
          else
            if k < 12 then
              if k < 10 then
                if k < 9 then
                  src8
                else
                  src9
              else
                if k < 11 then
                  src10
                else
                  src11
            else
              if k < 14 then
                if k < 13 then
                  src12
                else
                  src13
              else
                if k < 15 then
                  src14
                else
                  src15
        else
          if k < 24 then
            if k < 20 then
              if k < 18 then
                if k < 17 then
                  src16
                else
                  src17
              else
                if k < 19 then
                  src18
                else
                  src19
            else
              if k < 22 then
                if k < 21 then
                  src20
                else
                  src21
              else
                if k < 23 then
                  src22
                else
                  src23
          else
            if k < 28 then
              if k < 26 then
                if k < 25 then
                  src24
                else
                  src25
              else
                if k < 27 then
                  src26
                else
                  src27
            else
              if k < 30 then
                if k < 29 then
                  src28
                else
                  src29
              else
                if k < 31 then
                  src30
                else
                  src31
      else
        if k < 48 then
          if k < 40 then
            if k < 36 then
              if k < 34 then
                if k < 33 then
                  src32
                else
                  src33
              else
                if k < 35 then
                  src34
                else
                  src35
            else
              if k < 38 then
                if k < 37 then
                  src36
                else
                  src37
              else
                if k < 39 then
                  src38
                else
                  src39
          else
            if k < 44 then
              if k < 42 then
                if k < 41 then
                  src40
                else
                  src41
              else
                if k < 43 then
                  src42
                else
                  src43
            else
              if k < 46 then
                if k < 45 then
                  src44
                else
                  src45
              else
                if k < 47 then
                  src46
                else
                  src47
        else
          if k < 56 then
            if k < 52 then
              if k < 50 then
                if k < 49 then
                  src48
                else
                  src49
              else
                if k < 51 then
                  src50
                else
                  src51
            else
              if k < 54 then
                if k < 53 then
                  src52
                else
                  src53
              else
                if k < 55 then
                  src54
                else
                  src55
          else
            if k < 60 then
              if k < 58 then
                if k < 57 then
                  src56
                else
                  src57
              else
                if k < 59 then
                  src58
                else
                  src59
            else
              if k < 62 then
                if k < 61 then
                  src60
                else
                  src61
              else
                if k < 63 then
                  src62
                else
                  src63
    else
      if k < 96 then
        if k < 80 then
          if k < 72 then
            if k < 68 then
              if k < 66 then
                if k < 65 then
                  src64
                else
                  src65
              else
                if k < 67 then
                  src66
                else
                  src67
            else
              if k < 70 then
                if k < 69 then
                  src68
                else
                  src69
              else
                if k < 71 then
                  src70
                else
                  src71
          else
            if k < 76 then
              if k < 74 then
                if k < 73 then
                  src72
                else
                  src73
              else
                if k < 75 then
                  src74
                else
                  src75
            else
              if k < 78 then
                if k < 77 then
                  src76
                else
                  src77
              else
                if k < 79 then
                  src78
                else
                  src79
        else
          if k < 88 then
            if k < 84 then
              if k < 82 then
                if k < 81 then
                  src80
                else
                  src81
              else
                if k < 83 then
                  src82
                else
                  src83
            else
              if k < 86 then
                if k < 85 then
                  src84
                else
                  src85
              else
                if k < 87 then
                  src86
                else
                  src87
          else
            if k < 92 then
              if k < 90 then
                if k < 89 then
                  src88
                else
                  src89
              else
                if k < 91 then
                  src90
                else
                  src91
            else
              if k < 94 then
                if k < 93 then
                  src92
                else
                  src93
              else
                if k < 95 then
                  src94
                else
                  src95
      else
        if k < 112 then
          if k < 104 then
            if k < 100 then
              if k < 98 then
                if k < 97 then
                  src96
                else
                  src97
              else
                if k < 99 then
                  src98
                else
                  src99
            else
              if k < 102 then
                if k < 101 then
                  src100
                else
                  src101
              else
                if k < 103 then
                  src102
                else
                  src103
          else
            if k < 108 then
              if k < 106 then
                if k < 105 then
                  src104
                else
                  src105
              else
                if k < 107 then
                  src106
                else
                  src107
            else
              if k < 110 then
                if k < 109 then
                  src108
                else
                  src109
              else
                if k < 111 then
                  src110
                else
                  src111
        else
          if k < 120 then
            if k < 116 then
              if k < 114 then
                if k < 113 then
                  src112
                else
                  src113
              else
                if k < 115 then
                  src114
                else
                  src115
            else
              if k < 118 then
                if k < 117 then
                  src116
                else
                  src117
              else
                if k < 119 then
                  src118
                else
                  src119
          else
            if k < 124 then
              if k < 122 then
                if k < 121 then
                  src120
                else
                  src121
              else
                if k < 123 then
                  src122
                else
                  src123
            else
              if k < 126 then
                if k < 125 then
                  src124
                else
                  src125
              else
                if k < 127 then
                  src126
                else
                  src127
  else
    if k < 192 then
      if k < 160 then
        if k < 144 then
          if k < 136 then
            if k < 132 then
              if k < 130 then
                if k < 129 then
                  src128
                else
                  src129
              else
                if k < 131 then
                  src130
                else
                  src131
            else
              if k < 134 then
                if k < 133 then
                  src132
                else
                  src133
              else
                if k < 135 then
                  src134
                else
                  src135
          else
            if k < 140 then
              if k < 138 then
                if k < 137 then
                  src136
                else
                  src137
              else
                if k < 139 then
                  src138
                else
                  src139
            else
              if k < 142 then
                if k < 141 then
                  src140
                else
                  src141
              else
                if k < 143 then
                  src142
                else
                  src143
        else
          if k < 152 then
            if k < 148 then
              if k < 146 then
                if k < 145 then
                  src144
                else
                  src145
              else
                if k < 147 then
                  src146
                else
                  src147
            else
              if k < 150 then
                if k < 149 then
                  src148
                else
                  src149
              else
                if k < 151 then
                  src150
                else
                  src151
          else
            if k < 156 then
              if k < 154 then
                if k < 153 then
                  src152
                else
                  src153
              else
                if k < 155 then
                  src154
                else
                  src155
            else
              if k < 158 then
                if k < 157 then
                  src156
                else
                  src157
              else
                if k < 159 then
                  src158
                else
                  src159
      else
        if k < 176 then
          if k < 168 then
            if k < 164 then
              if k < 162 then
                if k < 161 then
                  src160
                else
                  src161
              else
                if k < 163 then
                  src162
                else
                  src163
            else
              if k < 166 then
                if k < 165 then
                  src164
                else
                  src165
              else
                if k < 167 then
                  src166
                else
                  src167
          else
            if k < 172 then
              if k < 170 then
                if k < 169 then
                  src168
                else
                  src169
              else
                if k < 171 then
                  src170
                else
                  src171
            else
              if k < 174 then
                if k < 173 then
                  src172
                else
                  src173
              else
                if k < 175 then
                  src174
                else
                  src175
        else
          if k < 184 then
            if k < 180 then
              if k < 178 then
                if k < 177 then
                  src176
                else
                  src177
              else
                if k < 179 then
                  src178
                else
                  src179
            else
              if k < 182 then
                if k < 181 then
                  src180
                else
                  src181
              else
                if k < 183 then
                  src182
                else
                  src183
          else
            if k < 188 then
              if k < 186 then
                if k < 185 then
                  src184
                else
                  src185
              else
                if k < 187 then
                  src186
                else
                  src187
            else
              if k < 190 then
                if k < 189 then
                  src188
                else
                  src189
              else
                if k < 191 then
                  src190
                else
                  src191
    else
      if k < 224 then
        if k < 208 then
          if k < 200 then
            if k < 196 then
              if k < 194 then
                if k < 193 then
                  src192
                else
                  src193
              else
                if k < 195 then
                  src194
                else
                  src195
            else
              if k < 198 then
                if k < 197 then
                  src196
                else
                  src197
              else
                if k < 199 then
                  src198
                else
                  src199
          else
            if k < 204 then
              if k < 202 then
                if k < 201 then
                  src200
                else
                  src201
              else
                if k < 203 then
                  src202
                else
                  src203
            else
              if k < 206 then
                if k < 205 then
                  src204
                else
                  src205
              else
                if k < 207 then
                  src206
                else
                  src207
        else
          if k < 216 then
            if k < 212 then
              if k < 210 then
                if k < 209 then
                  src208
                else
                  src209
              else
                if k < 211 then
                  src210
                else
                  src211
            else
              if k < 214 then
                if k < 213 then
                  src212
                else
                  src213
              else
                if k < 215 then
                  src214
                else
                  src215
          else
            if k < 220 then
              if k < 218 then
                if k < 217 then
                  src216
                else
                  src217
              else
                if k < 219 then
                  src218
                else
                  src219
            else
              if k < 222 then
                if k < 221 then
                  src220
                else
                  src221
              else
                if k < 223 then
                  src222
                else
                  src223
      else
        if k < 240 then
          if k < 232 then
            if k < 228 then
              if k < 226 then
                if k < 225 then
                  src224
                else
                  src225
              else
                if k < 227 then
                  src226
                else
                  src227
            else
              if k < 230 then
                if k < 229 then
                  src228
                else
                  src229
              else
                if k < 231 then
                  src230
                else
                  src231
          else
            if k < 236 then
              if k < 234 then
                if k < 233 then
                  src232
                else
                  src233
              else
                if k < 235 then
                  src234
                else
                  src235
            else
              if k < 238 then
                if k < 237 then
                  src236
                else
                  src237
              else
                if k < 239 then
                  src238
                else
                  src239
        else
          if k < 248 then
            if k < 244 then
              if k < 242 then
                if k < 241 then
                  src240
                else
                  src241
              else
                if k < 243 then
                  src242
                else
                  src243
            else
              if k < 246 then
                if k < 245 then
                  src244
                else
                  src245
              else
                if k < 247 then
                  src246
                else
                  src247
          else
            if k < 252 then
              if k < 250 then
                if k < 249 then
                  src248
                else
                  src249
              else
                if k < 251 then
                  src250
                else
                  src251
            else
              if k < 254 then
                if k < 253 then
                  src252
                else
                  src253
              else
                if k < 255 then
                  src254
                else
                  src255

def dstTable (k : ℕ) : E → W :=
  if k < 128 then
    if k < 64 then
      if k < 32 then
        if k < 16 then
          if k < 8 then
            if k < 4 then
              if k < 2 then
                if k < 1 then
                  dst0
                else
                  dst1
              else
                if k < 3 then
                  dst2
                else
                  dst3
            else
              if k < 6 then
                if k < 5 then
                  dst4
                else
                  dst5
              else
                if k < 7 then
                  dst6
                else
                  dst7
          else
            if k < 12 then
              if k < 10 then
                if k < 9 then
                  dst8
                else
                  dst9
              else
                if k < 11 then
                  dst10
                else
                  dst11
            else
              if k < 14 then
                if k < 13 then
                  dst12
                else
                  dst13
              else
                if k < 15 then
                  dst14
                else
                  dst15
        else
          if k < 24 then
            if k < 20 then
              if k < 18 then
                if k < 17 then
                  dst16
                else
                  dst17
              else
                if k < 19 then
                  dst18
                else
                  dst19
            else
              if k < 22 then
                if k < 21 then
                  dst20
                else
                  dst21
              else
                if k < 23 then
                  dst22
                else
                  dst23
          else
            if k < 28 then
              if k < 26 then
                if k < 25 then
                  dst24
                else
                  dst25
              else
                if k < 27 then
                  dst26
                else
                  dst27
            else
              if k < 30 then
                if k < 29 then
                  dst28
                else
                  dst29
              else
                if k < 31 then
                  dst30
                else
                  dst31
      else
        if k < 48 then
          if k < 40 then
            if k < 36 then
              if k < 34 then
                if k < 33 then
                  dst32
                else
                  dst33
              else
                if k < 35 then
                  dst34
                else
                  dst35
            else
              if k < 38 then
                if k < 37 then
                  dst36
                else
                  dst37
              else
                if k < 39 then
                  dst38
                else
                  dst39
          else
            if k < 44 then
              if k < 42 then
                if k < 41 then
                  dst40
                else
                  dst41
              else
                if k < 43 then
                  dst42
                else
                  dst43
            else
              if k < 46 then
                if k < 45 then
                  dst44
                else
                  dst45
              else
                if k < 47 then
                  dst46
                else
                  dst47
        else
          if k < 56 then
            if k < 52 then
              if k < 50 then
                if k < 49 then
                  dst48
                else
                  dst49
              else
                if k < 51 then
                  dst50
                else
                  dst51
            else
              if k < 54 then
                if k < 53 then
                  dst52
                else
                  dst53
              else
                if k < 55 then
                  dst54
                else
                  dst55
          else
            if k < 60 then
              if k < 58 then
                if k < 57 then
                  dst56
                else
                  dst57
              else
                if k < 59 then
                  dst58
                else
                  dst59
            else
              if k < 62 then
                if k < 61 then
                  dst60
                else
                  dst61
              else
                if k < 63 then
                  dst62
                else
                  dst63
    else
      if k < 96 then
        if k < 80 then
          if k < 72 then
            if k < 68 then
              if k < 66 then
                if k < 65 then
                  dst64
                else
                  dst65
              else
                if k < 67 then
                  dst66
                else
                  dst67
            else
              if k < 70 then
                if k < 69 then
                  dst68
                else
                  dst69
              else
                if k < 71 then
                  dst70
                else
                  dst71
          else
            if k < 76 then
              if k < 74 then
                if k < 73 then
                  dst72
                else
                  dst73
              else
                if k < 75 then
                  dst74
                else
                  dst75
            else
              if k < 78 then
                if k < 77 then
                  dst76
                else
                  dst77
              else
                if k < 79 then
                  dst78
                else
                  dst79
        else
          if k < 88 then
            if k < 84 then
              if k < 82 then
                if k < 81 then
                  dst80
                else
                  dst81
              else
                if k < 83 then
                  dst82
                else
                  dst83
            else
              if k < 86 then
                if k < 85 then
                  dst84
                else
                  dst85
              else
                if k < 87 then
                  dst86
                else
                  dst87
          else
            if k < 92 then
              if k < 90 then
                if k < 89 then
                  dst88
                else
                  dst89
              else
                if k < 91 then
                  dst90
                else
                  dst91
            else
              if k < 94 then
                if k < 93 then
                  dst92
                else
                  dst93
              else
                if k < 95 then
                  dst94
                else
                  dst95
      else
        if k < 112 then
          if k < 104 then
            if k < 100 then
              if k < 98 then
                if k < 97 then
                  dst96
                else
                  dst97
              else
                if k < 99 then
                  dst98
                else
                  dst99
            else
              if k < 102 then
                if k < 101 then
                  dst100
                else
                  dst101
              else
                if k < 103 then
                  dst102
                else
                  dst103
          else
            if k < 108 then
              if k < 106 then
                if k < 105 then
                  dst104
                else
                  dst105
              else
                if k < 107 then
                  dst106
                else
                  dst107
            else
              if k < 110 then
                if k < 109 then
                  dst108
                else
                  dst109
              else
                if k < 111 then
                  dst110
                else
                  dst111
        else
          if k < 120 then
            if k < 116 then
              if k < 114 then
                if k < 113 then
                  dst112
                else
                  dst113
              else
                if k < 115 then
                  dst114
                else
                  dst115
            else
              if k < 118 then
                if k < 117 then
                  dst116
                else
                  dst117
              else
                if k < 119 then
                  dst118
                else
                  dst119
          else
            if k < 124 then
              if k < 122 then
                if k < 121 then
                  dst120
                else
                  dst121
              else
                if k < 123 then
                  dst122
                else
                  dst123
            else
              if k < 126 then
                if k < 125 then
                  dst124
                else
                  dst125
              else
                if k < 127 then
                  dst126
                else
                  dst127
  else
    if k < 192 then
      if k < 160 then
        if k < 144 then
          if k < 136 then
            if k < 132 then
              if k < 130 then
                if k < 129 then
                  dst128
                else
                  dst129
              else
                if k < 131 then
                  dst130
                else
                  dst131
            else
              if k < 134 then
                if k < 133 then
                  dst132
                else
                  dst133
              else
                if k < 135 then
                  dst134
                else
                  dst135
          else
            if k < 140 then
              if k < 138 then
                if k < 137 then
                  dst136
                else
                  dst137
              else
                if k < 139 then
                  dst138
                else
                  dst139
            else
              if k < 142 then
                if k < 141 then
                  dst140
                else
                  dst141
              else
                if k < 143 then
                  dst142
                else
                  dst143
        else
          if k < 152 then
            if k < 148 then
              if k < 146 then
                if k < 145 then
                  dst144
                else
                  dst145
              else
                if k < 147 then
                  dst146
                else
                  dst147
            else
              if k < 150 then
                if k < 149 then
                  dst148
                else
                  dst149
              else
                if k < 151 then
                  dst150
                else
                  dst151
          else
            if k < 156 then
              if k < 154 then
                if k < 153 then
                  dst152
                else
                  dst153
              else
                if k < 155 then
                  dst154
                else
                  dst155
            else
              if k < 158 then
                if k < 157 then
                  dst156
                else
                  dst157
              else
                if k < 159 then
                  dst158
                else
                  dst159
      else
        if k < 176 then
          if k < 168 then
            if k < 164 then
              if k < 162 then
                if k < 161 then
                  dst160
                else
                  dst161
              else
                if k < 163 then
                  dst162
                else
                  dst163
            else
              if k < 166 then
                if k < 165 then
                  dst164
                else
                  dst165
              else
                if k < 167 then
                  dst166
                else
                  dst167
          else
            if k < 172 then
              if k < 170 then
                if k < 169 then
                  dst168
                else
                  dst169
              else
                if k < 171 then
                  dst170
                else
                  dst171
            else
              if k < 174 then
                if k < 173 then
                  dst172
                else
                  dst173
              else
                if k < 175 then
                  dst174
                else
                  dst175
        else
          if k < 184 then
            if k < 180 then
              if k < 178 then
                if k < 177 then
                  dst176
                else
                  dst177
              else
                if k < 179 then
                  dst178
                else
                  dst179
            else
              if k < 182 then
                if k < 181 then
                  dst180
                else
                  dst181
              else
                if k < 183 then
                  dst182
                else
                  dst183
          else
            if k < 188 then
              if k < 186 then
                if k < 185 then
                  dst184
                else
                  dst185
              else
                if k < 187 then
                  dst186
                else
                  dst187
            else
              if k < 190 then
                if k < 189 then
                  dst188
                else
                  dst189
              else
                if k < 191 then
                  dst190
                else
                  dst191
    else
      if k < 224 then
        if k < 208 then
          if k < 200 then
            if k < 196 then
              if k < 194 then
                if k < 193 then
                  dst192
                else
                  dst193
              else
                if k < 195 then
                  dst194
                else
                  dst195
            else
              if k < 198 then
                if k < 197 then
                  dst196
                else
                  dst197
              else
                if k < 199 then
                  dst198
                else
                  dst199
          else
            if k < 204 then
              if k < 202 then
                if k < 201 then
                  dst200
                else
                  dst201
              else
                if k < 203 then
                  dst202
                else
                  dst203
            else
              if k < 206 then
                if k < 205 then
                  dst204
                else
                  dst205
              else
                if k < 207 then
                  dst206
                else
                  dst207
        else
          if k < 216 then
            if k < 212 then
              if k < 210 then
                if k < 209 then
                  dst208
                else
                  dst209
              else
                if k < 211 then
                  dst210
                else
                  dst211
            else
              if k < 214 then
                if k < 213 then
                  dst212
                else
                  dst213
              else
                if k < 215 then
                  dst214
                else
                  dst215
          else
            if k < 220 then
              if k < 218 then
                if k < 217 then
                  dst216
                else
                  dst217
              else
                if k < 219 then
                  dst218
                else
                  dst219
            else
              if k < 222 then
                if k < 221 then
                  dst220
                else
                  dst221
              else
                if k < 223 then
                  dst222
                else
                  dst223
      else
        if k < 240 then
          if k < 232 then
            if k < 228 then
              if k < 226 then
                if k < 225 then
                  dst224
                else
                  dst225
              else
                if k < 227 then
                  dst226
                else
                  dst227
            else
              if k < 230 then
                if k < 229 then
                  dst228
                else
                  dst229
              else
                if k < 231 then
                  dst230
                else
                  dst231
          else
            if k < 236 then
              if k < 234 then
                if k < 233 then
                  dst232
                else
                  dst233
              else
                if k < 235 then
                  dst234
                else
                  dst235
            else
              if k < 238 then
                if k < 237 then
                  dst236
                else
                  dst237
              else
                if k < 239 then
                  dst238
                else
                  dst239
        else
          if k < 248 then
            if k < 244 then
              if k < 242 then
                if k < 241 then
                  dst240
                else
                  dst241
              else
                if k < 243 then
                  dst242
                else
                  dst243
            else
              if k < 246 then
                if k < 245 then
                  dst244
                else
                  dst245
              else
                if k < 247 then
                  dst246
                else
                  dst247
          else
            if k < 252 then
              if k < 250 then
                if k < 249 then
                  dst248
                else
                  dst249
              else
                if k < 251 then
                  dst250
                else
                  dst251
            else
              if k < 254 then
                if k < 253 then
                  dst252
                else
                  dst253
              else
                if k < 255 then
                  dst254
                else
                  dst255

lemma table_valid (k : Fin 256) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
  fin_cases k
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
  · exact valid_data200
  · exact valid_data201
  · exact valid_data202
  · exact valid_data203
  · exact valid_data204
  · exact valid_data205
  · exact valid_data206
  · exact valid_data207
  · exact valid_data208
  · exact valid_data209
  · exact valid_data210
  · exact valid_data211
  · exact valid_data212
  · exact valid_data213
  · exact valid_data214
  · exact valid_data215
  · exact valid_data216
  · exact valid_data217
  · exact valid_data218
  · exact valid_data219
  · exact valid_data220
  · exact valid_data221
  · exact valid_data222
  · exact valid_data223
  · exact valid_data224
  · exact valid_data225
  · exact valid_data226
  · exact valid_data227
  · exact valid_data228
  · exact valid_data229
  · exact valid_data230
  · exact valid_data231
  · exact valid_data232
  · exact valid_data233
  · exact valid_data234
  · exact valid_data235
  · exact valid_data236
  · exact valid_data237
  · exact valid_data238
  · exact valid_data239
  · exact valid_data240
  · exact valid_data241
  · exact valid_data242
  · exact valid_data243
  · exact valid_data244
  · exact valid_data245
  · exact valid_data246
  · exact valid_data247
  · exact valid_data248
  · exact valid_data249
  · exact valid_data250
  · exact valid_data251
  · exact valid_data252
  · exact valid_data253
  · exact valid_data254
  · exact valid_data255

lemma src_table_row : ∀ (k : Fin 256) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 256) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 256) := ∅
lemma size_mem : ∀ k : Fin 256, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 256, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows8

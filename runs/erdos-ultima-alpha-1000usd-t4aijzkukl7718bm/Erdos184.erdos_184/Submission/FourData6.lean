import Submission.FourRows6

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows6
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,7,2,12,13,14,4,12,13,22,6,7,14,22]
def dst0 : E → W := ![4,6,7,2,12,13,14,2,12,13,22,4,7,14,22,6]
def cycle0_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle0_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle0_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle0_3 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle0_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle0_5 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data0 : PartitionData E W := ⟨6,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,6,7,2,12,13,14,4,12,13,22,6,7,22,14]
def dst1 : E → W := ![4,6,7,2,12,13,14,2,12,13,22,4,7,22,14,6]
def cycle1_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle1_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle1_2 : CycleData E W := ⟨3,![4,8,11,13,3],![2,12,4,22,7]⟩
def cycle1_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle1_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data1 : PartitionData E W := ⟨5,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,6,7,2,12,13,14,4,12,13,22,6,14,7,22]
def dst2 : E → W := ![4,6,7,2,12,13,14,2,12,13,22,4,14,7,22,6]
def cycle2_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle2_1 : CycleData E W := ⟨2,![11,14,2,1],![4,22,7,6]⟩
def cycle2_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle2_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle2_4 : CycleData E W := ⟨2,![15,10,6,12],![6,22,13,14]⟩
def data2 : PartitionData E W := ⟨5,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,6,7,14,22]
def dst3 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,4,7,14,22,6]
def cycle3_0 : CycleData E W := ⟨3,![4,9,15,1,0],![2,12,22,6,4]⟩
def cycle3_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle3_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle3_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle3_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data3 : PartitionData E W := ⟨5,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,6,7,22,14]
def dst4 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,4,7,22,14,6]
def cycle4_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle4_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle4_2 : CycleData E W := ⟨2,![4,9,13,3],![2,12,22,7]⟩
def cycle4_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle4_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data4 : PartitionData E W := ⟨5,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,6,14,7,22]
def dst5 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,4,14,7,22,6]
def cycle5_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle5_1 : CycleData E W := ⟨2,![11,6,12,1],![4,13,14,6]⟩
def cycle5_2 : CycleData E W := ⟨1,![15,14,2],![6,22,7]⟩
def cycle5_3 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle5_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def data5 : PartitionData E W := ⟨5,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,6,7,2,12,13,14,4,13,12,22,6,7,14,22]
def dst6 : E → W := ![4,6,7,2,12,13,14,2,13,12,22,4,7,14,22,6]
def cycle6_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,12,22,6,4]⟩
def cycle6_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle6_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle6_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle6_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,13]⟩
def data6 : PartitionData E W := ⟨5,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,6,7,2,12,13,14,4,13,12,22,6,7,22,14]
def dst7 : E → W := ![4,6,7,2,12,13,14,2,13,12,22,4,7,22,14,6]
def cycle7_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle7_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle7_2 : CycleData E W := ⟨2,![4,10,13,3],![2,12,22,7]⟩
def cycle7_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle7_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,13]⟩
def data7 : PartitionData E W := ⟨5,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,6,7,2,12,13,14,4,13,12,22,6,14,7,22]
def dst8 : E → W := ![4,6,7,2,12,13,14,2,13,12,22,4,14,7,22,6]
def cycle8_0 : CycleData E W := ⟨2,![7,6,8,0],![2,14,13,4]⟩
def cycle8_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle8_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle8_3 : CycleData E W := ⟨2,![4,10,14,3],![2,12,22,7]⟩
def cycle8_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data8 : PartitionData E W := ⟨5,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,6,7,2,12,14,13,4,12,13,22,6,7,14,22]
def dst9 : E → W := ![4,6,7,2,12,14,13,2,12,13,22,4,7,14,22,6]
def cycle9_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle9_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle9_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle9_3 : CycleData E W := ⟨3,![7,9,5,13,3],![2,13,12,14,7]⟩
def cycle9_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data9 : PartitionData E W := ⟨5,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,6,7,2,12,14,13,4,12,13,22,6,7,22,14]
def dst10 : E → W := ![4,6,7,2,12,14,13,2,12,13,22,4,7,22,14,6]
def cycle10_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle10_1 : CycleData E W := ⟨2,![11,14,15,1],![4,22,14,6]⟩
def cycle10_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle10_3 : CycleData E W := ⟨2,![7,10,13,3],![2,13,22,7]⟩
def cycle10_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data10 : PartitionData E W := ⟨5,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,6,7,2,12,14,13,4,12,13,22,6,14,7,22]
def dst11 : E → W := ![4,6,7,2,12,14,13,2,12,13,22,4,14,7,22,6]
def cycle11_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle11_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle11_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle11_3 : CycleData E W := ⟨2,![7,10,14,3],![2,13,22,7]⟩
def cycle11_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data11 : PartitionData E W := ⟨5,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,6,7,14,22]
def dst12 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,4,7,14,22,6]
def cycle12_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle12_1 : CycleData E W := ⟨2,![11,10,15,1],![4,13,22,6]⟩
def cycle12_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle12_3 : CycleData E W := ⟨2,![7,6,13,3],![2,13,14,7]⟩
def cycle12_4 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def data12 : PartitionData E W := ⟨5,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,6,7,22,14]
def dst13 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,4,7,22,14,6]
def cycle13_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle13_1 : CycleData E W := ⟨2,![11,6,15,1],![4,13,14,6]⟩
def cycle13_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle13_3 : CycleData E W := ⟨2,![7,10,13,3],![2,13,22,7]⟩
def cycle13_4 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def data13 : PartitionData E W := ⟨5,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,6,14,7,22]
def dst14 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,4,14,7,22,6]
def cycle14_0 : CycleData E W := ⟨6,![7,10,9,5,13,2,1,0],![2,13,22,12,14,7,6,4]⟩
def cycle14_1 : CycleData E W := ⟨6,![4,8,11,6,12,15,14,3],![2,12,4,13,14,6,22,7]⟩
def data14 : PartitionData E W := ⟨2,![cycle14_0,cycle14_1]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,6,7,2,12,14,13,4,13,12,22,6,7,14,22]
def dst15 : E → W := ![4,6,7,2,12,14,13,2,13,12,22,4,7,14,22,6]
def cycle15_0 : CycleData E W := ⟨3,![3,13,6,8,0],![2,7,14,13,4]⟩
def cycle15_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle15_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle15_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle15_4 : CycleData E W := ⟨1,![10,14,5],![12,22,14]⟩
def data15 : PartitionData E W := ⟨5,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,6,7,2,12,14,13,4,13,12,22,6,7,22,14]
def dst16 : E → W := ![4,6,7,2,12,14,13,2,13,12,22,4,7,22,14,6]
def cycle16_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle16_1 : CycleData E W := ⟨2,![11,14,15,1],![4,22,14,6]⟩
def cycle16_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle16_3 : CycleData E W := ⟨2,![4,10,13,3],![2,12,22,7]⟩
def cycle16_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data16 : PartitionData E W := ⟨5,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,6,7,2,12,14,13,4,13,12,22,6,14,7,22]
def dst17 : E → W := ![4,6,7,2,12,14,13,2,13,12,22,4,14,7,22,6]
def cycle17_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle17_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle17_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle17_3 : CycleData E W := ⟨2,![4,10,14,3],![2,12,22,7]⟩
def cycle17_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data17 : PartitionData E W := ⟨5,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,6,7,2,13,12,14,4,12,13,22,6,7,14,22]
def dst18 : E → W := ![4,6,7,2,13,12,14,2,12,13,22,4,7,14,22,6]
def cycle18_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,13,22,6,4]⟩
def cycle18_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle18_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle18_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle18_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,12]⟩
def data18 : PartitionData E W := ⟨5,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,6,7,2,13,12,14,4,12,13,22,6,7,22,14]
def dst19 : E → W := ![4,6,7,2,13,12,14,2,12,13,22,4,7,22,14,6]
def cycle19_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle19_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle19_2 : CycleData E W := ⟨2,![4,10,13,3],![2,13,22,7]⟩
def cycle19_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle19_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,12]⟩
def data19 : PartitionData E W := ⟨5,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,6,7,2,13,12,14,4,12,13,22,6,14,7,22]
def dst20 : E → W := ![4,6,7,2,13,12,14,2,12,13,22,4,14,7,22,6]
def cycle20_0 : CycleData E W := ⟨2,![7,6,8,0],![2,14,12,4]⟩
def cycle20_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle20_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle20_3 : CycleData E W := ⟨2,![4,10,14,3],![2,13,22,7]⟩
def cycle20_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data20 : PartitionData E W := ⟨5,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,6,7,14,22]
def dst21 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,4,7,14,22,6]
def cycle21_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,13,22,6,4]⟩
def cycle21_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle21_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle21_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle21_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data21 : PartitionData E W := ⟨5,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,6,7,22,14]
def dst22 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,4,7,22,14,6]
def cycle22_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle22_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle22_2 : CycleData E W := ⟨2,![4,10,13,3],![2,13,22,7]⟩
def cycle22_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle22_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data22 : PartitionData E W := ⟨5,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,6,14,7,22]
def dst23 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,4,14,7,22,6]
def cycle23_0 : CycleData E W := ⟨1,![4,11,0],![2,13,4]⟩
def cycle23_1 : CycleData E W := ⟨2,![8,6,12,1],![4,12,14,6]⟩
def cycle23_2 : CycleData E W := ⟨1,![15,14,2],![6,22,7]⟩
def cycle23_3 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle23_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def data23 : PartitionData E W := ⟨5,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,6,7,2,13,12,14,4,13,12,22,6,7,14,22]
def dst24 : E → W := ![4,6,7,2,13,12,14,2,13,12,22,4,7,14,22,6]
def cycle24_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle24_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle24_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle24_3 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle24_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle24_5 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data24 : PartitionData E W := ⟨6,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4,cycle24_5]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,6,7,2,13,12,14,4,13,12,22,6,7,22,14]
def dst25 : E → W := ![4,6,7,2,13,12,14,2,13,12,22,4,7,22,14,6]
def cycle25_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,6,4]⟩
def cycle25_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle25_2 : CycleData E W := ⟨3,![4,8,11,13,3],![2,13,4,22,7]⟩
def cycle25_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle25_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data25 : PartitionData E W := ⟨5,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,6,7,2,13,12,14,4,13,12,22,6,14,7,22]
def dst26 : E → W := ![4,6,7,2,13,12,14,2,13,12,22,4,14,7,22,6]
def cycle26_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle26_1 : CycleData E W := ⟨2,![11,14,2,1],![4,22,7,6]⟩
def cycle26_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle26_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle26_4 : CycleData E W := ⟨2,![15,10,6,12],![6,22,12,14]⟩
def data26 : PartitionData E W := ⟨5,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,7,6,2,12,13,14,4,12,13,22,6,7,14,22]
def dst27 : E → W := ![4,7,6,2,12,13,14,2,12,13,22,4,7,14,22,6]
def cycle27_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle27_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle27_2 : CycleData E W := ⟨3,![4,8,11,15,3],![2,12,4,22,6]⟩
def cycle27_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle27_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data27 : PartitionData E W := ⟨5,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,7,6,2,12,13,14,4,12,13,22,6,7,22,14]
def dst28 : E → W := ![4,7,6,2,12,13,14,2,12,13,22,4,7,22,14,6]
def cycle28_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle28_1 : CycleData E W := ⟨1,![11,13,1],![4,22,7]⟩
def cycle28_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle28_3 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle28_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle28_5 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data28 : PartitionData E W := ⟨6,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4,cycle28_5]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,7,6,2,12,13,14,4,12,13,22,6,14,7,22]
def dst29 : E → W := ![4,7,6,2,12,13,14,2,12,13,22,4,14,7,22,6]
def cycle29_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle29_1 : CycleData E W := ⟨2,![11,15,2,1],![4,22,6,7]⟩
def cycle29_2 : CycleData E W := ⟨1,![7,12,3],![2,14,6]⟩
def cycle29_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle29_4 : CycleData E W := ⟨2,![14,10,6,13],![7,22,13,14]⟩
def data29 : PartitionData E W := ⟨5,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,6,7,14,22]
def dst30 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,4,7,14,22,6]
def cycle30_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle30_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle30_2 : CycleData E W := ⟨2,![4,9,15,3],![2,12,22,6]⟩
def cycle30_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle30_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data30 : PartitionData E W := ⟨5,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,6,7,22,14]
def dst31 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,4,7,22,14,6]
def cycle31_0 : CycleData E W := ⟨3,![4,9,13,1,0],![2,12,22,7,4]⟩
def cycle31_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle31_2 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle31_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle31_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data31 : PartitionData E W := ⟨5,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,6,14,7,22]
def dst32 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,4,14,7,22,6]
def cycle32_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle32_1 : CycleData E W := ⟨2,![11,6,13,1],![4,13,14,7]⟩
def cycle32_2 : CycleData E W := ⟨1,![15,14,2],![6,22,7]⟩
def cycle32_3 : CycleData E W := ⟨1,![7,12,3],![2,14,6]⟩
def cycle32_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def data32 : PartitionData E W := ⟨5,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,7,6,2,12,13,14,4,13,12,22,6,7,14,22]
def dst33 : E → W := ![4,7,6,2,12,13,14,2,13,12,22,4,7,14,22,6]
def cycle33_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle33_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle33_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,6]⟩
def cycle33_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle33_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,13]⟩
def data33 : PartitionData E W := ⟨5,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,7,6,2,12,13,14,4,13,12,22,6,7,22,14]
def dst34 : E → W := ![4,7,6,2,12,13,14,2,13,12,22,4,7,22,14,6]
def cycle34_0 : CycleData E W := ⟨3,![4,10,13,1,0],![2,12,22,7,4]⟩
def cycle34_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle34_2 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle34_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle34_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,13]⟩
def data34 : PartitionData E W := ⟨5,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,7,6,2,12,13,14,4,13,12,22,6,14,7,22]
def dst35 : E → W := ![4,7,6,2,12,13,14,2,13,12,22,4,14,7,22,6]
def cycle35_0 : CycleData E W := ⟨2,![7,6,8,0],![2,14,13,4]⟩
def cycle35_1 : CycleData E W := ⟨1,![11,14,1],![4,22,7]⟩
def cycle35_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle35_3 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,6]⟩
def cycle35_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data35 : PartitionData E W := ⟨5,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def src36 : E → W := ![2,4,7,6,2,12,14,13,4,12,13,22,6,7,14,22]
def dst36 : E → W := ![4,7,6,2,12,14,13,2,12,13,22,4,7,14,22,6]
def cycle36_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle36_1 : CycleData E W := ⟨2,![11,14,13,1],![4,22,14,7]⟩
def cycle36_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle36_3 : CycleData E W := ⟨2,![7,10,15,3],![2,13,22,6]⟩
def cycle36_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data36 : PartitionData E W := ⟨5,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4]⟩
lemma valid_data36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel

def src37 : E → W := ![2,4,7,6,2,12,14,13,4,12,13,22,6,7,22,14]
def dst37 : E → W := ![4,7,6,2,12,14,13,2,12,13,22,4,7,22,14,6]
def cycle37_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle37_1 : CycleData E W := ⟨1,![11,13,1],![4,22,7]⟩
def cycle37_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle37_3 : CycleData E W := ⟨3,![7,9,5,15,3],![2,13,12,14,6]⟩
def cycle37_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data37 : PartitionData E W := ⟨5,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4]⟩
lemma valid_data37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel

def src38 : E → W := ![2,4,7,6,2,12,14,13,4,12,13,22,6,14,7,22]
def dst38 : E → W := ![4,7,6,2,12,14,13,2,12,13,22,4,14,7,22,6]
def cycle38_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle38_1 : CycleData E W := ⟨1,![11,14,1],![4,22,7]⟩
def cycle38_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle38_3 : CycleData E W := ⟨2,![7,10,15,3],![2,13,22,6]⟩
def cycle38_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data38 : PartitionData E W := ⟨5,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4]⟩
lemma valid_data38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel

def src39 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,6,7,14,22]
def dst39 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,4,7,14,22,6]
def cycle39_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle39_1 : CycleData E W := ⟨2,![11,6,13,1],![4,13,14,7]⟩
def cycle39_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle39_3 : CycleData E W := ⟨2,![7,10,15,3],![2,13,22,6]⟩
def cycle39_4 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def data39 : PartitionData E W := ⟨5,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4]⟩
lemma valid_data39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel

def src40 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,6,7,22,14]
def dst40 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,4,7,22,14,6]
def cycle40_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle40_1 : CycleData E W := ⟨2,![11,10,13,1],![4,13,22,7]⟩
def cycle40_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle40_3 : CycleData E W := ⟨2,![7,6,15,3],![2,13,14,6]⟩
def cycle40_4 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def data40 : PartitionData E W := ⟨5,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4]⟩
lemma valid_data40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel

def src41 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,6,14,7,22]
def dst41 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,4,14,7,22,6]
def cycle41_0 : CycleData E W := ⟨6,![7,10,9,5,12,2,1,0],![2,13,22,12,14,6,7,4]⟩
def cycle41_1 : CycleData E W := ⟨6,![4,8,11,6,13,14,15,3],![2,12,4,13,14,7,22,6]⟩
def data41 : PartitionData E W := ⟨2,![cycle41_0,cycle41_1]⟩
lemma valid_data41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel

def src42 : E → W := ![2,4,7,6,2,12,14,13,4,13,12,22,6,7,14,22]
def dst42 : E → W := ![4,7,6,2,12,14,13,2,13,12,22,4,7,14,22,6]
def cycle42_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle42_1 : CycleData E W := ⟨2,![11,14,13,1],![4,22,14,7]⟩
def cycle42_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle42_3 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,6]⟩
def cycle42_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data42 : PartitionData E W := ⟨5,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4]⟩
lemma valid_data42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel

def src43 : E → W := ![2,4,7,6,2,12,14,13,4,13,12,22,6,7,22,14]
def dst43 : E → W := ![4,7,6,2,12,14,13,2,13,12,22,4,7,22,14,6]
def cycle43_0 : CycleData E W := ⟨3,![3,15,6,8,0],![2,6,14,13,4]⟩
def cycle43_1 : CycleData E W := ⟨1,![11,13,1],![4,22,7]⟩
def cycle43_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle43_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle43_4 : CycleData E W := ⟨1,![10,14,5],![12,22,14]⟩
def data43 : PartitionData E W := ⟨5,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4]⟩
lemma valid_data43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel

def src44 : E → W := ![2,4,7,6,2,12,14,13,4,13,12,22,6,14,7,22]
def dst44 : E → W := ![4,7,6,2,12,14,13,2,13,12,22,4,14,7,22,6]
def cycle44_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle44_1 : CycleData E W := ⟨1,![11,14,1],![4,22,7]⟩
def cycle44_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle44_3 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,6]⟩
def cycle44_4 : CycleData E W := ⟨1,![9,6,5],![12,13,14]⟩
def data44 : PartitionData E W := ⟨5,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4]⟩
lemma valid_data44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel

def src45 : E → W := ![2,4,7,6,2,13,12,14,4,12,13,22,6,7,14,22]
def dst45 : E → W := ![4,7,6,2,13,12,14,2,12,13,22,4,7,14,22,6]
def cycle45_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle45_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle45_2 : CycleData E W := ⟨2,![4,10,15,3],![2,13,22,6]⟩
def cycle45_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle45_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,12]⟩
def data45 : PartitionData E W := ⟨5,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4]⟩
lemma valid_data45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel

def src46 : E → W := ![2,4,7,6,2,13,12,14,4,12,13,22,6,7,22,14]
def dst46 : E → W := ![4,7,6,2,13,12,14,2,12,13,22,4,7,22,14,6]
def cycle46_0 : CycleData E W := ⟨3,![4,10,13,1,0],![2,13,22,7,4]⟩
def cycle46_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle46_2 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle46_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle46_4 : CycleData E W := ⟨2,![11,14,6,8],![4,22,14,12]⟩
def data46 : PartitionData E W := ⟨5,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4]⟩
lemma valid_data46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel

def src47 : E → W := ![2,4,7,6,2,13,12,14,4,12,13,22,6,14,7,22]
def dst47 : E → W := ![4,7,6,2,13,12,14,2,12,13,22,4,14,7,22,6]
def cycle47_0 : CycleData E W := ⟨2,![7,6,8,0],![2,14,12,4]⟩
def cycle47_1 : CycleData E W := ⟨1,![11,14,1],![4,22,7]⟩
def cycle47_2 : CycleData E W := ⟨1,![12,13,2],![6,14,7]⟩
def cycle47_3 : CycleData E W := ⟨2,![4,10,15,3],![2,13,22,6]⟩
def cycle47_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data47 : PartitionData E W := ⟨5,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4]⟩
lemma valid_data47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel

def src48 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,6,7,14,22]
def dst48 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,4,7,14,22,6]
def cycle48_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle48_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle48_2 : CycleData E W := ⟨2,![4,10,15,3],![2,13,22,6]⟩
def cycle48_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle48_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data48 : PartitionData E W := ⟨5,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4]⟩
lemma valid_data48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel

def src49 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,6,7,22,14]
def dst49 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,4,7,22,14,6]
def cycle49_0 : CycleData E W := ⟨3,![4,10,13,1,0],![2,13,22,7,4]⟩
def cycle49_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle49_2 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle49_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle49_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data49 : PartitionData E W := ⟨5,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4]⟩
lemma valid_data49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel

def src50 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,6,14,7,22]
def dst50 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,4,14,7,22,6]
def cycle50_0 : CycleData E W := ⟨1,![4,11,0],![2,13,4]⟩
def cycle50_1 : CycleData E W := ⟨2,![8,6,13,1],![4,12,14,7]⟩
def cycle50_2 : CycleData E W := ⟨1,![15,14,2],![6,22,7]⟩
def cycle50_3 : CycleData E W := ⟨1,![7,12,3],![2,14,6]⟩
def cycle50_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def data50 : PartitionData E W := ⟨5,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4]⟩
lemma valid_data50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel

def src51 : E → W := ![2,4,7,6,2,13,12,14,4,13,12,22,6,7,14,22]
def dst51 : E → W := ![4,7,6,2,13,12,14,2,13,12,22,4,7,14,22,6]
def cycle51_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,7,4]⟩
def cycle51_1 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle51_2 : CycleData E W := ⟨3,![4,8,11,15,3],![2,13,4,22,6]⟩
def cycle51_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle51_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data51 : PartitionData E W := ⟨5,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4]⟩
lemma valid_data51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel

def src52 : E → W := ![2,4,7,6,2,13,12,14,4,13,12,22,6,7,22,14]
def dst52 : E → W := ![4,7,6,2,13,12,14,2,13,12,22,4,7,22,14,6]
def cycle52_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle52_1 : CycleData E W := ⟨1,![11,13,1],![4,22,7]⟩
def cycle52_2 : CycleData E W := ⟨0,![12,2],![6,7]⟩
def cycle52_3 : CycleData E W := ⟨1,![7,15,3],![2,14,6]⟩
def cycle52_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle52_5 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data52 : PartitionData E W := ⟨6,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5]⟩
lemma valid_data52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel

def src53 : E → W := ![2,4,7,6,2,13,12,14,4,13,12,22,6,14,7,22]
def dst53 : E → W := ![4,7,6,2,13,12,14,2,13,12,22,4,14,7,22,6]
def cycle53_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle53_1 : CycleData E W := ⟨2,![11,15,2,1],![4,22,6,7]⟩
def cycle53_2 : CycleData E W := ⟨1,![7,12,3],![2,14,6]⟩
def cycle53_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle53_4 : CycleData E W := ⟨2,![14,10,6,13],![7,22,12,14]⟩
def data53 : PartitionData E W := ⟨5,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4]⟩
lemma valid_data53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel

def src54 : E → W := ![2,6,4,7,2,12,13,14,4,12,13,22,6,7,14,22]
def dst54 : E → W := ![6,4,7,2,12,13,14,2,12,13,22,4,7,14,22,6]
def cycle54_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle54_1 : CycleData E W := ⟨2,![11,15,12,2],![4,22,6,7]⟩
def cycle54_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle54_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle54_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data54 : PartitionData E W := ⟨5,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4]⟩
lemma valid_data54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel

def src55 : E → W := ![2,6,4,7,2,12,13,14,4,12,13,22,6,7,22,14]
def dst55 : E → W := ![6,4,7,2,12,13,14,2,12,13,22,4,7,22,14,6]
def cycle55_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle55_1 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle55_2 : CycleData E W := ⟨2,![7,15,12,3],![2,14,6,7]⟩
def cycle55_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle55_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data55 : PartitionData E W := ⟨5,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4]⟩
lemma valid_data55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel

def src56 : E → W := ![2,6,4,7,2,12,13,14,4,12,13,22,6,14,7,22]
def dst56 : E → W := ![6,4,7,2,12,13,14,2,12,13,22,4,14,7,22,6]
def cycle56_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle56_1 : CycleData E W := ⟨1,![11,14,2],![4,22,7]⟩
def cycle56_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle56_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle56_4 : CycleData E W := ⟨2,![15,10,6,12],![6,22,13,14]⟩
def data56 : PartitionData E W := ⟨5,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4]⟩
lemma valid_data56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel

def src57 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,6,7,14,22]
def dst57 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,4,7,14,22,6]
def cycle57_0 : CycleData E W := ⟨2,![4,9,15,0],![2,12,22,6]⟩
def cycle57_1 : CycleData E W := ⟨1,![2,12,1],![4,7,6]⟩
def cycle57_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle57_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle57_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data57 : PartitionData E W := ⟨5,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4]⟩
lemma valid_data57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel

def src58 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,6,7,22,14]
def dst58 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,4,7,22,14,6]
def cycle58_0 : CycleData E W := ⟨1,![7,15,0],![2,14,6]⟩
def cycle58_1 : CycleData E W := ⟨1,![2,12,1],![4,7,6]⟩
def cycle58_2 : CycleData E W := ⟨2,![4,9,13,3],![2,12,22,7]⟩
def cycle58_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle58_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data58 : PartitionData E W := ⟨5,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4]⟩
lemma valid_data58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel

def src59 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,6,14,7,22]
def dst59 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,4,14,7,22,6]
def cycle59_0 : CycleData E W := ⟨6,![7,6,5,9,14,2,1,0],![2,14,13,12,22,7,4,6]⟩
def cycle59_1 : CycleData E W := ⟨6,![4,8,11,10,15,12,13,3],![2,12,4,13,22,6,14,7]⟩
def data59 : PartitionData E W := ⟨2,![cycle59_0,cycle59_1]⟩
lemma valid_data59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel

def src60 : E → W := ![2,6,4,7,2,12,13,14,4,13,12,22,6,7,14,22]
def dst60 : E → W := ![6,4,7,2,12,13,14,2,13,12,22,4,7,14,22,6]
def cycle60_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle60_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle60_2 : CycleData E W := ⟨2,![8,6,13,2],![4,13,14,7]⟩
def cycle60_3 : CycleData E W := ⟨2,![7,14,10,4],![2,14,22,12]⟩
def cycle60_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data60 : PartitionData E W := ⟨5,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4]⟩
lemma valid_data60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel

def src61 : E → W := ![2,6,4,7,2,12,13,14,4,13,12,22,6,7,22,14]
def dst61 : E → W := ![6,4,7,2,12,13,14,2,13,12,22,4,7,22,14,6]
def cycle61_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle61_1 : CycleData E W := ⟨2,![8,6,15,1],![4,13,14,6]⟩
def cycle61_2 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle61_3 : CycleData E W := ⟨2,![7,14,10,4],![2,14,22,12]⟩
def cycle61_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data61 : PartitionData E W := ⟨5,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4]⟩
lemma valid_data61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel

def src62 : E → W := ![2,6,4,7,2,12,13,14,4,13,12,22,6,14,7,22]
def dst62 : E → W := ![6,4,7,2,12,13,14,2,13,12,22,4,14,7,22,6]
def cycle62_0 : CycleData E W := ⟨1,![7,12,0],![2,14,6]⟩
def cycle62_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle62_2 : CycleData E W := ⟨2,![8,6,13,2],![4,13,14,7]⟩
def cycle62_3 : CycleData E W := ⟨2,![4,10,14,3],![2,12,22,7]⟩
def cycle62_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data62 : PartitionData E W := ⟨5,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4]⟩
lemma valid_data62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel

def src63 : E → W := ![2,6,4,7,2,12,14,13,4,12,13,22,6,7,14,22]
def dst63 : E → W := ![6,4,7,2,12,14,13,2,12,13,22,4,7,14,22,6]
def cycle63_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle63_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle63_2 : CycleData E W := ⟨2,![8,5,13,2],![4,12,14,7]⟩
def cycle63_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle63_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data63 : PartitionData E W := ⟨5,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4]⟩
lemma valid_data63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel

def src64 : E → W := ![2,6,4,7,2,12,14,13,4,12,13,22,6,7,22,14]
def dst64 : E → W := ![6,4,7,2,12,14,13,2,12,13,22,4,7,22,14,6]
def cycle64_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle64_1 : CycleData E W := ⟨2,![8,5,15,1],![4,12,14,6]⟩
def cycle64_2 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle64_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle64_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data64 : PartitionData E W := ⟨5,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4]⟩
lemma valid_data64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel

def src65 : E → W := ![2,6,4,7,2,12,14,13,4,12,13,22,6,14,7,22]
def dst65 : E → W := ![6,4,7,2,12,14,13,2,12,13,22,4,14,7,22,6]
def cycle65_0 : CycleData E W := ⟨6,![4,5,6,10,14,2,1,0],![2,12,14,13,22,7,4,6]⟩
def cycle65_1 : CycleData E W := ⟨6,![7,9,8,11,15,12,13,3],![2,13,12,4,22,6,14,7]⟩
def data65 : PartitionData E W := ⟨2,![cycle65_0,cycle65_1]⟩
lemma valid_data65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel

def src66 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,6,7,14,22]
def dst66 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,4,7,14,22,6]
def cycle66_0 : CycleData E W := ⟨6,![7,10,9,5,13,2,1,0],![2,13,22,12,14,7,4,6]⟩
def cycle66_1 : CycleData E W := ⟨6,![4,8,11,6,14,15,12,3],![2,12,4,13,14,22,6,7]⟩
def data66 : PartitionData E W := ⟨2,![cycle66_0,cycle66_1]⟩
lemma valid_data66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel

def src67 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,6,7,22,14]
def dst67 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,4,7,22,14,6]
def cycle67_0 : CycleData E W := ⟨6,![7,6,5,9,13,2,1,0],![2,13,14,12,22,7,4,6]⟩
def cycle67_1 : CycleData E W := ⟨6,![4,8,11,10,14,15,12,3],![2,12,4,13,22,14,6,7]⟩
def data67 : PartitionData E W := ⟨2,![cycle67_0,cycle67_1]⟩
lemma valid_data67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel

def src68 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,6,14,7,22]
def dst68 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,4,14,7,22,6]
def cycle68_0 : CycleData E W := ⟨6,![7,10,9,5,13,2,1,0],![2,13,22,12,14,7,4,6]⟩
def cycle68_1 : CycleData E W := ⟨6,![4,8,11,6,12,15,14,3],![2,12,4,13,14,6,22,7]⟩
def data68 : PartitionData E W := ⟨2,![cycle68_0,cycle68_1]⟩
lemma valid_data68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel

def src69 : E → W := ![2,6,4,7,2,12,14,13,4,13,12,22,6,7,14,22]
def dst69 : E → W := ![6,4,7,2,12,14,13,2,13,12,22,4,7,14,22,6]
def cycle69_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle69_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle69_2 : CycleData E W := ⟨2,![8,6,13,2],![4,13,14,7]⟩
def cycle69_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle69_4 : CycleData E W := ⟨1,![10,14,5],![12,22,14]⟩
def data69 : PartitionData E W := ⟨5,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4]⟩
lemma valid_data69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel

def src70 : E → W := ![2,6,4,7,2,12,14,13,4,13,12,22,6,7,22,14]
def dst70 : E → W := ![6,4,7,2,12,14,13,2,13,12,22,4,7,22,14,6]
def cycle70_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle70_1 : CycleData E W := ⟨2,![8,6,15,1],![4,13,14,6]⟩
def cycle70_2 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle70_3 : CycleData E W := ⟨1,![7,9,4],![2,13,12]⟩
def cycle70_4 : CycleData E W := ⟨1,![10,14,5],![12,22,14]⟩
def data70 : PartitionData E W := ⟨5,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4]⟩
lemma valid_data70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel

def src71 : E → W := ![2,6,4,7,2,12,14,13,4,13,12,22,6,14,7,22]
def dst71 : E → W := ![6,4,7,2,12,14,13,2,13,12,22,4,14,7,22,6]
def cycle71_0 : CycleData E W := ⟨6,![7,6,5,10,14,2,1,0],![2,13,14,12,22,7,4,6]⟩
def cycle71_1 : CycleData E W := ⟨6,![4,9,8,11,15,12,13,3],![2,12,13,4,22,6,14,7]⟩
def data71 : PartitionData E W := ⟨2,![cycle71_0,cycle71_1]⟩
lemma valid_data71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel

def src72 : E → W := ![2,6,4,7,2,13,12,14,4,12,13,22,6,7,14,22]
def dst72 : E → W := ![6,4,7,2,13,12,14,2,12,13,22,4,7,14,22,6]
def cycle72_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle72_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle72_2 : CycleData E W := ⟨2,![8,6,13,2],![4,12,14,7]⟩
def cycle72_3 : CycleData E W := ⟨2,![7,14,10,4],![2,14,22,13]⟩
def cycle72_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data72 : PartitionData E W := ⟨5,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4]⟩
lemma valid_data72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel

def src73 : E → W := ![2,6,4,7,2,13,12,14,4,12,13,22,6,7,22,14]
def dst73 : E → W := ![6,4,7,2,13,12,14,2,12,13,22,4,7,22,14,6]
def cycle73_0 : CycleData E W := ⟨1,![3,12,0],![2,7,6]⟩
def cycle73_1 : CycleData E W := ⟨2,![8,6,15,1],![4,12,14,6]⟩
def cycle73_2 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle73_3 : CycleData E W := ⟨2,![7,14,10,4],![2,14,22,13]⟩
def cycle73_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data73 : PartitionData E W := ⟨5,![cycle73_0,cycle73_1,cycle73_2,cycle73_3,cycle73_4]⟩
lemma valid_data73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel

def src74 : E → W := ![2,6,4,7,2,13,12,14,4,12,13,22,6,14,7,22]
def dst74 : E → W := ![6,4,7,2,13,12,14,2,12,13,22,4,14,7,22,6]
def cycle74_0 : CycleData E W := ⟨1,![7,12,0],![2,14,6]⟩
def cycle74_1 : CycleData E W := ⟨1,![11,15,1],![4,22,6]⟩
def cycle74_2 : CycleData E W := ⟨2,![8,6,13,2],![4,12,14,7]⟩
def cycle74_3 : CycleData E W := ⟨2,![4,10,14,3],![2,13,22,7]⟩
def cycle74_4 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def data74 : PartitionData E W := ⟨5,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4]⟩
lemma valid_data74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel

def src75 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,6,7,14,22]
def dst75 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,4,7,14,22,6]
def cycle75_0 : CycleData E W := ⟨2,![4,10,15,0],![2,13,22,6]⟩
def cycle75_1 : CycleData E W := ⟨1,![2,12,1],![4,7,6]⟩
def cycle75_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle75_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle75_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data75 : PartitionData E W := ⟨5,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4]⟩
lemma valid_data75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel

def src76 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,6,7,22,14]
def dst76 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,4,7,22,14,6]
def cycle76_0 : CycleData E W := ⟨1,![7,15,0],![2,14,6]⟩
def cycle76_1 : CycleData E W := ⟨1,![2,12,1],![4,7,6]⟩
def cycle76_2 : CycleData E W := ⟨2,![4,10,13,3],![2,13,22,7]⟩
def cycle76_3 : CycleData E W := ⟨1,![11,5,8],![4,13,12]⟩
def cycle76_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data76 : PartitionData E W := ⟨5,![cycle76_0,cycle76_1,cycle76_2,cycle76_3,cycle76_4]⟩
lemma valid_data76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel

def src77 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,6,14,7,22]
def dst77 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,4,14,7,22,6]
def cycle77_0 : CycleData E W := ⟨6,![7,6,5,10,14,2,1,0],![2,14,12,13,22,7,4,6]⟩
def cycle77_1 : CycleData E W := ⟨6,![4,11,8,9,15,12,13,3],![2,13,4,12,22,6,14,7]⟩
def data77 : PartitionData E W := ⟨2,![cycle77_0,cycle77_1]⟩
lemma valid_data77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel

def src78 : E → W := ![2,6,4,7,2,13,12,14,4,13,12,22,6,7,14,22]
def dst78 : E → W := ![6,4,7,2,13,12,14,2,13,12,22,4,7,14,22,6]
def cycle78_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle78_1 : CycleData E W := ⟨2,![11,15,12,2],![4,22,6,7]⟩
def cycle78_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle78_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle78_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data78 : PartitionData E W := ⟨5,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4]⟩
lemma valid_data78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel

def src79 : E → W := ![2,6,4,7,2,13,12,14,4,13,12,22,6,7,22,14]
def dst79 : E → W := ![6,4,7,2,13,12,14,2,13,12,22,4,7,22,14,6]
def cycle79_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle79_1 : CycleData E W := ⟨1,![11,13,2],![4,22,7]⟩
def cycle79_2 : CycleData E W := ⟨2,![7,15,12,3],![2,14,6,7]⟩
def cycle79_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle79_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data79 : PartitionData E W := ⟨5,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4]⟩
lemma valid_data79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel

def src80 : E → W := ![2,6,4,7,2,13,12,14,4,13,12,22,6,14,7,22]
def dst80 : E → W := ![6,4,7,2,13,12,14,2,13,12,22,4,14,7,22,6]
def cycle80_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle80_1 : CycleData E W := ⟨1,![11,14,2],![4,22,7]⟩
def cycle80_2 : CycleData E W := ⟨1,![7,13,3],![2,14,7]⟩
def cycle80_3 : CycleData E W := ⟨0,![9,5],![12,13]⟩
def cycle80_4 : CycleData E W := ⟨2,![15,10,6,12],![6,22,12,14]⟩
def data80 : PartitionData E W := ⟨5,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4]⟩
lemma valid_data80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
  if k < 40 then
    if k < 20 then
      if k < 10 then
        if k < 5 then
          if k < 2 then
            if k < 1 then
              data0
            else
              data1
          else
            if k < 3 then
              data2
            else
              if k < 4 then
                data3
              else
                data4
        else
          if k < 7 then
            if k < 6 then
              data5
            else
              data6
          else
            if k < 8 then
              data7
            else
              if k < 9 then
                data8
              else
                data9
      else
        if k < 15 then
          if k < 12 then
            if k < 11 then
              data10
            else
              data11
          else
            if k < 13 then
              data12
            else
              if k < 14 then
                data13
              else
                data14
        else
          if k < 17 then
            if k < 16 then
              data15
            else
              data16
          else
            if k < 18 then
              data17
            else
              if k < 19 then
                data18
              else
                data19
    else
      if k < 30 then
        if k < 25 then
          if k < 22 then
            if k < 21 then
              data20
            else
              data21
          else
            if k < 23 then
              data22
            else
              if k < 24 then
                data23
              else
                data24
        else
          if k < 27 then
            if k < 26 then
              data25
            else
              data26
          else
            if k < 28 then
              data27
            else
              if k < 29 then
                data28
              else
                data29
      else
        if k < 35 then
          if k < 32 then
            if k < 31 then
              data30
            else
              data31
          else
            if k < 33 then
              data32
            else
              if k < 34 then
                data33
              else
                data34
        else
          if k < 37 then
            if k < 36 then
              data35
            else
              data36
          else
            if k < 38 then
              data37
            else
              if k < 39 then
                data38
              else
                data39
  else
    if k < 60 then
      if k < 50 then
        if k < 45 then
          if k < 42 then
            if k < 41 then
              data40
            else
              data41
          else
            if k < 43 then
              data42
            else
              if k < 44 then
                data43
              else
                data44
        else
          if k < 47 then
            if k < 46 then
              data45
            else
              data46
          else
            if k < 48 then
              data47
            else
              if k < 49 then
                data48
              else
                data49
      else
        if k < 55 then
          if k < 52 then
            if k < 51 then
              data50
            else
              data51
          else
            if k < 53 then
              data52
            else
              if k < 54 then
                data53
              else
                data54
        else
          if k < 57 then
            if k < 56 then
              data55
            else
              data56
          else
            if k < 58 then
              data57
            else
              if k < 59 then
                data58
              else
                data59
    else
      if k < 70 then
        if k < 65 then
          if k < 62 then
            if k < 61 then
              data60
            else
              data61
          else
            if k < 63 then
              data62
            else
              if k < 64 then
                data63
              else
                data64
        else
          if k < 67 then
            if k < 66 then
              data65
            else
              data66
          else
            if k < 68 then
              data67
            else
              if k < 69 then
                data68
              else
                data69
      else
        if k < 75 then
          if k < 72 then
            if k < 71 then
              data70
            else
              data71
          else
            if k < 73 then
              data72
            else
              if k < 74 then
                data73
              else
                data74
        else
          if k < 78 then
            if k < 76 then
              data75
            else
              if k < 77 then
                data76
              else
                data77
          else
            if k < 79 then
              data78
            else
              if k < 80 then
                data79
              else
                data80

def srcTable (k : ℕ) : E → W :=
  if k < 40 then
    if k < 20 then
      if k < 10 then
        if k < 5 then
          if k < 2 then
            if k < 1 then
              src0
            else
              src1
          else
            if k < 3 then
              src2
            else
              if k < 4 then
                src3
              else
                src4
        else
          if k < 7 then
            if k < 6 then
              src5
            else
              src6
          else
            if k < 8 then
              src7
            else
              if k < 9 then
                src8
              else
                src9
      else
        if k < 15 then
          if k < 12 then
            if k < 11 then
              src10
            else
              src11
          else
            if k < 13 then
              src12
            else
              if k < 14 then
                src13
              else
                src14
        else
          if k < 17 then
            if k < 16 then
              src15
            else
              src16
          else
            if k < 18 then
              src17
            else
              if k < 19 then
                src18
              else
                src19
    else
      if k < 30 then
        if k < 25 then
          if k < 22 then
            if k < 21 then
              src20
            else
              src21
          else
            if k < 23 then
              src22
            else
              if k < 24 then
                src23
              else
                src24
        else
          if k < 27 then
            if k < 26 then
              src25
            else
              src26
          else
            if k < 28 then
              src27
            else
              if k < 29 then
                src28
              else
                src29
      else
        if k < 35 then
          if k < 32 then
            if k < 31 then
              src30
            else
              src31
          else
            if k < 33 then
              src32
            else
              if k < 34 then
                src33
              else
                src34
        else
          if k < 37 then
            if k < 36 then
              src35
            else
              src36
          else
            if k < 38 then
              src37
            else
              if k < 39 then
                src38
              else
                src39
  else
    if k < 60 then
      if k < 50 then
        if k < 45 then
          if k < 42 then
            if k < 41 then
              src40
            else
              src41
          else
            if k < 43 then
              src42
            else
              if k < 44 then
                src43
              else
                src44
        else
          if k < 47 then
            if k < 46 then
              src45
            else
              src46
          else
            if k < 48 then
              src47
            else
              if k < 49 then
                src48
              else
                src49
      else
        if k < 55 then
          if k < 52 then
            if k < 51 then
              src50
            else
              src51
          else
            if k < 53 then
              src52
            else
              if k < 54 then
                src53
              else
                src54
        else
          if k < 57 then
            if k < 56 then
              src55
            else
              src56
          else
            if k < 58 then
              src57
            else
              if k < 59 then
                src58
              else
                src59
    else
      if k < 70 then
        if k < 65 then
          if k < 62 then
            if k < 61 then
              src60
            else
              src61
          else
            if k < 63 then
              src62
            else
              if k < 64 then
                src63
              else
                src64
        else
          if k < 67 then
            if k < 66 then
              src65
            else
              src66
          else
            if k < 68 then
              src67
            else
              if k < 69 then
                src68
              else
                src69
      else
        if k < 75 then
          if k < 72 then
            if k < 71 then
              src70
            else
              src71
          else
            if k < 73 then
              src72
            else
              if k < 74 then
                src73
              else
                src74
        else
          if k < 78 then
            if k < 76 then
              src75
            else
              if k < 77 then
                src76
              else
                src77
          else
            if k < 79 then
              src78
            else
              if k < 80 then
                src79
              else
                src80

def dstTable (k : ℕ) : E → W :=
  if k < 40 then
    if k < 20 then
      if k < 10 then
        if k < 5 then
          if k < 2 then
            if k < 1 then
              dst0
            else
              dst1
          else
            if k < 3 then
              dst2
            else
              if k < 4 then
                dst3
              else
                dst4
        else
          if k < 7 then
            if k < 6 then
              dst5
            else
              dst6
          else
            if k < 8 then
              dst7
            else
              if k < 9 then
                dst8
              else
                dst9
      else
        if k < 15 then
          if k < 12 then
            if k < 11 then
              dst10
            else
              dst11
          else
            if k < 13 then
              dst12
            else
              if k < 14 then
                dst13
              else
                dst14
        else
          if k < 17 then
            if k < 16 then
              dst15
            else
              dst16
          else
            if k < 18 then
              dst17
            else
              if k < 19 then
                dst18
              else
                dst19
    else
      if k < 30 then
        if k < 25 then
          if k < 22 then
            if k < 21 then
              dst20
            else
              dst21
          else
            if k < 23 then
              dst22
            else
              if k < 24 then
                dst23
              else
                dst24
        else
          if k < 27 then
            if k < 26 then
              dst25
            else
              dst26
          else
            if k < 28 then
              dst27
            else
              if k < 29 then
                dst28
              else
                dst29
      else
        if k < 35 then
          if k < 32 then
            if k < 31 then
              dst30
            else
              dst31
          else
            if k < 33 then
              dst32
            else
              if k < 34 then
                dst33
              else
                dst34
        else
          if k < 37 then
            if k < 36 then
              dst35
            else
              dst36
          else
            if k < 38 then
              dst37
            else
              if k < 39 then
                dst38
              else
                dst39
  else
    if k < 60 then
      if k < 50 then
        if k < 45 then
          if k < 42 then
            if k < 41 then
              dst40
            else
              dst41
          else
            if k < 43 then
              dst42
            else
              if k < 44 then
                dst43
              else
                dst44
        else
          if k < 47 then
            if k < 46 then
              dst45
            else
              dst46
          else
            if k < 48 then
              dst47
            else
              if k < 49 then
                dst48
              else
                dst49
      else
        if k < 55 then
          if k < 52 then
            if k < 51 then
              dst50
            else
              dst51
          else
            if k < 53 then
              dst52
            else
              if k < 54 then
                dst53
              else
                dst54
        else
          if k < 57 then
            if k < 56 then
              dst55
            else
              dst56
          else
            if k < 58 then
              dst57
            else
              if k < 59 then
                dst58
              else
                dst59
    else
      if k < 70 then
        if k < 65 then
          if k < 62 then
            if k < 61 then
              dst60
            else
              dst61
          else
            if k < 63 then
              dst62
            else
              if k < 64 then
                dst63
              else
                dst64
        else
          if k < 67 then
            if k < 66 then
              dst65
            else
              dst66
          else
            if k < 68 then
              dst67
            else
              if k < 69 then
                dst68
              else
                dst69
      else
        if k < 75 then
          if k < 72 then
            if k < 71 then
              dst70
            else
              dst71
          else
            if k < 73 then
              dst72
            else
              if k < 74 then
                dst73
              else
                dst74
        else
          if k < 78 then
            if k < 76 then
              dst75
            else
              if k < 77 then
                dst76
              else
                dst77
          else
            if k < 79 then
              dst78
            else
              if k < 80 then
                dst79
              else
                dst80

lemma table_valid (k : Fin 81) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
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

lemma src_table_row : ∀ (k : Fin 81) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 81) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 81) := {14,41,59,65,66,67,68,71,77}
lemma size_mem : ∀ k : Fin 81, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 81, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows6

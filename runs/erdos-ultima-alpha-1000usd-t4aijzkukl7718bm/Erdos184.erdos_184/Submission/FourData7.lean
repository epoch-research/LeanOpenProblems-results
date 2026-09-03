import Submission.FourRows7

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows7
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,23,6,14,22,7,23]
def dst0 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle0_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle0_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle0_2 : CycleData E W := ⟨2,![4,9,15,3],![2,12,22,7]⟩
def cycle0_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle0_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data0 : PartitionData E W := ⟨5,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,23,6,14,23,7,22]
def dst1 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle1_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle1_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle1_2 : CycleData E W := ⟨3,![4,8,12,15,3],![2,12,4,23,7]⟩
def cycle1_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle1_4 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data1 : PartitionData E W := ⟨5,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,23,6,22,7,14,23]
def dst2 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle2_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle2_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle2_2 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle2_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle2_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle2_5 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data2 : PartitionData E W := ⟨6,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4,cycle2_5]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,6,7,2,12,13,14,4,12,22,13,23,6,22,14,7,23]
def dst3 : E → W := ![4,6,7,2,12,13,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle3_0 : CycleData E W := ⟨3,![4,9,13,1,0],![2,12,22,6,4]⟩
def cycle3_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle3_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle3_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle3_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data3 : PartitionData E W := ⟨5,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,6,7,2,12,13,14,4,12,23,13,22,6,14,22,7,23]
def dst4 : E → W := ![4,6,7,2,12,13,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle4_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle4_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle4_2 : CycleData E W := ⟨3,![4,8,12,15,3],![2,12,4,22,7]⟩
def cycle4_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle4_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data4 : PartitionData E W := ⟨5,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,6,7,2,12,13,14,4,12,23,13,22,6,14,23,7,22]
def dst5 : E → W := ![4,6,7,2,12,13,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle5_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle5_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle5_2 : CycleData E W := ⟨2,![4,9,15,3],![2,12,23,7]⟩
def cycle5_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle5_4 : CycleData E W := ⟨1,![10,14,6],![13,23,14]⟩
def data5 : PartitionData E W := ⟨5,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,6,7,2,12,13,14,4,12,23,13,22,6,22,7,14,23]
def dst6 : E → W := ![4,6,7,2,12,13,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle6_0 : CycleData E W := ⟨3,![4,9,17,1,0],![2,12,23,6,4]⟩
def cycle6_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle6_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle6_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle6_4 : CycleData E W := ⟨1,![10,16,6],![13,23,14]⟩
def data6 : PartitionData E W := ⟨5,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,6,7,2,12,13,14,4,12,23,13,22,6,22,14,7,23]
def dst7 : E → W := ![4,6,7,2,12,13,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle7_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle7_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle7_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle7_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle7_4 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle7_5 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data7 : PartitionData E W := ⟨6,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,6,7,2,12,13,14,4,13,22,12,23,6,14,22,7,23]
def dst8 : E → W := ![4,6,7,2,12,13,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle8_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle8_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle8_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,7]⟩
def cycle8_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle8_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data8 : PartitionData E W := ⟨5,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,6,7,2,12,13,14,4,13,22,12,23,6,14,23,7,22]
def dst9 : E → W := ![4,6,7,2,12,13,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle9_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle9_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle9_2 : CycleData E W := ⟨2,![4,11,15,3],![2,12,23,7]⟩
def cycle9_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle9_4 : CycleData E W := ⟨2,![12,14,6,8],![4,23,14,13]⟩
def data9 : PartitionData E W := ⟨5,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,6,7,2,12,13,14,4,13,22,12,23,6,22,7,14,23]
def dst10 : E → W := ![4,6,7,2,12,13,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle10_0 : CycleData E W := ⟨3,![4,11,17,1,0],![2,12,23,6,4]⟩
def cycle10_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle10_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle10_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle10_4 : CycleData E W := ⟨2,![12,16,6,8],![4,23,14,13]⟩
def data10 : PartitionData E W := ⟨5,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,6,7,2,12,13,14,4,13,22,12,23,6,22,14,7,23]
def dst11 : E → W := ![4,6,7,2,12,13,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle11_0 : CycleData E W := ⟨3,![4,10,13,1,0],![2,12,22,6,4]⟩
def cycle11_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle11_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle11_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle11_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data11 : PartitionData E W := ⟨5,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,6,7,2,12,13,14,4,13,23,12,22,6,14,22,7,23]
def dst12 : E → W := ![4,6,7,2,12,13,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle12_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle12_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle12_2 : CycleData E W := ⟨2,![4,11,15,3],![2,12,22,7]⟩
def cycle12_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle12_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,13]⟩
def data12 : PartitionData E W := ⟨5,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,6,7,2,12,13,14,4,13,23,12,22,6,14,23,7,22]
def dst13 : E → W := ![4,6,7,2,12,13,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle13_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle13_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle13_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,23,7]⟩
def cycle13_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle13_4 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def data13 : PartitionData E W := ⟨5,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,6,7,2,12,13,14,4,13,23,12,22,6,22,7,14,23]
def dst14 : E → W := ![4,6,7,2,12,13,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle14_0 : CycleData E W := ⟨3,![4,10,17,1,0],![2,12,23,6,4]⟩
def cycle14_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle14_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle14_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle14_4 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def data14 : PartitionData E W := ⟨5,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,6,7,2,12,13,14,4,13,23,12,22,6,22,14,7,23]
def dst15 : E → W := ![4,6,7,2,12,13,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle15_0 : CycleData E W := ⟨3,![4,11,13,1,0],![2,12,22,6,4]⟩
def cycle15_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle15_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle15_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle15_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,13]⟩
def data15 : PartitionData E W := ⟨5,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,23,6,14,22,7,23]
def dst16 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,23,4,14,22,7,23,6]
def cycle16_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle16_1 : CycleData E W := ⟨2,![12,16,2,1],![4,23,7,6]⟩
def cycle16_2 : CycleData E W := ⟨2,![7,10,15,3],![2,13,22,7]⟩
def cycle16_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle16_4 : CycleData E W := ⟨2,![17,11,6,13],![6,23,13,14]⟩
def data16 : PartitionData E W := ⟨5,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,23,6,14,23,7,22]
def dst17 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,23,4,14,23,7,22,6]
def cycle17_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle17_1 : CycleData E W := ⟨2,![12,15,2,1],![4,23,7,6]⟩
def cycle17_2 : CycleData E W := ⟨2,![7,10,16,3],![2,13,22,7]⟩
def cycle17_3 : CycleData E W := ⟨2,![17,9,5,13],![6,22,12,14]⟩
def cycle17_4 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data17 : PartitionData E W := ⟨5,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,23,6,22,7,14,23]
def dst18 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,23,4,22,7,14,23,6]
def cycle18_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle18_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle18_2 : CycleData E W := ⟨3,![7,10,13,2,3],![2,13,22,6,7]⟩
def cycle18_3 : CycleData E W := ⟨2,![15,5,9,14],![7,14,12,22]⟩
def cycle18_4 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data18 : PartitionData E W := ⟨5,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,6,7,2,12,14,13,4,12,22,13,23,6,22,14,7,23]
def dst19 : E → W := ![4,6,7,2,12,14,13,2,12,22,13,23,4,22,14,7,23,6]
def cycle19_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle19_1 : CycleData E W := ⟨2,![12,16,2,1],![4,23,7,6]⟩
def cycle19_2 : CycleData E W := ⟨2,![7,6,15,3],![2,13,14,7]⟩
def cycle19_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle19_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,13,22]⟩
def data19 : PartitionData E W := ⟨5,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,6,7,2,12,14,13,4,12,23,13,22,6,14,22,7,23]
def dst20 : E → W := ![4,6,7,2,12,14,13,2,12,23,13,22,4,14,22,7,23,6]
def cycle20_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle20_1 : CycleData E W := ⟨2,![12,15,2,1],![4,22,7,6]⟩
def cycle20_2 : CycleData E W := ⟨2,![7,10,16,3],![2,13,23,7]⟩
def cycle20_3 : CycleData E W := ⟨2,![17,9,5,13],![6,23,12,14]⟩
def cycle20_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data20 : PartitionData E W := ⟨5,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,6,7,2,12,14,13,4,12,23,13,22,6,14,23,7,22]
def dst21 : E → W := ![4,6,7,2,12,14,13,2,12,23,13,22,4,14,23,7,22,6]
def cycle21_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle21_1 : CycleData E W := ⟨2,![12,16,2,1],![4,22,7,6]⟩
def cycle21_2 : CycleData E W := ⟨2,![7,10,15,3],![2,13,23,7]⟩
def cycle21_3 : CycleData E W := ⟨1,![9,14,5],![12,23,14]⟩
def cycle21_4 : CycleData E W := ⟨2,![17,11,6,13],![6,22,13,14]⟩
def data21 : PartitionData E W := ⟨5,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,6,7,2,12,14,13,4,12,23,13,22,6,22,7,14,23]
def dst22 : E → W := ![4,6,7,2,12,14,13,2,12,23,13,22,4,22,7,14,23,6]
def cycle22_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle22_1 : CycleData E W := ⟨2,![12,14,2,1],![4,22,7,6]⟩
def cycle22_2 : CycleData E W := ⟨2,![7,6,15,3],![2,13,14,7]⟩
def cycle22_3 : CycleData E W := ⟨1,![9,16,5],![12,23,14]⟩
def cycle22_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,13,22]⟩
def data22 : PartitionData E W := ⟨5,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,6,7,2,12,14,13,4,12,23,13,22,6,22,14,7,23]
def dst23 : E → W := ![4,6,7,2,12,14,13,2,12,23,13,22,4,22,14,7,23,6]
def cycle23_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle23_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle23_2 : CycleData E W := ⟨3,![7,10,17,2,3],![2,13,23,6,7]⟩
def cycle23_3 : CycleData E W := ⟨2,![16,9,5,15],![7,23,12,14]⟩
def cycle23_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data23 : PartitionData E W := ⟨5,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,6,7,2,12,14,13,4,13,22,12,23,6,14,22,7,23]
def dst24 : E → W := ![4,6,7,2,12,14,13,2,13,22,12,23,4,14,22,7,23,6]
def cycle24_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle24_1 : CycleData E W := ⟨2,![12,16,2,1],![4,23,7,6]⟩
def cycle24_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,7]⟩
def cycle24_3 : CycleData E W := ⟨2,![17,11,5,13],![6,23,12,14]⟩
def cycle24_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data24 : PartitionData E W := ⟨5,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,6,7,2,12,14,13,4,13,22,12,23,6,14,23,7,22]
def dst25 : E → W := ![4,6,7,2,12,14,13,2,13,22,12,23,4,14,23,7,22,6]
def cycle25_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle25_1 : CycleData E W := ⟨2,![12,15,2,1],![4,23,7,6]⟩
def cycle25_2 : CycleData E W := ⟨2,![4,10,16,3],![2,12,22,7]⟩
def cycle25_3 : CycleData E W := ⟨1,![11,14,5],![12,23,14]⟩
def cycle25_4 : CycleData E W := ⟨2,![17,9,6,13],![6,22,13,14]⟩
def data25 : PartitionData E W := ⟨5,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,6,7,2,12,14,13,4,13,22,12,23,6,22,7,14,23]
def dst26 : E → W := ![4,6,7,2,12,14,13,2,13,22,12,23,4,22,7,14,23,6]
def cycle26_0 : CycleData E W := ⟨3,![3,15,6,8,0],![2,7,14,13,4]⟩
def cycle26_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle26_2 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle26_3 : CycleData E W := ⟨2,![7,9,10,4],![2,13,22,12]⟩
def cycle26_4 : CycleData E W := ⟨1,![11,16,5],![12,23,14]⟩
def data26 : PartitionData E W := ⟨5,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,6,7,2,12,14,13,4,13,22,12,23,6,22,14,7,23]
def dst27 : E → W := ![4,6,7,2,12,14,13,2,13,22,12,23,4,22,14,7,23,6]
def cycle27_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle27_1 : CycleData E W := ⟨2,![12,16,2,1],![4,23,7,6]⟩
def cycle27_2 : CycleData E W := ⟨2,![4,5,15,3],![2,12,14,7]⟩
def cycle27_3 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def cycle27_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,12,22]⟩
def data27 : PartitionData E W := ⟨5,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,6,7,2,12,14,13,4,13,23,12,22,6,14,22,7,23]
def dst28 : E → W := ![4,6,7,2,12,14,13,2,13,23,12,22,4,14,22,7,23,6]
def cycle28_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle28_1 : CycleData E W := ⟨2,![12,15,2,1],![4,22,7,6]⟩
def cycle28_2 : CycleData E W := ⟨2,![4,10,16,3],![2,12,23,7]⟩
def cycle28_3 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def cycle28_4 : CycleData E W := ⟨2,![17,9,6,13],![6,23,13,14]⟩
def data28 : PartitionData E W := ⟨5,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,6,7,2,12,14,13,4,13,23,12,22,6,14,23,7,22]
def dst29 : E → W := ![4,6,7,2,12,14,13,2,13,23,12,22,4,14,23,7,22,6]
def cycle29_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle29_1 : CycleData E W := ⟨2,![12,16,2,1],![4,22,7,6]⟩
def cycle29_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,23,7]⟩
def cycle29_3 : CycleData E W := ⟨2,![17,11,5,13],![6,22,12,14]⟩
def cycle29_4 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def data29 : PartitionData E W := ⟨5,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,6,7,2,12,14,13,4,13,23,12,22,6,22,7,14,23]
def dst30 : E → W := ![4,6,7,2,12,14,13,2,13,23,12,22,4,22,7,14,23,6]
def cycle30_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle30_1 : CycleData E W := ⟨2,![12,14,2,1],![4,22,7,6]⟩
def cycle30_2 : CycleData E W := ⟨2,![4,5,15,3],![2,12,14,7]⟩
def cycle30_3 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def cycle30_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,12,22]⟩
def data30 : PartitionData E W := ⟨5,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,6,7,2,12,14,13,4,13,23,12,22,6,22,14,7,23]
def dst31 : E → W := ![4,6,7,2,12,14,13,2,13,23,12,22,4,22,14,7,23,6]
def cycle31_0 : CycleData E W := ⟨3,![3,15,6,8,0],![2,7,14,13,4]⟩
def cycle31_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle31_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle31_3 : CycleData E W := ⟨2,![7,9,10,4],![2,13,23,12]⟩
def cycle31_4 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def data31 : PartitionData E W := ⟨5,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,23,6,14,22,7,23]
def dst32 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle32_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle32_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle32_2 : CycleData E W := ⟨2,![4,10,15,3],![2,13,22,7]⟩
def cycle32_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle32_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data32 : PartitionData E W := ⟨5,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,23,6,14,23,7,22]
def dst33 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle33_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle33_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle33_2 : CycleData E W := ⟨2,![4,11,15,3],![2,13,23,7]⟩
def cycle33_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle33_4 : CycleData E W := ⟨2,![12,14,6,8],![4,23,14,12]⟩
def data33 : PartitionData E W := ⟨5,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,23,6,22,7,14,23]
def dst34 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle34_0 : CycleData E W := ⟨3,![4,11,17,1,0],![2,13,23,6,4]⟩
def cycle34_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle34_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle34_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle34_4 : CycleData E W := ⟨2,![12,16,6,8],![4,23,14,12]⟩
def data34 : PartitionData E W := ⟨5,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,6,7,2,13,12,14,4,12,22,13,23,6,22,14,7,23]
def dst35 : E → W := ![4,6,7,2,13,12,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle35_0 : CycleData E W := ⟨3,![4,10,13,1,0],![2,13,22,6,4]⟩
def cycle35_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle35_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle35_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle35_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data35 : PartitionData E W := ⟨5,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def src36 : E → W := ![2,4,6,7,2,13,12,14,4,12,23,13,22,6,14,22,7,23]
def dst36 : E → W := ![4,6,7,2,13,12,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle36_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle36_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle36_2 : CycleData E W := ⟨2,![4,11,15,3],![2,13,22,7]⟩
def cycle36_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle36_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,12]⟩
def data36 : PartitionData E W := ⟨5,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4]⟩
lemma valid_data36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel

def src37 : E → W := ![2,4,6,7,2,13,12,14,4,12,23,13,22,6,14,23,7,22]
def dst37 : E → W := ![4,6,7,2,13,12,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle37_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle37_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle37_2 : CycleData E W := ⟨2,![4,10,15,3],![2,13,23,7]⟩
def cycle37_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle37_4 : CycleData E W := ⟨1,![9,14,6],![12,23,14]⟩
def data37 : PartitionData E W := ⟨5,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4]⟩
lemma valid_data37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel

def src38 : E → W := ![2,4,6,7,2,13,12,14,4,12,23,13,22,6,22,7,14,23]
def dst38 : E → W := ![4,6,7,2,13,12,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle38_0 : CycleData E W := ⟨3,![4,10,17,1,0],![2,13,23,6,4]⟩
def cycle38_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle38_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle38_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle38_4 : CycleData E W := ⟨1,![9,16,6],![12,23,14]⟩
def data38 : PartitionData E W := ⟨5,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4]⟩
lemma valid_data38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel

def src39 : E → W := ![2,4,6,7,2,13,12,14,4,12,23,13,22,6,22,14,7,23]
def dst39 : E → W := ![4,6,7,2,13,12,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle39_0 : CycleData E W := ⟨3,![4,11,13,1,0],![2,13,22,6,4]⟩
def cycle39_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle39_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle39_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle39_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,12]⟩
def data39 : PartitionData E W := ⟨5,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4]⟩
lemma valid_data39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel

def src40 : E → W := ![2,4,6,7,2,13,12,14,4,13,22,12,23,6,14,22,7,23]
def dst40 : E → W := ![4,6,7,2,13,12,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle40_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle40_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle40_2 : CycleData E W := ⟨2,![4,9,15,3],![2,13,22,7]⟩
def cycle40_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle40_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data40 : PartitionData E W := ⟨5,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4]⟩
lemma valid_data40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel

def src41 : E → W := ![2,4,6,7,2,13,12,14,4,13,22,12,23,6,14,23,7,22]
def dst41 : E → W := ![4,6,7,2,13,12,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle41_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle41_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle41_2 : CycleData E W := ⟨3,![4,8,12,15,3],![2,13,4,23,7]⟩
def cycle41_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle41_4 : CycleData E W := ⟨1,![11,14,6],![12,23,14]⟩
def data41 : PartitionData E W := ⟨5,![cycle41_0,cycle41_1,cycle41_2,cycle41_3,cycle41_4]⟩
lemma valid_data41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel

def src42 : E → W := ![2,4,6,7,2,13,12,14,4,13,22,12,23,6,22,7,14,23]
def dst42 : E → W := ![4,6,7,2,13,12,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle42_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle42_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle42_2 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle42_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle42_4 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle42_5 : CycleData E W := ⟨1,![11,16,6],![12,23,14]⟩
def data42 : PartitionData E W := ⟨6,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4,cycle42_5]⟩
lemma valid_data42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel

def src43 : E → W := ![2,4,6,7,2,13,12,14,4,13,22,12,23,6,22,14,7,23]
def dst43 : E → W := ![4,6,7,2,13,12,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle43_0 : CycleData E W := ⟨3,![4,9,13,1,0],![2,13,22,6,4]⟩
def cycle43_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle43_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle43_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle43_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data43 : PartitionData E W := ⟨5,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4]⟩
lemma valid_data43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel

def src44 : E → W := ![2,4,6,7,2,13,12,14,4,13,23,12,22,6,14,22,7,23]
def dst44 : E → W := ![4,6,7,2,13,12,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle44_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle44_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle44_2 : CycleData E W := ⟨3,![4,8,12,15,3],![2,13,4,22,7]⟩
def cycle44_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle44_4 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data44 : PartitionData E W := ⟨5,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4]⟩
lemma valid_data44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel

def src45 : E → W := ![2,4,6,7,2,13,12,14,4,13,23,12,22,6,14,23,7,22]
def dst45 : E → W := ![4,6,7,2,13,12,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle45_0 : CycleData E W := ⟨2,![7,13,1,0],![2,14,6,4]⟩
def cycle45_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle45_2 : CycleData E W := ⟨2,![4,9,15,3],![2,13,23,7]⟩
def cycle45_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle45_4 : CycleData E W := ⟨1,![10,14,6],![12,23,14]⟩
def data45 : PartitionData E W := ⟨5,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4]⟩
lemma valid_data45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel

def src46 : E → W := ![2,4,6,7,2,13,12,14,4,13,23,12,22,6,22,7,14,23]
def dst46 : E → W := ![4,6,7,2,13,12,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle46_0 : CycleData E W := ⟨3,![4,9,17,1,0],![2,13,23,6,4]⟩
def cycle46_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle46_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle46_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle46_4 : CycleData E W := ⟨1,![10,16,6],![12,23,14]⟩
def data46 : PartitionData E W := ⟨5,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4]⟩
lemma valid_data46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel

def src47 : E → W := ![2,4,6,7,2,13,12,14,4,13,23,12,22,6,22,14,7,23]
def dst47 : E → W := ![4,6,7,2,13,12,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle47_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle47_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle47_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle47_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle47_4 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle47_5 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data47 : PartitionData E W := ⟨6,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4,cycle47_5]⟩
lemma valid_data47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel

def src48 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,23,6,14,22,7,23]
def dst48 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle48_0 : CycleData E W := ⟨3,![4,9,15,1,0],![2,12,22,7,4]⟩
def cycle48_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle48_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle48_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle48_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data48 : PartitionData E W := ⟨5,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4]⟩
lemma valid_data48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel

def src49 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,23,6,14,23,7,22]
def dst49 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle49_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle49_1 : CycleData E W := ⟨1,![12,15,1],![4,23,7]⟩
def cycle49_2 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle49_3 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle49_4 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle49_5 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data49 : PartitionData E W := ⟨6,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4,cycle49_5]⟩
lemma valid_data49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel

def src50 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,23,6,22,7,14,23]
def dst50 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle50_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle50_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle50_2 : CycleData E W := ⟨3,![4,8,12,17,3],![2,12,4,23,6]⟩
def cycle50_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle50_4 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data50 : PartitionData E W := ⟨5,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4]⟩
lemma valid_data50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel

def src51 : E → W := ![2,4,7,6,2,12,13,14,4,12,22,13,23,6,22,14,7,23]
def dst51 : E → W := ![4,7,6,2,12,13,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle51_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle51_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle51_2 : CycleData E W := ⟨2,![4,9,13,3],![2,12,22,6]⟩
def cycle51_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle51_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data51 : PartitionData E W := ⟨5,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4]⟩
lemma valid_data51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel

def src52 : E → W := ![2,4,7,6,2,12,13,14,4,12,23,13,22,6,14,22,7,23]
def dst52 : E → W := ![4,7,6,2,12,13,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle52_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle52_1 : CycleData E W := ⟨1,![12,15,1],![4,22,7]⟩
def cycle52_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle52_3 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle52_4 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle52_5 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data52 : PartitionData E W := ⟨6,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5]⟩
lemma valid_data52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel

def src53 : E → W := ![2,4,7,6,2,12,13,14,4,12,23,13,22,6,14,23,7,22]
def dst53 : E → W := ![4,7,6,2,12,13,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle53_0 : CycleData E W := ⟨3,![4,9,15,1,0],![2,12,23,7,4]⟩
def cycle53_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle53_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle53_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle53_4 : CycleData E W := ⟨1,![10,14,6],![13,23,14]⟩
def data53 : PartitionData E W := ⟨5,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4]⟩
lemma valid_data53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel

def src54 : E → W := ![2,4,7,6,2,12,13,14,4,12,23,13,22,6,22,7,14,23]
def dst54 : E → W := ![4,7,6,2,12,13,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle54_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle54_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle54_2 : CycleData E W := ⟨2,![4,9,17,3],![2,12,23,6]⟩
def cycle54_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle54_4 : CycleData E W := ⟨1,![10,16,6],![13,23,14]⟩
def data54 : PartitionData E W := ⟨5,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4]⟩
lemma valid_data54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel

def src55 : E → W := ![2,4,7,6,2,12,13,14,4,12,23,13,22,6,22,14,7,23]
def dst55 : E → W := ![4,7,6,2,12,13,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle55_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle55_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle55_2 : CycleData E W := ⟨3,![4,8,12,13,3],![2,12,4,22,6]⟩
def cycle55_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle55_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data55 : PartitionData E W := ⟨5,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4]⟩
lemma valid_data55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel

def src56 : E → W := ![2,4,7,6,2,12,13,14,4,13,22,12,23,6,14,22,7,23]
def dst56 : E → W := ![4,7,6,2,12,13,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle56_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,12,22,7,4]⟩
def cycle56_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle56_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle56_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle56_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data56 : PartitionData E W := ⟨5,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4]⟩
lemma valid_data56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel

def src57 : E → W := ![2,4,7,6,2,12,13,14,4,13,22,12,23,6,14,23,7,22]
def dst57 : E → W := ![4,7,6,2,12,13,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle57_0 : CycleData E W := ⟨3,![4,11,15,1,0],![2,12,23,7,4]⟩
def cycle57_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle57_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle57_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle57_4 : CycleData E W := ⟨2,![12,14,6,8],![4,23,14,13]⟩
def data57 : PartitionData E W := ⟨5,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4]⟩
lemma valid_data57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel

def src58 : E → W := ![2,4,7,6,2,12,13,14,4,13,22,12,23,6,22,7,14,23]
def dst58 : E → W := ![4,7,6,2,12,13,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle58_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle58_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle58_2 : CycleData E W := ⟨2,![4,11,17,3],![2,12,23,6]⟩
def cycle58_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle58_4 : CycleData E W := ⟨2,![12,16,6,8],![4,23,14,13]⟩
def data58 : PartitionData E W := ⟨5,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4]⟩
lemma valid_data58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel

def src59 : E → W := ![2,4,7,6,2,12,13,14,4,13,22,12,23,6,22,14,7,23]
def dst59 : E → W := ![4,7,6,2,12,13,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle59_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle59_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle59_2 : CycleData E W := ⟨2,![4,10,13,3],![2,12,22,6]⟩
def cycle59_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle59_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data59 : PartitionData E W := ⟨5,![cycle59_0,cycle59_1,cycle59_2,cycle59_3,cycle59_4]⟩
lemma valid_data59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel

def src60 : E → W := ![2,4,7,6,2,12,13,14,4,13,23,12,22,6,14,22,7,23]
def dst60 : E → W := ![4,7,6,2,12,13,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle60_0 : CycleData E W := ⟨3,![4,11,15,1,0],![2,12,22,7,4]⟩
def cycle60_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle60_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle60_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle60_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,13]⟩
def data60 : PartitionData E W := ⟨5,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4]⟩
lemma valid_data60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel

def src61 : E → W := ![2,4,7,6,2,12,13,14,4,13,23,12,22,6,14,23,7,22]
def dst61 : E → W := ![4,7,6,2,12,13,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle61_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,12,23,7,4]⟩
def cycle61_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle61_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle61_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle61_4 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def data61 : PartitionData E W := ⟨5,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4]⟩
lemma valid_data61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel

def src62 : E → W := ![2,4,7,6,2,12,13,14,4,13,23,12,22,6,22,7,14,23]
def dst62 : E → W := ![4,7,6,2,12,13,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle62_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle62_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle62_2 : CycleData E W := ⟨2,![4,10,17,3],![2,12,23,6]⟩
def cycle62_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle62_4 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def data62 : PartitionData E W := ⟨5,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4]⟩
lemma valid_data62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel

def src63 : E → W := ![2,4,7,6,2,12,13,14,4,13,23,12,22,6,22,14,7,23]
def dst63 : E → W := ![4,7,6,2,12,13,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle63_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle63_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle63_2 : CycleData E W := ⟨2,![4,11,13,3],![2,12,22,6]⟩
def cycle63_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle63_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,13]⟩
def data63 : PartitionData E W := ⟨5,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4]⟩
lemma valid_data63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel

def src64 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,23,6,14,22,7,23]
def dst64 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,23,4,14,22,7,23,6]
def cycle64_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle64_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle64_2 : CycleData E W := ⟨2,![7,6,13,3],![2,13,14,6]⟩
def cycle64_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle64_4 : CycleData E W := ⟨2,![16,11,10,15],![7,23,13,22]⟩
def data64 : PartitionData E W := ⟨5,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4]⟩
lemma valid_data64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel

def src65 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,23,6,14,23,7,22]
def dst65 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,23,4,14,23,7,22,6]
def cycle65_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle65_1 : CycleData E W := ⟨1,![12,15,1],![4,23,7]⟩
def cycle65_2 : CycleData E W := ⟨3,![7,10,16,2,3],![2,13,22,7,6]⟩
def cycle65_3 : CycleData E W := ⟨2,![17,9,5,13],![6,22,12,14]⟩
def cycle65_4 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data65 : PartitionData E W := ⟨5,![cycle65_0,cycle65_1,cycle65_2,cycle65_3,cycle65_4]⟩
lemma valid_data65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel

def src66 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,23,6,22,7,14,23]
def dst66 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,23,4,22,7,14,23,6]
def cycle66_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle66_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle66_2 : CycleData E W := ⟨2,![7,10,13,3],![2,13,22,6]⟩
def cycle66_3 : CycleData E W := ⟨2,![15,5,9,14],![7,14,12,22]⟩
def cycle66_4 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data66 : PartitionData E W := ⟨5,![cycle66_0,cycle66_1,cycle66_2,cycle66_3,cycle66_4]⟩
lemma valid_data66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel

def src67 : E → W := ![2,4,7,6,2,12,14,13,4,12,22,13,23,6,22,14,7,23]
def dst67 : E → W := ![4,7,6,2,12,14,13,2,12,22,13,23,4,22,14,7,23,6]
def cycle67_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle67_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle67_2 : CycleData E W := ⟨2,![7,10,13,3],![2,13,22,6]⟩
def cycle67_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle67_4 : CycleData E W := ⟨2,![16,11,6,15],![7,23,13,14]⟩
def data67 : PartitionData E W := ⟨5,![cycle67_0,cycle67_1,cycle67_2,cycle67_3,cycle67_4]⟩
lemma valid_data67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel

def src68 : E → W := ![2,4,7,6,2,12,14,13,4,12,23,13,22,6,14,22,7,23]
def dst68 : E → W := ![4,7,6,2,12,14,13,2,12,23,13,22,4,14,22,7,23,6]
def cycle68_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle68_1 : CycleData E W := ⟨1,![12,15,1],![4,22,7]⟩
def cycle68_2 : CycleData E W := ⟨3,![7,10,16,2,3],![2,13,23,7,6]⟩
def cycle68_3 : CycleData E W := ⟨2,![17,9,5,13],![6,23,12,14]⟩
def cycle68_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data68 : PartitionData E W := ⟨5,![cycle68_0,cycle68_1,cycle68_2,cycle68_3,cycle68_4]⟩
lemma valid_data68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel

def src69 : E → W := ![2,4,7,6,2,12,14,13,4,12,23,13,22,6,14,23,7,22]
def dst69 : E → W := ![4,7,6,2,12,14,13,2,12,23,13,22,4,14,23,7,22,6]
def cycle69_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle69_1 : CycleData E W := ⟨2,![12,17,2,1],![4,22,6,7]⟩
def cycle69_2 : CycleData E W := ⟨2,![7,6,13,3],![2,13,14,6]⟩
def cycle69_3 : CycleData E W := ⟨1,![9,14,5],![12,23,14]⟩
def cycle69_4 : CycleData E W := ⟨2,![16,11,10,15],![7,22,13,23]⟩
def data69 : PartitionData E W := ⟨5,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4]⟩
lemma valid_data69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel

def src70 : E → W := ![2,4,7,6,2,12,14,13,4,12,23,13,22,6,22,7,14,23]
def dst70 : E → W := ![4,7,6,2,12,14,13,2,12,23,13,22,4,22,7,14,23,6]
def cycle70_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle70_1 : CycleData E W := ⟨2,![12,13,2,1],![4,22,6,7]⟩
def cycle70_2 : CycleData E W := ⟨2,![7,10,17,3],![2,13,23,6]⟩
def cycle70_3 : CycleData E W := ⟨1,![9,16,5],![12,23,14]⟩
def cycle70_4 : CycleData E W := ⟨2,![15,6,11,14],![7,14,13,22]⟩
def data70 : PartitionData E W := ⟨5,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4]⟩
lemma valid_data70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel

def src71 : E → W := ![2,4,7,6,2,12,14,13,4,12,23,13,22,6,22,14,7,23]
def dst71 : E → W := ![4,7,6,2,12,14,13,2,12,23,13,22,4,22,14,7,23,6]
def cycle71_0 : CycleData E W := ⟨1,![4,8,0],![2,12,4]⟩
def cycle71_1 : CycleData E W := ⟨2,![12,13,2,1],![4,22,6,7]⟩
def cycle71_2 : CycleData E W := ⟨2,![7,10,17,3],![2,13,23,6]⟩
def cycle71_3 : CycleData E W := ⟨2,![16,9,5,15],![7,23,12,14]⟩
def cycle71_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data71 : PartitionData E W := ⟨5,![cycle71_0,cycle71_1,cycle71_2,cycle71_3,cycle71_4]⟩
lemma valid_data71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel

def src72 : E → W := ![2,4,7,6,2,12,14,13,4,13,22,12,23,6,14,22,7,23]
def dst72 : E → W := ![4,7,6,2,12,14,13,2,13,22,12,23,4,14,22,7,23,6]
def cycle72_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle72_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle72_2 : CycleData E W := ⟨2,![4,5,13,3],![2,12,14,6]⟩
def cycle72_3 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def cycle72_4 : CycleData E W := ⟨2,![16,11,10,15],![7,23,12,22]⟩
def data72 : PartitionData E W := ⟨5,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4]⟩
lemma valid_data72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel

def src73 : E → W := ![2,4,7,6,2,12,14,13,4,13,22,12,23,6,14,23,7,22]
def dst73 : E → W := ![4,7,6,2,12,14,13,2,13,22,12,23,4,14,23,7,22,6]
def cycle73_0 : CycleData E W := ⟨3,![3,13,6,8,0],![2,6,14,13,4]⟩
def cycle73_1 : CycleData E W := ⟨1,![12,15,1],![4,23,7]⟩
def cycle73_2 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle73_3 : CycleData E W := ⟨2,![7,9,10,4],![2,13,22,12]⟩
def cycle73_4 : CycleData E W := ⟨1,![11,14,5],![12,23,14]⟩
def data73 : PartitionData E W := ⟨5,![cycle73_0,cycle73_1,cycle73_2,cycle73_3,cycle73_4]⟩
lemma valid_data73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel

def src74 : E → W := ![2,4,7,6,2,12,14,13,4,13,22,12,23,6,22,7,14,23]
def dst74 : E → W := ![4,7,6,2,12,14,13,2,13,22,12,23,4,22,7,14,23,6]
def cycle74_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle74_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle74_2 : CycleData E W := ⟨2,![4,10,13,3],![2,12,22,6]⟩
def cycle74_3 : CycleData E W := ⟨1,![11,16,5],![12,23,14]⟩
def cycle74_4 : CycleData E W := ⟨2,![15,6,9,14],![7,14,13,22]⟩
def data74 : PartitionData E W := ⟨5,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4]⟩
lemma valid_data74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel

def src75 : E → W := ![2,4,7,6,2,12,14,13,4,13,22,12,23,6,22,14,7,23]
def dst75 : E → W := ![4,7,6,2,12,14,13,2,13,22,12,23,4,22,14,7,23,6]
def cycle75_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle75_1 : CycleData E W := ⟨2,![12,17,2,1],![4,23,6,7]⟩
def cycle75_2 : CycleData E W := ⟨2,![4,10,13,3],![2,12,22,6]⟩
def cycle75_3 : CycleData E W := ⟨2,![16,11,5,15],![7,23,12,14]⟩
def cycle75_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data75 : PartitionData E W := ⟨5,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4]⟩
lemma valid_data75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel

def src76 : E → W := ![2,4,7,6,2,12,14,13,4,13,23,12,22,6,14,22,7,23]
def dst76 : E → W := ![4,7,6,2,12,14,13,2,13,23,12,22,4,14,22,7,23,6]
def cycle76_0 : CycleData E W := ⟨3,![3,13,6,8,0],![2,6,14,13,4]⟩
def cycle76_1 : CycleData E W := ⟨1,![12,15,1],![4,22,7]⟩
def cycle76_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle76_3 : CycleData E W := ⟨2,![7,9,10,4],![2,13,23,12]⟩
def cycle76_4 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def data76 : PartitionData E W := ⟨5,![cycle76_0,cycle76_1,cycle76_2,cycle76_3,cycle76_4]⟩
lemma valid_data76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel

def src77 : E → W := ![2,4,7,6,2,12,14,13,4,13,23,12,22,6,14,23,7,22]
def dst77 : E → W := ![4,7,6,2,12,14,13,2,13,23,12,22,4,14,23,7,22,6]
def cycle77_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle77_1 : CycleData E W := ⟨2,![12,17,2,1],![4,22,6,7]⟩
def cycle77_2 : CycleData E W := ⟨2,![4,5,13,3],![2,12,14,6]⟩
def cycle77_3 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def cycle77_4 : CycleData E W := ⟨2,![16,11,10,15],![7,22,12,23]⟩
def data77 : PartitionData E W := ⟨5,![cycle77_0,cycle77_1,cycle77_2,cycle77_3,cycle77_4]⟩
lemma valid_data77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel

def src78 : E → W := ![2,4,7,6,2,12,14,13,4,13,23,12,22,6,22,7,14,23]
def dst78 : E → W := ![4,7,6,2,12,14,13,2,13,23,12,22,4,22,7,14,23,6]
def cycle78_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle78_1 : CycleData E W := ⟨2,![12,13,2,1],![4,22,6,7]⟩
def cycle78_2 : CycleData E W := ⟨2,![4,10,17,3],![2,12,23,6]⟩
def cycle78_3 : CycleData E W := ⟨2,![15,5,11,14],![7,14,12,22]⟩
def cycle78_4 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def data78 : PartitionData E W := ⟨5,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4]⟩
lemma valid_data78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel

def src79 : E → W := ![2,4,7,6,2,12,14,13,4,13,23,12,22,6,22,14,7,23]
def dst79 : E → W := ![4,7,6,2,12,14,13,2,13,23,12,22,4,22,14,7,23,6]
def cycle79_0 : CycleData E W := ⟨1,![7,8,0],![2,13,4]⟩
def cycle79_1 : CycleData E W := ⟨2,![12,13,2,1],![4,22,6,7]⟩
def cycle79_2 : CycleData E W := ⟨2,![4,10,17,3],![2,12,23,6]⟩
def cycle79_3 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def cycle79_4 : CycleData E W := ⟨2,![16,9,6,15],![7,23,13,14]⟩
def data79 : PartitionData E W := ⟨5,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4]⟩
lemma valid_data79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel

def src80 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,23,6,14,22,7,23]
def dst80 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle80_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,13,22,7,4]⟩
def cycle80_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle80_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle80_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle80_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data80 : PartitionData E W := ⟨5,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4]⟩
lemma valid_data80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel

def src81 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,23,6,14,23,7,22]
def dst81 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle81_0 : CycleData E W := ⟨3,![4,11,15,1,0],![2,13,23,7,4]⟩
def cycle81_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle81_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle81_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle81_4 : CycleData E W := ⟨2,![12,14,6,8],![4,23,14,12]⟩
def data81 : PartitionData E W := ⟨5,![cycle81_0,cycle81_1,cycle81_2,cycle81_3,cycle81_4]⟩
lemma valid_data81 : data81.Valid src81 dst81 Finset.univ := by decide +kernel

def src82 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,23,6,22,7,14,23]
def dst82 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle82_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle82_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle82_2 : CycleData E W := ⟨2,![4,11,17,3],![2,13,23,6]⟩
def cycle82_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle82_4 : CycleData E W := ⟨2,![12,16,6,8],![4,23,14,12]⟩
def data82 : PartitionData E W := ⟨5,![cycle82_0,cycle82_1,cycle82_2,cycle82_3,cycle82_4]⟩
lemma valid_data82 : data82.Valid src82 dst82 Finset.univ := by decide +kernel

def src83 : E → W := ![2,4,7,6,2,13,12,14,4,12,22,13,23,6,22,14,7,23]
def dst83 : E → W := ![4,7,6,2,13,12,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle83_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle83_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle83_2 : CycleData E W := ⟨2,![4,10,13,3],![2,13,22,6]⟩
def cycle83_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,13,12]⟩
def cycle83_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data83 : PartitionData E W := ⟨5,![cycle83_0,cycle83_1,cycle83_2,cycle83_3,cycle83_4]⟩
lemma valid_data83 : data83.Valid src83 dst83 Finset.univ := by decide +kernel

def src84 : E → W := ![2,4,7,6,2,13,12,14,4,12,23,13,22,6,14,22,7,23]
def dst84 : E → W := ![4,7,6,2,13,12,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle84_0 : CycleData E W := ⟨3,![4,11,15,1,0],![2,13,22,7,4]⟩
def cycle84_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle84_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle84_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle84_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,12]⟩
def data84 : PartitionData E W := ⟨5,![cycle84_0,cycle84_1,cycle84_2,cycle84_3,cycle84_4]⟩
lemma valid_data84 : data84.Valid src84 dst84 Finset.univ := by decide +kernel

def src85 : E → W := ![2,4,7,6,2,13,12,14,4,12,23,13,22,6,14,23,7,22]
def dst85 : E → W := ![4,7,6,2,13,12,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle85_0 : CycleData E W := ⟨3,![4,10,15,1,0],![2,13,23,7,4]⟩
def cycle85_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle85_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle85_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle85_4 : CycleData E W := ⟨1,![9,14,6],![12,23,14]⟩
def data85 : PartitionData E W := ⟨5,![cycle85_0,cycle85_1,cycle85_2,cycle85_3,cycle85_4]⟩
lemma valid_data85 : data85.Valid src85 dst85 Finset.univ := by decide +kernel

def src86 : E → W := ![2,4,7,6,2,13,12,14,4,12,23,13,22,6,22,7,14,23]
def dst86 : E → W := ![4,7,6,2,13,12,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle86_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle86_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle86_2 : CycleData E W := ⟨2,![4,10,17,3],![2,13,23,6]⟩
def cycle86_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,13,12]⟩
def cycle86_4 : CycleData E W := ⟨1,![9,16,6],![12,23,14]⟩
def data86 : PartitionData E W := ⟨5,![cycle86_0,cycle86_1,cycle86_2,cycle86_3,cycle86_4]⟩
lemma valid_data86 : data86.Valid src86 dst86 Finset.univ := by decide +kernel

def src87 : E → W := ![2,4,7,6,2,13,12,14,4,12,23,13,22,6,22,14,7,23]
def dst87 : E → W := ![4,7,6,2,13,12,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle87_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle87_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle87_2 : CycleData E W := ⟨2,![4,11,13,3],![2,13,22,6]⟩
def cycle87_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle87_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,12]⟩
def data87 : PartitionData E W := ⟨5,![cycle87_0,cycle87_1,cycle87_2,cycle87_3,cycle87_4]⟩
lemma valid_data87 : data87.Valid src87 dst87 Finset.univ := by decide +kernel

def src88 : E → W := ![2,4,7,6,2,13,12,14,4,13,22,12,23,6,14,22,7,23]
def dst88 : E → W := ![4,7,6,2,13,12,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle88_0 : CycleData E W := ⟨3,![4,9,15,1,0],![2,13,22,7,4]⟩
def cycle88_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle88_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle88_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle88_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data88 : PartitionData E W := ⟨5,![cycle88_0,cycle88_1,cycle88_2,cycle88_3,cycle88_4]⟩
lemma valid_data88 : data88.Valid src88 dst88 Finset.univ := by decide +kernel

def src89 : E → W := ![2,4,7,6,2,13,12,14,4,13,22,12,23,6,14,23,7,22]
def dst89 : E → W := ![4,7,6,2,13,12,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle89_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle89_1 : CycleData E W := ⟨1,![12,15,1],![4,23,7]⟩
def cycle89_2 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle89_3 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle89_4 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle89_5 : CycleData E W := ⟨1,![11,14,6],![12,23,14]⟩
def data89 : PartitionData E W := ⟨6,![cycle89_0,cycle89_1,cycle89_2,cycle89_3,cycle89_4,cycle89_5]⟩
lemma valid_data89 : data89.Valid src89 dst89 Finset.univ := by decide +kernel

def src90 : E → W := ![2,4,7,6,2,13,12,14,4,13,22,12,23,6,22,7,14,23]
def dst90 : E → W := ![4,7,6,2,13,12,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle90_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle90_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle90_2 : CycleData E W := ⟨3,![4,8,12,17,3],![2,13,4,23,6]⟩
def cycle90_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle90_4 : CycleData E W := ⟨1,![11,16,6],![12,23,14]⟩
def data90 : PartitionData E W := ⟨5,![cycle90_0,cycle90_1,cycle90_2,cycle90_3,cycle90_4]⟩
lemma valid_data90 : data90.Valid src90 dst90 Finset.univ := by decide +kernel

def src91 : E → W := ![2,4,7,6,2,13,12,14,4,13,22,12,23,6,22,14,7,23]
def dst91 : E → W := ![4,7,6,2,13,12,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle91_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle91_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle91_2 : CycleData E W := ⟨2,![4,9,13,3],![2,13,22,6]⟩
def cycle91_3 : CycleData E W := ⟨2,![12,11,5,8],![4,23,12,13]⟩
def cycle91_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data91 : PartitionData E W := ⟨5,![cycle91_0,cycle91_1,cycle91_2,cycle91_3,cycle91_4]⟩
lemma valid_data91 : data91.Valid src91 dst91 Finset.univ := by decide +kernel

def src92 : E → W := ![2,4,7,6,2,13,12,14,4,13,23,12,22,6,14,22,7,23]
def dst92 : E → W := ![4,7,6,2,13,12,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle92_0 : CycleData E W := ⟨1,![4,8,0],![2,13,4]⟩
def cycle92_1 : CycleData E W := ⟨1,![12,15,1],![4,22,7]⟩
def cycle92_2 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle92_3 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle92_4 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle92_5 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data92 : PartitionData E W := ⟨6,![cycle92_0,cycle92_1,cycle92_2,cycle92_3,cycle92_4,cycle92_5]⟩
lemma valid_data92 : data92.Valid src92 dst92 Finset.univ := by decide +kernel

def src93 : E → W := ![2,4,7,6,2,13,12,14,4,13,23,12,22,6,14,23,7,22]
def dst93 : E → W := ![4,7,6,2,13,12,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle93_0 : CycleData E W := ⟨3,![4,9,15,1,0],![2,13,23,7,4]⟩
def cycle93_1 : CycleData E W := ⟨1,![17,16,2],![6,22,7]⟩
def cycle93_2 : CycleData E W := ⟨1,![7,13,3],![2,14,6]⟩
def cycle93_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle93_4 : CycleData E W := ⟨1,![10,14,6],![12,23,14]⟩
def data93 : PartitionData E W := ⟨5,![cycle93_0,cycle93_1,cycle93_2,cycle93_3,cycle93_4]⟩
lemma valid_data93 : data93.Valid src93 dst93 Finset.univ := by decide +kernel

def src94 : E → W := ![2,4,7,6,2,13,12,14,4,13,23,12,22,6,22,7,14,23]
def dst94 : E → W := ![4,7,6,2,13,12,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle94_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle94_1 : CycleData E W := ⟨1,![13,14,2],![6,22,7]⟩
def cycle94_2 : CycleData E W := ⟨2,![4,9,17,3],![2,13,23,6]⟩
def cycle94_3 : CycleData E W := ⟨2,![12,11,5,8],![4,22,12,13]⟩
def cycle94_4 : CycleData E W := ⟨1,![10,16,6],![12,23,14]⟩
def data94 : PartitionData E W := ⟨5,![cycle94_0,cycle94_1,cycle94_2,cycle94_3,cycle94_4]⟩
lemma valid_data94 : data94.Valid src94 dst94 Finset.univ := by decide +kernel

def src95 : E → W := ![2,4,7,6,2,13,12,14,4,13,23,12,22,6,22,14,7,23]
def dst95 : E → W := ![4,7,6,2,13,12,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle95_0 : CycleData E W := ⟨2,![7,15,1,0],![2,14,7,4]⟩
def cycle95_1 : CycleData E W := ⟨1,![17,16,2],![6,23,7]⟩
def cycle95_2 : CycleData E W := ⟨3,![4,8,12,13,3],![2,13,4,22,6]⟩
def cycle95_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle95_4 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data95 : PartitionData E W := ⟨5,![cycle95_0,cycle95_1,cycle95_2,cycle95_3,cycle95_4]⟩
lemma valid_data95 : data95.Valid src95 dst95 Finset.univ := by decide +kernel

def src96 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,23,6,14,22,7,23]
def dst96 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle96_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle96_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle96_2 : CycleData E W := ⟨2,![7,14,15,3],![2,14,22,7]⟩
def cycle96_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle96_4 : CycleData E W := ⟨2,![17,11,6,13],![6,23,13,14]⟩
def data96 : PartitionData E W := ⟨5,![cycle96_0,cycle96_1,cycle96_2,cycle96_3,cycle96_4]⟩
lemma valid_data96 : data96.Valid src96 dst96 Finset.univ := by decide +kernel

def src97 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,23,6,14,23,7,22]
def dst97 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle97_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle97_1 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle97_2 : CycleData E W := ⟨3,![7,13,17,16,3],![2,14,6,22,7]⟩
def cycle97_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle97_4 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data97 : PartitionData E W := ⟨5,![cycle97_0,cycle97_1,cycle97_2,cycle97_3,cycle97_4]⟩
lemma valid_data97 : data97.Valid src97 dst97 Finset.univ := by decide +kernel

def src98 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,23,6,22,7,14,23]
def dst98 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle98_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle98_1 : CycleData E W := ⟨3,![12,17,13,14,2],![4,23,6,22,7]⟩
def cycle98_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle98_3 : CycleData E W := ⟨1,![9,10,5],![12,22,13]⟩
def cycle98_4 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data98 : PartitionData E W := ⟨5,![cycle98_0,cycle98_1,cycle98_2,cycle98_3,cycle98_4]⟩
lemma valid_data98 : data98.Valid src98 dst98 Finset.univ := by decide +kernel

def src99 : E → W := ![2,6,4,7,2,12,13,14,4,12,22,13,23,6,22,14,7,23]
def dst99 : E → W := ![6,4,7,2,12,13,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle99_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle99_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle99_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle99_3 : CycleData E W := ⟨3,![17,11,5,9,13],![6,23,13,12,22]⟩
def cycle99_4 : CycleData E W := ⟨1,![10,14,6],![13,22,14]⟩
def data99 : PartitionData E W := ⟨5,![cycle99_0,cycle99_1,cycle99_2,cycle99_3,cycle99_4]⟩
lemma valid_data99 : data99.Valid src99 dst99 Finset.univ := by decide +kernel

def src100 : E → W := ![2,6,4,7,2,12,13,14,4,12,23,13,22,6,14,22,7,23]
def dst100 : E → W := ![6,4,7,2,12,13,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle100_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle100_1 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle100_2 : CycleData E W := ⟨3,![7,13,17,16,3],![2,14,6,23,7]⟩
def cycle100_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle100_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data100 : PartitionData E W := ⟨5,![cycle100_0,cycle100_1,cycle100_2,cycle100_3,cycle100_4]⟩
lemma valid_data100 : data100.Valid src100 dst100 Finset.univ := by decide +kernel

def src101 : E → W := ![2,6,4,7,2,12,13,14,4,12,23,13,22,6,14,23,7,22]
def dst101 : E → W := ![6,4,7,2,12,13,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle101_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle101_1 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle101_2 : CycleData E W := ⟨2,![7,14,15,3],![2,14,23,7]⟩
def cycle101_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle101_4 : CycleData E W := ⟨2,![17,11,6,13],![6,22,13,14]⟩
def data101 : PartitionData E W := ⟨5,![cycle101_0,cycle101_1,cycle101_2,cycle101_3,cycle101_4]⟩
lemma valid_data101 : data101.Valid src101 dst101 Finset.univ := by decide +kernel

def src102 : E → W := ![2,6,4,7,2,12,13,14,4,12,23,13,22,6,22,7,14,23]
def dst102 : E → W := ![6,4,7,2,12,13,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle102_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle102_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle102_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle102_3 : CycleData E W := ⟨3,![17,9,5,11,13],![6,23,12,13,22]⟩
def cycle102_4 : CycleData E W := ⟨1,![10,16,6],![13,23,14]⟩
def data102 : PartitionData E W := ⟨5,![cycle102_0,cycle102_1,cycle102_2,cycle102_3,cycle102_4]⟩
lemma valid_data102 : data102.Valid src102 dst102 Finset.univ := by decide +kernel

def src103 : E → W := ![2,6,4,7,2,12,13,14,4,12,23,13,22,6,22,14,7,23]
def dst103 : E → W := ![6,4,7,2,12,13,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle103_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle103_1 : CycleData E W := ⟨3,![12,13,17,16,2],![4,22,6,23,7]⟩
def cycle103_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle103_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle103_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data103 : PartitionData E W := ⟨5,![cycle103_0,cycle103_1,cycle103_2,cycle103_3,cycle103_4]⟩
lemma valid_data103 : data103.Valid src103 dst103 Finset.univ := by decide +kernel

def src104 : E → W := ![2,6,4,7,2,12,13,14,4,13,22,12,23,6,14,22,7,23]
def dst104 : E → W := ![6,4,7,2,12,13,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle104_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle104_1 : CycleData E W := ⟨3,![8,5,11,17,1],![4,13,12,23,6]⟩
def cycle104_2 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle104_3 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,7]⟩
def cycle104_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data104 : PartitionData E W := ⟨5,![cycle104_0,cycle104_1,cycle104_2,cycle104_3,cycle104_4]⟩
lemma valid_data104 : data104.Valid src104 dst104 Finset.univ := by decide +kernel

def src105 : E → W := ![2,6,4,7,2,12,13,14,4,13,22,12,23,6,14,23,7,22]
def dst105 : E → W := ![6,4,7,2,12,13,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle105_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle105_1 : CycleData E W := ⟨2,![8,9,17,1],![4,13,22,6]⟩
def cycle105_2 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle105_3 : CycleData E W := ⟨2,![4,10,16,3],![2,12,22,7]⟩
def cycle105_4 : CycleData E W := ⟨2,![11,14,6,5],![12,23,14,13]⟩
def data105 : PartitionData E W := ⟨5,![cycle105_0,cycle105_1,cycle105_2,cycle105_3,cycle105_4]⟩
lemma valid_data105 : data105.Valid src105 dst105 Finset.univ := by decide +kernel

def src106 : E → W := ![2,6,4,7,2,12,13,14,4,13,22,12,23,6,22,7,14,23]
def dst106 : E → W := ![6,4,7,2,12,13,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle106_0 : CycleData E W := ⟨2,![4,10,13,0],![2,12,22,6]⟩
def cycle106_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle106_2 : CycleData E W := ⟨2,![8,9,14,2],![4,13,22,7]⟩
def cycle106_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle106_4 : CycleData E W := ⟨2,![11,16,6,5],![12,23,14,13]⟩
def data106 : PartitionData E W := ⟨5,![cycle106_0,cycle106_1,cycle106_2,cycle106_3,cycle106_4]⟩
lemma valid_data106 : data106.Valid src106 dst106 Finset.univ := by decide +kernel

def src107 : E → W := ![2,6,4,7,2,12,13,14,4,13,22,12,23,6,22,14,7,23]
def dst107 : E → W := ![6,4,7,2,12,13,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle107_0 : CycleData E W := ⟨3,![4,5,8,1,0],![2,12,13,4,6]⟩
def cycle107_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle107_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle107_3 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def cycle107_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,12,22]⟩
def data107 : PartitionData E W := ⟨5,![cycle107_0,cycle107_1,cycle107_2,cycle107_3,cycle107_4]⟩
lemma valid_data107 : data107.Valid src107 dst107 Finset.univ := by decide +kernel

def src108 : E → W := ![2,6,4,7,2,12,13,14,4,13,23,12,22,6,14,22,7,23]
def dst108 : E → W := ![6,4,7,2,12,13,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle108_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle108_1 : CycleData E W := ⟨2,![8,9,17,1],![4,13,23,6]⟩
def cycle108_2 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle108_3 : CycleData E W := ⟨2,![4,10,16,3],![2,12,23,7]⟩
def cycle108_4 : CycleData E W := ⟨2,![11,14,6,5],![12,22,14,13]⟩
def data108 : PartitionData E W := ⟨5,![cycle108_0,cycle108_1,cycle108_2,cycle108_3,cycle108_4]⟩
lemma valid_data108 : data108.Valid src108 dst108 Finset.univ := by decide +kernel

def src109 : E → W := ![2,6,4,7,2,12,13,14,4,13,23,12,22,6,14,23,7,22]
def dst109 : E → W := ![6,4,7,2,12,13,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle109_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle109_1 : CycleData E W := ⟨3,![8,5,11,17,1],![4,13,12,22,6]⟩
def cycle109_2 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle109_3 : CycleData E W := ⟨2,![4,10,15,3],![2,12,23,7]⟩
def cycle109_4 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def data109 : PartitionData E W := ⟨5,![cycle109_0,cycle109_1,cycle109_2,cycle109_3,cycle109_4]⟩
lemma valid_data109 : data109.Valid src109 dst109 Finset.univ := by decide +kernel

def src110 : E → W := ![2,6,4,7,2,12,13,14,4,13,23,12,22,6,22,7,14,23]
def dst110 : E → W := ![6,4,7,2,12,13,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle110_0 : CycleData E W := ⟨3,![4,5,8,1,0],![2,12,13,4,6]⟩
def cycle110_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle110_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle110_3 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def cycle110_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,12,22]⟩
def data110 : PartitionData E W := ⟨5,![cycle110_0,cycle110_1,cycle110_2,cycle110_3,cycle110_4]⟩
lemma valid_data110 : data110.Valid src110 dst110 Finset.univ := by decide +kernel

def src111 : E → W := ![2,6,4,7,2,12,13,14,4,13,23,12,22,6,22,14,7,23]
def dst111 : E → W := ![6,4,7,2,12,13,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle111_0 : CycleData E W := ⟨2,![4,11,13,0],![2,12,22,6]⟩
def cycle111_1 : CycleData E W := ⟨2,![2,16,17,1],![4,7,23,6]⟩
def cycle111_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle111_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle111_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,13]⟩
def data111 : PartitionData E W := ⟨5,![cycle111_0,cycle111_1,cycle111_2,cycle111_3,cycle111_4]⟩
lemma valid_data111 : data111.Valid src111 dst111 Finset.univ := by decide +kernel

def src112 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,23,6,14,22,7,23]
def dst112 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,23,4,14,22,7,23,6]
def cycle112_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle112_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle112_2 : CycleData E W := ⟨2,![7,10,15,3],![2,13,22,7]⟩
def cycle112_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle112_4 : CycleData E W := ⟨2,![17,11,6,13],![6,23,13,14]⟩
def data112 : PartitionData E W := ⟨5,![cycle112_0,cycle112_1,cycle112_2,cycle112_3,cycle112_4]⟩
lemma valid_data112 : data112.Valid src112 dst112 Finset.univ := by decide +kernel

def src113 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,23,6,14,23,7,22]
def dst113 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,23,4,14,23,7,22,6]
def cycle113_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle113_1 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle113_2 : CycleData E W := ⟨2,![7,10,16,3],![2,13,22,7]⟩
def cycle113_3 : CycleData E W := ⟨2,![17,9,5,13],![6,22,12,14]⟩
def cycle113_4 : CycleData E W := ⟨1,![11,14,6],![13,23,14]⟩
def data113 : PartitionData E W := ⟨5,![cycle113_0,cycle113_1,cycle113_2,cycle113_3,cycle113_4]⟩
lemma valid_data113 : data113.Valid src113 dst113 Finset.univ := by decide +kernel

def src114 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,23,6,22,7,14,23]
def dst114 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,23,4,22,7,14,23,6]
def cycle114_0 : CycleData E W := ⟨2,![4,9,13,0],![2,12,22,6]⟩
def cycle114_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle114_2 : CycleData E W := ⟨2,![8,5,15,2],![4,12,14,7]⟩
def cycle114_3 : CycleData E W := ⟨2,![7,10,14,3],![2,13,22,7]⟩
def cycle114_4 : CycleData E W := ⟨1,![11,16,6],![13,23,14]⟩
def data114 : PartitionData E W := ⟨5,![cycle114_0,cycle114_1,cycle114_2,cycle114_3,cycle114_4]⟩
lemma valid_data114 : data114.Valid src114 dst114 Finset.univ := by decide +kernel

def src115 : E → W := ![2,6,4,7,2,12,14,13,4,12,22,13,23,6,22,14,7,23]
def dst115 : E → W := ![6,4,7,2,12,14,13,2,12,22,13,23,4,22,14,7,23,6]
def cycle115_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle115_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle115_2 : CycleData E W := ⟨2,![7,6,15,3],![2,13,14,7]⟩
def cycle115_3 : CycleData E W := ⟨1,![9,14,5],![12,22,14]⟩
def cycle115_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,13,22]⟩
def data115 : PartitionData E W := ⟨5,![cycle115_0,cycle115_1,cycle115_2,cycle115_3,cycle115_4]⟩
lemma valid_data115 : data115.Valid src115 dst115 Finset.univ := by decide +kernel

def src116 : E → W := ![2,6,4,7,2,12,14,13,4,12,23,13,22,6,14,22,7,23]
def dst116 : E → W := ![6,4,7,2,12,14,13,2,12,23,13,22,4,14,22,7,23,6]
def cycle116_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle116_1 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle116_2 : CycleData E W := ⟨2,![7,10,16,3],![2,13,23,7]⟩
def cycle116_3 : CycleData E W := ⟨2,![17,9,5,13],![6,23,12,14]⟩
def cycle116_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data116 : PartitionData E W := ⟨5,![cycle116_0,cycle116_1,cycle116_2,cycle116_3,cycle116_4]⟩
lemma valid_data116 : data116.Valid src116 dst116 Finset.univ := by decide +kernel

def src117 : E → W := ![2,6,4,7,2,12,14,13,4,12,23,13,22,6,14,23,7,22]
def dst117 : E → W := ![6,4,7,2,12,14,13,2,12,23,13,22,4,14,23,7,22,6]
def cycle117_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle117_1 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle117_2 : CycleData E W := ⟨2,![7,10,15,3],![2,13,23,7]⟩
def cycle117_3 : CycleData E W := ⟨1,![9,14,5],![12,23,14]⟩
def cycle117_4 : CycleData E W := ⟨2,![17,11,6,13],![6,22,13,14]⟩
def data117 : PartitionData E W := ⟨5,![cycle117_0,cycle117_1,cycle117_2,cycle117_3,cycle117_4]⟩
lemma valid_data117 : data117.Valid src117 dst117 Finset.univ := by decide +kernel

def src118 : E → W := ![2,6,4,7,2,12,14,13,4,12,23,13,22,6,22,7,14,23]
def dst118 : E → W := ![6,4,7,2,12,14,13,2,12,23,13,22,4,22,7,14,23,6]
def cycle118_0 : CycleData E W := ⟨2,![4,8,1,0],![2,12,4,6]⟩
def cycle118_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle118_2 : CycleData E W := ⟨2,![7,6,15,3],![2,13,14,7]⟩
def cycle118_3 : CycleData E W := ⟨1,![9,16,5],![12,23,14]⟩
def cycle118_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,13,22]⟩
def data118 : PartitionData E W := ⟨5,![cycle118_0,cycle118_1,cycle118_2,cycle118_3,cycle118_4]⟩
lemma valid_data118 : data118.Valid src118 dst118 Finset.univ := by decide +kernel

def src119 : E → W := ![2,6,4,7,2,12,14,13,4,12,23,13,22,6,22,14,7,23]
def dst119 : E → W := ![6,4,7,2,12,14,13,2,12,23,13,22,4,22,14,7,23,6]
def cycle119_0 : CycleData E W := ⟨2,![4,9,17,0],![2,12,23,6]⟩
def cycle119_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle119_2 : CycleData E W := ⟨2,![8,5,15,2],![4,12,14,7]⟩
def cycle119_3 : CycleData E W := ⟨2,![7,10,16,3],![2,13,23,7]⟩
def cycle119_4 : CycleData E W := ⟨1,![11,14,6],![13,22,14]⟩
def data119 : PartitionData E W := ⟨5,![cycle119_0,cycle119_1,cycle119_2,cycle119_3,cycle119_4]⟩
lemma valid_data119 : data119.Valid src119 dst119 Finset.univ := by decide +kernel

def src120 : E → W := ![2,6,4,7,2,12,14,13,4,13,22,12,23,6,14,22,7,23]
def dst120 : E → W := ![6,4,7,2,12,14,13,2,13,22,12,23,4,14,22,7,23,6]
def cycle120_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle120_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle120_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,22,7]⟩
def cycle120_3 : CycleData E W := ⟨2,![17,11,5,13],![6,23,12,14]⟩
def cycle120_4 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def data120 : PartitionData E W := ⟨5,![cycle120_0,cycle120_1,cycle120_2,cycle120_3,cycle120_4]⟩
lemma valid_data120 : data120.Valid src120 dst120 Finset.univ := by decide +kernel

def src121 : E → W := ![2,6,4,7,2,12,14,13,4,13,22,12,23,6,14,23,7,22]
def dst121 : E → W := ![6,4,7,2,12,14,13,2,13,22,12,23,4,14,23,7,22,6]
def cycle121_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle121_1 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle121_2 : CycleData E W := ⟨2,![4,10,16,3],![2,12,22,7]⟩
def cycle121_3 : CycleData E W := ⟨1,![11,14,5],![12,23,14]⟩
def cycle121_4 : CycleData E W := ⟨2,![17,9,6,13],![6,22,13,14]⟩
def data121 : PartitionData E W := ⟨5,![cycle121_0,cycle121_1,cycle121_2,cycle121_3,cycle121_4]⟩
lemma valid_data121 : data121.Valid src121 dst121 Finset.univ := by decide +kernel

def src122 : E → W := ![2,6,4,7,2,12,14,13,4,13,22,12,23,6,22,7,14,23]
def dst122 : E → W := ![6,4,7,2,12,14,13,2,13,22,12,23,4,22,7,14,23,6]
def cycle122_0 : CycleData E W := ⟨2,![7,9,13,0],![2,13,22,6]⟩
def cycle122_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle122_2 : CycleData E W := ⟨2,![8,6,15,2],![4,13,14,7]⟩
def cycle122_3 : CycleData E W := ⟨2,![4,10,14,3],![2,12,22,7]⟩
def cycle122_4 : CycleData E W := ⟨1,![11,16,5],![12,23,14]⟩
def data122 : PartitionData E W := ⟨5,![cycle122_0,cycle122_1,cycle122_2,cycle122_3,cycle122_4]⟩
lemma valid_data122 : data122.Valid src122 dst122 Finset.univ := by decide +kernel

def src123 : E → W := ![2,6,4,7,2,12,14,13,4,13,22,12,23,6,22,14,7,23]
def dst123 : E → W := ![6,4,7,2,12,14,13,2,13,22,12,23,4,22,14,7,23,6]
def cycle123_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle123_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle123_2 : CycleData E W := ⟨2,![4,5,15,3],![2,12,14,7]⟩
def cycle123_3 : CycleData E W := ⟨1,![9,14,6],![13,22,14]⟩
def cycle123_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,12,22]⟩
def data123 : PartitionData E W := ⟨5,![cycle123_0,cycle123_1,cycle123_2,cycle123_3,cycle123_4]⟩
lemma valid_data123 : data123.Valid src123 dst123 Finset.univ := by decide +kernel

def src124 : E → W := ![2,6,4,7,2,12,14,13,4,13,23,12,22,6,14,22,7,23]
def dst124 : E → W := ![6,4,7,2,12,14,13,2,13,23,12,22,4,14,22,7,23,6]
def cycle124_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle124_1 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle124_2 : CycleData E W := ⟨2,![4,10,16,3],![2,12,23,7]⟩
def cycle124_3 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def cycle124_4 : CycleData E W := ⟨2,![17,9,6,13],![6,23,13,14]⟩
def data124 : PartitionData E W := ⟨5,![cycle124_0,cycle124_1,cycle124_2,cycle124_3,cycle124_4]⟩
lemma valid_data124 : data124.Valid src124 dst124 Finset.univ := by decide +kernel

def src125 : E → W := ![2,6,4,7,2,12,14,13,4,13,23,12,22,6,14,23,7,22]
def dst125 : E → W := ![6,4,7,2,12,14,13,2,13,23,12,22,4,14,23,7,22,6]
def cycle125_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle125_1 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle125_2 : CycleData E W := ⟨2,![4,10,15,3],![2,12,23,7]⟩
def cycle125_3 : CycleData E W := ⟨2,![17,11,5,13],![6,22,12,14]⟩
def cycle125_4 : CycleData E W := ⟨1,![9,14,6],![13,23,14]⟩
def data125 : PartitionData E W := ⟨5,![cycle125_0,cycle125_1,cycle125_2,cycle125_3,cycle125_4]⟩
lemma valid_data125 : data125.Valid src125 dst125 Finset.univ := by decide +kernel

def src126 : E → W := ![2,6,4,7,2,12,14,13,4,13,23,12,22,6,22,7,14,23]
def dst126 : E → W := ![6,4,7,2,12,14,13,2,13,23,12,22,4,22,7,14,23,6]
def cycle126_0 : CycleData E W := ⟨2,![7,8,1,0],![2,13,4,6]⟩
def cycle126_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle126_2 : CycleData E W := ⟨2,![4,5,15,3],![2,12,14,7]⟩
def cycle126_3 : CycleData E W := ⟨1,![9,16,6],![13,23,14]⟩
def cycle126_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,12,22]⟩
def data126 : PartitionData E W := ⟨5,![cycle126_0,cycle126_1,cycle126_2,cycle126_3,cycle126_4]⟩
lemma valid_data126 : data126.Valid src126 dst126 Finset.univ := by decide +kernel

def src127 : E → W := ![2,6,4,7,2,12,14,13,4,13,23,12,22,6,22,14,7,23]
def dst127 : E → W := ![6,4,7,2,12,14,13,2,13,23,12,22,4,22,14,7,23,6]
def cycle127_0 : CycleData E W := ⟨2,![7,9,17,0],![2,13,23,6]⟩
def cycle127_1 : CycleData E W := ⟨1,![12,13,1],![4,22,6]⟩
def cycle127_2 : CycleData E W := ⟨2,![8,6,15,2],![4,13,14,7]⟩
def cycle127_3 : CycleData E W := ⟨2,![4,10,16,3],![2,12,23,7]⟩
def cycle127_4 : CycleData E W := ⟨1,![11,14,5],![12,22,14]⟩
def data127 : PartitionData E W := ⟨5,![cycle127_0,cycle127_1,cycle127_2,cycle127_3,cycle127_4]⟩
lemma valid_data127 : data127.Valid src127 dst127 Finset.univ := by decide +kernel

def src128 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,23,6,14,22,7,23]
def dst128 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,23,4,14,22,7,23,6]
def cycle128_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle128_1 : CycleData E W := ⟨3,![8,5,11,17,1],![4,12,13,23,6]⟩
def cycle128_2 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle128_3 : CycleData E W := ⟨2,![4,10,15,3],![2,13,22,7]⟩
def cycle128_4 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def data128 : PartitionData E W := ⟨5,![cycle128_0,cycle128_1,cycle128_2,cycle128_3,cycle128_4]⟩
lemma valid_data128 : data128.Valid src128 dst128 Finset.univ := by decide +kernel

def src129 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,23,6,14,23,7,22]
def dst129 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,23,4,14,23,7,22,6]
def cycle129_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle129_1 : CycleData E W := ⟨2,![8,9,17,1],![4,12,22,6]⟩
def cycle129_2 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle129_3 : CycleData E W := ⟨2,![4,10,16,3],![2,13,22,7]⟩
def cycle129_4 : CycleData E W := ⟨2,![6,14,11,5],![12,14,23,13]⟩
def data129 : PartitionData E W := ⟨5,![cycle129_0,cycle129_1,cycle129_2,cycle129_3,cycle129_4]⟩
lemma valid_data129 : data129.Valid src129 dst129 Finset.univ := by decide +kernel

def src130 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,23,6,22,7,14,23]
def dst130 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,23,4,22,7,14,23,6]
def cycle130_0 : CycleData E W := ⟨2,![4,10,13,0],![2,13,22,6]⟩
def cycle130_1 : CycleData E W := ⟨1,![12,17,1],![4,23,6]⟩
def cycle130_2 : CycleData E W := ⟨2,![8,9,14,2],![4,12,22,7]⟩
def cycle130_3 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle130_4 : CycleData E W := ⟨2,![6,16,11,5],![12,14,23,13]⟩
def data130 : PartitionData E W := ⟨5,![cycle130_0,cycle130_1,cycle130_2,cycle130_3,cycle130_4]⟩
lemma valid_data130 : data130.Valid src130 dst130 Finset.univ := by decide +kernel

def src131 : E → W := ![2,6,4,7,2,13,12,14,4,12,22,13,23,6,22,14,7,23]
def dst131 : E → W := ![6,4,7,2,13,12,14,2,12,22,13,23,4,22,14,7,23,6]
def cycle131_0 : CycleData E W := ⟨3,![4,5,8,1,0],![2,13,12,4,6]⟩
def cycle131_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle131_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle131_3 : CycleData E W := ⟨1,![9,14,6],![12,22,14]⟩
def cycle131_4 : CycleData E W := ⟨2,![17,11,10,13],![6,23,13,22]⟩
def data131 : PartitionData E W := ⟨5,![cycle131_0,cycle131_1,cycle131_2,cycle131_3,cycle131_4]⟩
lemma valid_data131 : data131.Valid src131 dst131 Finset.univ := by decide +kernel

def src132 : E → W := ![2,6,4,7,2,13,12,14,4,12,23,13,22,6,14,22,7,23]
def dst132 : E → W := ![6,4,7,2,13,12,14,2,12,23,13,22,4,14,22,7,23,6]
def cycle132_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle132_1 : CycleData E W := ⟨2,![8,9,17,1],![4,12,23,6]⟩
def cycle132_2 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle132_3 : CycleData E W := ⟨2,![4,10,16,3],![2,13,23,7]⟩
def cycle132_4 : CycleData E W := ⟨2,![6,14,11,5],![12,14,22,13]⟩
def data132 : PartitionData E W := ⟨5,![cycle132_0,cycle132_1,cycle132_2,cycle132_3,cycle132_4]⟩
lemma valid_data132 : data132.Valid src132 dst132 Finset.univ := by decide +kernel

def src133 : E → W := ![2,6,4,7,2,13,12,14,4,12,23,13,22,6,14,23,7,22]
def dst133 : E → W := ![6,4,7,2,13,12,14,2,12,23,13,22,4,14,23,7,22,6]
def cycle133_0 : CycleData E W := ⟨1,![7,13,0],![2,14,6]⟩
def cycle133_1 : CycleData E W := ⟨3,![8,5,11,17,1],![4,12,13,22,6]⟩
def cycle133_2 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle133_3 : CycleData E W := ⟨2,![4,10,15,3],![2,13,23,7]⟩
def cycle133_4 : CycleData E W := ⟨1,![9,14,6],![12,23,14]⟩
def data133 : PartitionData E W := ⟨5,![cycle133_0,cycle133_1,cycle133_2,cycle133_3,cycle133_4]⟩
lemma valid_data133 : data133.Valid src133 dst133 Finset.univ := by decide +kernel

def src134 : E → W := ![2,6,4,7,2,13,12,14,4,12,23,13,22,6,22,7,14,23]
def dst134 : E → W := ![6,4,7,2,13,12,14,2,12,23,13,22,4,22,7,14,23,6]
def cycle134_0 : CycleData E W := ⟨3,![4,5,8,1,0],![2,13,12,4,6]⟩
def cycle134_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle134_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle134_3 : CycleData E W := ⟨1,![9,16,6],![12,23,14]⟩
def cycle134_4 : CycleData E W := ⟨2,![17,10,11,13],![6,23,13,22]⟩
def data134 : PartitionData E W := ⟨5,![cycle134_0,cycle134_1,cycle134_2,cycle134_3,cycle134_4]⟩
lemma valid_data134 : data134.Valid src134 dst134 Finset.univ := by decide +kernel

def src135 : E → W := ![2,6,4,7,2,13,12,14,4,12,23,13,22,6,22,14,7,23]
def dst135 : E → W := ![6,4,7,2,13,12,14,2,12,23,13,22,4,22,14,7,23,6]
def cycle135_0 : CycleData E W := ⟨2,![4,11,13,0],![2,13,22,6]⟩
def cycle135_1 : CycleData E W := ⟨2,![2,16,17,1],![4,7,23,6]⟩
def cycle135_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle135_3 : CycleData E W := ⟨1,![9,10,5],![12,23,13]⟩
def cycle135_4 : CycleData E W := ⟨2,![12,14,6,8],![4,22,14,12]⟩
def data135 : PartitionData E W := ⟨5,![cycle135_0,cycle135_1,cycle135_2,cycle135_3,cycle135_4]⟩
lemma valid_data135 : data135.Valid src135 dst135 Finset.univ := by decide +kernel

def src136 : E → W := ![2,6,4,7,2,13,12,14,4,13,22,12,23,6,14,22,7,23]
def dst136 : E → W := ![6,4,7,2,13,12,14,2,13,22,12,23,4,14,22,7,23,6]
def cycle136_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle136_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle136_2 : CycleData E W := ⟨2,![7,14,15,3],![2,14,22,7]⟩
def cycle136_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle136_4 : CycleData E W := ⟨2,![17,11,6,13],![6,23,12,14]⟩
def data136 : PartitionData E W := ⟨5,![cycle136_0,cycle136_1,cycle136_2,cycle136_3,cycle136_4]⟩
lemma valid_data136 : data136.Valid src136 dst136 Finset.univ := by decide +kernel

def src137 : E → W := ![2,6,4,7,2,13,12,14,4,13,22,12,23,6,14,23,7,22]
def dst137 : E → W := ![6,4,7,2,13,12,14,2,13,22,12,23,4,14,23,7,22,6]
def cycle137_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle137_1 : CycleData E W := ⟨1,![12,15,2],![4,23,7]⟩
def cycle137_2 : CycleData E W := ⟨3,![7,13,17,16,3],![2,14,6,22,7]⟩
def cycle137_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle137_4 : CycleData E W := ⟨1,![11,14,6],![12,23,14]⟩
def data137 : PartitionData E W := ⟨5,![cycle137_0,cycle137_1,cycle137_2,cycle137_3,cycle137_4]⟩
lemma valid_data137 : data137.Valid src137 dst137 Finset.univ := by decide +kernel

def src138 : E → W := ![2,6,4,7,2,13,12,14,4,13,22,12,23,6,22,7,14,23]
def dst138 : E → W := ![6,4,7,2,13,12,14,2,13,22,12,23,4,22,7,14,23,6]
def cycle138_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle138_1 : CycleData E W := ⟨3,![12,17,13,14,2],![4,23,6,22,7]⟩
def cycle138_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle138_3 : CycleData E W := ⟨1,![10,9,5],![12,22,13]⟩
def cycle138_4 : CycleData E W := ⟨1,![11,16,6],![12,23,14]⟩
def data138 : PartitionData E W := ⟨5,![cycle138_0,cycle138_1,cycle138_2,cycle138_3,cycle138_4]⟩
lemma valid_data138 : data138.Valid src138 dst138 Finset.univ := by decide +kernel

def src139 : E → W := ![2,6,4,7,2,13,12,14,4,13,22,12,23,6,22,14,7,23]
def dst139 : E → W := ![6,4,7,2,13,12,14,2,13,22,12,23,4,22,14,7,23,6]
def cycle139_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle139_1 : CycleData E W := ⟨1,![12,16,2],![4,23,7]⟩
def cycle139_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle139_3 : CycleData E W := ⟨3,![17,11,5,9,13],![6,23,12,13,22]⟩
def cycle139_4 : CycleData E W := ⟨1,![10,14,6],![12,22,14]⟩
def data139 : PartitionData E W := ⟨5,![cycle139_0,cycle139_1,cycle139_2,cycle139_3,cycle139_4]⟩
lemma valid_data139 : data139.Valid src139 dst139 Finset.univ := by decide +kernel

def src140 : E → W := ![2,6,4,7,2,13,12,14,4,13,23,12,22,6,14,22,7,23]
def dst140 : E → W := ![6,4,7,2,13,12,14,2,13,23,12,22,4,14,22,7,23,6]
def cycle140_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle140_1 : CycleData E W := ⟨1,![12,15,2],![4,22,7]⟩
def cycle140_2 : CycleData E W := ⟨3,![7,13,17,16,3],![2,14,6,23,7]⟩
def cycle140_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle140_4 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data140 : PartitionData E W := ⟨5,![cycle140_0,cycle140_1,cycle140_2,cycle140_3,cycle140_4]⟩
lemma valid_data140 : data140.Valid src140 dst140 Finset.univ := by decide +kernel

def src141 : E → W := ![2,6,4,7,2,13,12,14,4,13,23,12,22,6,14,23,7,22]
def dst141 : E → W := ![6,4,7,2,13,12,14,2,13,23,12,22,4,14,23,7,22,6]
def cycle141_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle141_1 : CycleData E W := ⟨1,![12,16,2],![4,22,7]⟩
def cycle141_2 : CycleData E W := ⟨2,![7,14,15,3],![2,14,23,7]⟩
def cycle141_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle141_4 : CycleData E W := ⟨2,![17,11,6,13],![6,22,12,14]⟩
def data141 : PartitionData E W := ⟨5,![cycle141_0,cycle141_1,cycle141_2,cycle141_3,cycle141_4]⟩
lemma valid_data141 : data141.Valid src141 dst141 Finset.univ := by decide +kernel

def src142 : E → W := ![2,6,4,7,2,13,12,14,4,13,23,12,22,6,22,7,14,23]
def dst142 : E → W := ![6,4,7,2,13,12,14,2,13,23,12,22,4,22,7,14,23,6]
def cycle142_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle142_1 : CycleData E W := ⟨1,![12,14,2],![4,22,7]⟩
def cycle142_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle142_3 : CycleData E W := ⟨3,![17,9,5,11,13],![6,23,13,12,22]⟩
def cycle142_4 : CycleData E W := ⟨1,![10,16,6],![12,23,14]⟩
def data142 : PartitionData E W := ⟨5,![cycle142_0,cycle142_1,cycle142_2,cycle142_3,cycle142_4]⟩
lemma valid_data142 : data142.Valid src142 dst142 Finset.univ := by decide +kernel

def src143 : E → W := ![2,6,4,7,2,13,12,14,4,13,23,12,22,6,22,14,7,23]
def dst143 : E → W := ![6,4,7,2,13,12,14,2,13,23,12,22,4,22,14,7,23,6]
def cycle143_0 : CycleData E W := ⟨2,![4,8,1,0],![2,13,4,6]⟩
def cycle143_1 : CycleData E W := ⟨3,![12,13,17,16,2],![4,22,6,23,7]⟩
def cycle143_2 : CycleData E W := ⟨1,![7,15,3],![2,14,7]⟩
def cycle143_3 : CycleData E W := ⟨1,![10,9,5],![12,23,13]⟩
def cycle143_4 : CycleData E W := ⟨1,![11,14,6],![12,22,14]⟩
def data143 : PartitionData E W := ⟨5,![cycle143_0,cycle143_1,cycle143_2,cycle143_3,cycle143_4]⟩
lemma valid_data143 : data143.Valid src143 dst143 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
  if k < 72 then
    if k < 36 then
      if k < 18 then
        if k < 9 then
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
                if k < 8 then
                  data7
                else
                  data8
        else
          if k < 13 then
            if k < 11 then
              if k < 10 then
                data9
              else
                data10
            else
              if k < 12 then
                data11
              else
                data12
          else
            if k < 15 then
              if k < 14 then
                data13
              else
                data14
            else
              if k < 16 then
                data15
              else
                if k < 17 then
                  data16
                else
                  data17
      else
        if k < 27 then
          if k < 22 then
            if k < 20 then
              if k < 19 then
                data18
              else
                data19
            else
              if k < 21 then
                data20
              else
                data21
          else
            if k < 24 then
              if k < 23 then
                data22
              else
                data23
            else
              if k < 25 then
                data24
              else
                if k < 26 then
                  data25
                else
                  data26
        else
          if k < 31 then
            if k < 29 then
              if k < 28 then
                data27
              else
                data28
            else
              if k < 30 then
                data29
              else
                data30
          else
            if k < 33 then
              if k < 32 then
                data31
              else
                data32
            else
              if k < 34 then
                data33
              else
                if k < 35 then
                  data34
                else
                  data35
    else
      if k < 54 then
        if k < 45 then
          if k < 40 then
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
          if k < 49 then
            if k < 47 then
              if k < 46 then
                data45
              else
                data46
            else
              if k < 48 then
                data47
              else
                data48
          else
            if k < 51 then
              if k < 50 then
                data49
              else
                data50
            else
              if k < 52 then
                data51
              else
                if k < 53 then
                  data52
                else
                  data53
      else
        if k < 63 then
          if k < 58 then
            if k < 56 then
              if k < 55 then
                data54
              else
                data55
            else
              if k < 57 then
                data56
              else
                data57
          else
            if k < 60 then
              if k < 59 then
                data58
              else
                data59
            else
              if k < 61 then
                data60
              else
                if k < 62 then
                  data61
                else
                  data62
        else
          if k < 67 then
            if k < 65 then
              if k < 64 then
                data63
              else
                data64
            else
              if k < 66 then
                data65
              else
                data66
          else
            if k < 69 then
              if k < 68 then
                data67
              else
                data68
            else
              if k < 70 then
                data69
              else
                if k < 71 then
                  data70
                else
                  data71
  else
    if k < 108 then
      if k < 90 then
        if k < 81 then
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
                if k < 80 then
                  data79
                else
                  data80
        else
          if k < 85 then
            if k < 83 then
              if k < 82 then
                data81
              else
                data82
            else
              if k < 84 then
                data83
              else
                data84
          else
            if k < 87 then
              if k < 86 then
                data85
              else
                data86
            else
              if k < 88 then
                data87
              else
                if k < 89 then
                  data88
                else
                  data89
      else
        if k < 99 then
          if k < 94 then
            if k < 92 then
              if k < 91 then
                data90
              else
                data91
            else
              if k < 93 then
                data92
              else
                data93
          else
            if k < 96 then
              if k < 95 then
                data94
              else
                data95
            else
              if k < 97 then
                data96
              else
                if k < 98 then
                  data97
                else
                  data98
        else
          if k < 103 then
            if k < 101 then
              if k < 100 then
                data99
              else
                data100
            else
              if k < 102 then
                data101
              else
                data102
          else
            if k < 105 then
              if k < 104 then
                data103
              else
                data104
            else
              if k < 106 then
                data105
              else
                if k < 107 then
                  data106
                else
                  data107
    else
      if k < 126 then
        if k < 117 then
          if k < 112 then
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
            if k < 114 then
              if k < 113 then
                data112
              else
                data113
            else
              if k < 115 then
                data114
              else
                if k < 116 then
                  data115
                else
                  data116
        else
          if k < 121 then
            if k < 119 then
              if k < 118 then
                data117
              else
                data118
            else
              if k < 120 then
                data119
              else
                data120
          else
            if k < 123 then
              if k < 122 then
                data121
              else
                data122
            else
              if k < 124 then
                data123
              else
                if k < 125 then
                  data124
                else
                  data125
      else
        if k < 135 then
          if k < 130 then
            if k < 128 then
              if k < 127 then
                data126
              else
                data127
            else
              if k < 129 then
                data128
              else
                data129
          else
            if k < 132 then
              if k < 131 then
                data130
              else
                data131
            else
              if k < 133 then
                data132
              else
                if k < 134 then
                  data133
                else
                  data134
        else
          if k < 139 then
            if k < 137 then
              if k < 136 then
                data135
              else
                data136
            else
              if k < 138 then
                data137
              else
                data138
          else
            if k < 141 then
              if k < 140 then
                data139
              else
                data140
            else
              if k < 142 then
                data141
              else
                if k < 143 then
                  data142
                else
                  data143

def srcTable (k : ℕ) : E → W :=
  if k < 72 then
    if k < 36 then
      if k < 18 then
        if k < 9 then
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
                if k < 8 then
                  src7
                else
                  src8
        else
          if k < 13 then
            if k < 11 then
              if k < 10 then
                src9
              else
                src10
            else
              if k < 12 then
                src11
              else
                src12
          else
            if k < 15 then
              if k < 14 then
                src13
              else
                src14
            else
              if k < 16 then
                src15
              else
                if k < 17 then
                  src16
                else
                  src17
      else
        if k < 27 then
          if k < 22 then
            if k < 20 then
              if k < 19 then
                src18
              else
                src19
            else
              if k < 21 then
                src20
              else
                src21
          else
            if k < 24 then
              if k < 23 then
                src22
              else
                src23
            else
              if k < 25 then
                src24
              else
                if k < 26 then
                  src25
                else
                  src26
        else
          if k < 31 then
            if k < 29 then
              if k < 28 then
                src27
              else
                src28
            else
              if k < 30 then
                src29
              else
                src30
          else
            if k < 33 then
              if k < 32 then
                src31
              else
                src32
            else
              if k < 34 then
                src33
              else
                if k < 35 then
                  src34
                else
                  src35
    else
      if k < 54 then
        if k < 45 then
          if k < 40 then
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
          if k < 49 then
            if k < 47 then
              if k < 46 then
                src45
              else
                src46
            else
              if k < 48 then
                src47
              else
                src48
          else
            if k < 51 then
              if k < 50 then
                src49
              else
                src50
            else
              if k < 52 then
                src51
              else
                if k < 53 then
                  src52
                else
                  src53
      else
        if k < 63 then
          if k < 58 then
            if k < 56 then
              if k < 55 then
                src54
              else
                src55
            else
              if k < 57 then
                src56
              else
                src57
          else
            if k < 60 then
              if k < 59 then
                src58
              else
                src59
            else
              if k < 61 then
                src60
              else
                if k < 62 then
                  src61
                else
                  src62
        else
          if k < 67 then
            if k < 65 then
              if k < 64 then
                src63
              else
                src64
            else
              if k < 66 then
                src65
              else
                src66
          else
            if k < 69 then
              if k < 68 then
                src67
              else
                src68
            else
              if k < 70 then
                src69
              else
                if k < 71 then
                  src70
                else
                  src71
  else
    if k < 108 then
      if k < 90 then
        if k < 81 then
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
                if k < 80 then
                  src79
                else
                  src80
        else
          if k < 85 then
            if k < 83 then
              if k < 82 then
                src81
              else
                src82
            else
              if k < 84 then
                src83
              else
                src84
          else
            if k < 87 then
              if k < 86 then
                src85
              else
                src86
            else
              if k < 88 then
                src87
              else
                if k < 89 then
                  src88
                else
                  src89
      else
        if k < 99 then
          if k < 94 then
            if k < 92 then
              if k < 91 then
                src90
              else
                src91
            else
              if k < 93 then
                src92
              else
                src93
          else
            if k < 96 then
              if k < 95 then
                src94
              else
                src95
            else
              if k < 97 then
                src96
              else
                if k < 98 then
                  src97
                else
                  src98
        else
          if k < 103 then
            if k < 101 then
              if k < 100 then
                src99
              else
                src100
            else
              if k < 102 then
                src101
              else
                src102
          else
            if k < 105 then
              if k < 104 then
                src103
              else
                src104
            else
              if k < 106 then
                src105
              else
                if k < 107 then
                  src106
                else
                  src107
    else
      if k < 126 then
        if k < 117 then
          if k < 112 then
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
            if k < 114 then
              if k < 113 then
                src112
              else
                src113
            else
              if k < 115 then
                src114
              else
                if k < 116 then
                  src115
                else
                  src116
        else
          if k < 121 then
            if k < 119 then
              if k < 118 then
                src117
              else
                src118
            else
              if k < 120 then
                src119
              else
                src120
          else
            if k < 123 then
              if k < 122 then
                src121
              else
                src122
            else
              if k < 124 then
                src123
              else
                if k < 125 then
                  src124
                else
                  src125
      else
        if k < 135 then
          if k < 130 then
            if k < 128 then
              if k < 127 then
                src126
              else
                src127
            else
              if k < 129 then
                src128
              else
                src129
          else
            if k < 132 then
              if k < 131 then
                src130
              else
                src131
            else
              if k < 133 then
                src132
              else
                if k < 134 then
                  src133
                else
                  src134
        else
          if k < 139 then
            if k < 137 then
              if k < 136 then
                src135
              else
                src136
            else
              if k < 138 then
                src137
              else
                src138
          else
            if k < 141 then
              if k < 140 then
                src139
              else
                src140
            else
              if k < 142 then
                src141
              else
                if k < 143 then
                  src142
                else
                  src143

def dstTable (k : ℕ) : E → W :=
  if k < 72 then
    if k < 36 then
      if k < 18 then
        if k < 9 then
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
                if k < 8 then
                  dst7
                else
                  dst8
        else
          if k < 13 then
            if k < 11 then
              if k < 10 then
                dst9
              else
                dst10
            else
              if k < 12 then
                dst11
              else
                dst12
          else
            if k < 15 then
              if k < 14 then
                dst13
              else
                dst14
            else
              if k < 16 then
                dst15
              else
                if k < 17 then
                  dst16
                else
                  dst17
      else
        if k < 27 then
          if k < 22 then
            if k < 20 then
              if k < 19 then
                dst18
              else
                dst19
            else
              if k < 21 then
                dst20
              else
                dst21
          else
            if k < 24 then
              if k < 23 then
                dst22
              else
                dst23
            else
              if k < 25 then
                dst24
              else
                if k < 26 then
                  dst25
                else
                  dst26
        else
          if k < 31 then
            if k < 29 then
              if k < 28 then
                dst27
              else
                dst28
            else
              if k < 30 then
                dst29
              else
                dst30
          else
            if k < 33 then
              if k < 32 then
                dst31
              else
                dst32
            else
              if k < 34 then
                dst33
              else
                if k < 35 then
                  dst34
                else
                  dst35
    else
      if k < 54 then
        if k < 45 then
          if k < 40 then
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
          if k < 49 then
            if k < 47 then
              if k < 46 then
                dst45
              else
                dst46
            else
              if k < 48 then
                dst47
              else
                dst48
          else
            if k < 51 then
              if k < 50 then
                dst49
              else
                dst50
            else
              if k < 52 then
                dst51
              else
                if k < 53 then
                  dst52
                else
                  dst53
      else
        if k < 63 then
          if k < 58 then
            if k < 56 then
              if k < 55 then
                dst54
              else
                dst55
            else
              if k < 57 then
                dst56
              else
                dst57
          else
            if k < 60 then
              if k < 59 then
                dst58
              else
                dst59
            else
              if k < 61 then
                dst60
              else
                if k < 62 then
                  dst61
                else
                  dst62
        else
          if k < 67 then
            if k < 65 then
              if k < 64 then
                dst63
              else
                dst64
            else
              if k < 66 then
                dst65
              else
                dst66
          else
            if k < 69 then
              if k < 68 then
                dst67
              else
                dst68
            else
              if k < 70 then
                dst69
              else
                if k < 71 then
                  dst70
                else
                  dst71
  else
    if k < 108 then
      if k < 90 then
        if k < 81 then
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
                if k < 80 then
                  dst79
                else
                  dst80
        else
          if k < 85 then
            if k < 83 then
              if k < 82 then
                dst81
              else
                dst82
            else
              if k < 84 then
                dst83
              else
                dst84
          else
            if k < 87 then
              if k < 86 then
                dst85
              else
                dst86
            else
              if k < 88 then
                dst87
              else
                if k < 89 then
                  dst88
                else
                  dst89
      else
        if k < 99 then
          if k < 94 then
            if k < 92 then
              if k < 91 then
                dst90
              else
                dst91
            else
              if k < 93 then
                dst92
              else
                dst93
          else
            if k < 96 then
              if k < 95 then
                dst94
              else
                dst95
            else
              if k < 97 then
                dst96
              else
                if k < 98 then
                  dst97
                else
                  dst98
        else
          if k < 103 then
            if k < 101 then
              if k < 100 then
                dst99
              else
                dst100
            else
              if k < 102 then
                dst101
              else
                dst102
          else
            if k < 105 then
              if k < 104 then
                dst103
              else
                dst104
            else
              if k < 106 then
                dst105
              else
                if k < 107 then
                  dst106
                else
                  dst107
    else
      if k < 126 then
        if k < 117 then
          if k < 112 then
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
            if k < 114 then
              if k < 113 then
                dst112
              else
                dst113
            else
              if k < 115 then
                dst114
              else
                if k < 116 then
                  dst115
                else
                  dst116
        else
          if k < 121 then
            if k < 119 then
              if k < 118 then
                dst117
              else
                dst118
            else
              if k < 120 then
                dst119
              else
                dst120
          else
            if k < 123 then
              if k < 122 then
                dst121
              else
                dst122
            else
              if k < 124 then
                dst123
              else
                if k < 125 then
                  dst124
                else
                  dst125
      else
        if k < 135 then
          if k < 130 then
            if k < 128 then
              if k < 127 then
                dst126
              else
                dst127
            else
              if k < 129 then
                dst128
              else
                dst129
          else
            if k < 132 then
              if k < 131 then
                dst130
              else
                dst131
            else
              if k < 133 then
                dst132
              else
                if k < 134 then
                  dst133
                else
                  dst134
        else
          if k < 139 then
            if k < 137 then
              if k < 136 then
                dst135
              else
                dst136
            else
              if k < 138 then
                dst137
              else
                dst138
          else
            if k < 141 then
              if k < 140 then
                dst139
              else
                dst140
            else
              if k < 142 then
                dst141
              else
                if k < 143 then
                  dst142
                else
                  dst143

lemma table_valid (k : Fin 144) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
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

lemma src_table_row : ∀ (k : Fin 144) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 144) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 144) := ∅
lemma size_mem : ∀ k : Fin 144, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 144, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows7

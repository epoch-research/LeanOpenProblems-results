import Submission.FourRows4

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,2,12,14,15,4,12,22,23,6,14,22,15,23]
def dst0 : E → W := ![4,6,2,12,14,15,2,12,22,23,4,14,22,15,23,6]
def cycle0_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle0_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle0_2 : CycleData E W := ⟨2,![6,5,11,2],![2,15,14,6]⟩
def cycle0_3 : CycleData E W := ⟨1,![8,12,4],![12,22,14]⟩
def cycle0_4 : CycleData E W := ⟨1,![14,9,13],![15,23,22]⟩
def data0 : PartitionData E W := ⟨5,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,6,2,12,14,15,4,12,22,23,6,14,23,15,22]
def dst1 : E → W := ![4,6,2,12,14,15,2,12,22,23,4,14,23,15,22,6]
def cycle1_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,15,23,22,12,14,6,4]⟩
def cycle1_1 : CycleData E W := ⟨6,![3,7,10,12,5,14,15,2],![2,12,4,23,14,15,22,6]⟩
def data1 : PartitionData E W := ⟨2,![cycle1_0,cycle1_1]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,6,2,12,14,15,4,12,22,23,6,15,22,14,23]
def dst2 : E → W := ![4,6,2,12,14,15,2,12,22,23,4,15,22,14,23,6]
def cycle2_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle2_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle2_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle2_3 : CycleData E W := ⟨2,![8,12,5,4],![12,22,15,14]⟩
def cycle2_4 : CycleData E W := ⟨1,![14,9,13],![14,23,22]⟩
def data2 : PartitionData E W := ⟨5,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,6,2,12,14,15,4,12,22,23,6,15,23,14,22]
def dst3 : E → W := ![4,6,2,12,14,15,2,12,22,23,4,15,23,14,22,6]
def cycle3_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle3_1 : CycleData E W := ⟨2,![10,9,15,1],![4,23,22,6]⟩
def cycle3_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle3_3 : CycleData E W := ⟨1,![8,14,4],![12,22,14]⟩
def cycle3_4 : CycleData E W := ⟨1,![13,12,5],![14,23,15]⟩
def data3 : PartitionData E W := ⟨5,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,6,2,12,14,15,4,12,23,22,6,14,22,15,23]
def dst4 : E → W := ![4,6,2,12,14,15,2,12,23,22,4,14,22,15,23,6]
def cycle4_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,15,22,23,12,14,6,4]⟩
def cycle4_1 : CycleData E W := ⟨6,![3,7,10,12,5,14,15,2],![2,12,4,22,14,15,23,6]⟩
def data4 : PartitionData E W := ⟨2,![cycle4_0,cycle4_1]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,6,2,12,14,15,4,12,23,22,6,14,23,15,22]
def dst5 : E → W := ![4,6,2,12,14,15,2,12,23,22,4,14,23,15,22,6]
def cycle5_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle5_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle5_2 : CycleData E W := ⟨2,![6,5,11,2],![2,15,14,6]⟩
def cycle5_3 : CycleData E W := ⟨1,![8,12,4],![12,23,14]⟩
def cycle5_4 : CycleData E W := ⟨1,![14,9,13],![15,22,23]⟩
def data5 : PartitionData E W := ⟨5,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,6,2,12,14,15,4,12,23,22,6,15,22,14,23]
def dst6 : E → W := ![4,6,2,12,14,15,2,12,23,22,4,15,22,14,23,6]
def cycle6_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle6_1 : CycleData E W := ⟨2,![10,9,15,1],![4,22,23,6]⟩
def cycle6_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle6_3 : CycleData E W := ⟨1,![8,14,4],![12,23,14]⟩
def cycle6_4 : CycleData E W := ⟨1,![13,12,5],![14,22,15]⟩
def data6 : PartitionData E W := ⟨5,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,6,2,12,14,15,4,12,23,22,6,15,23,14,22]
def dst7 : E → W := ![4,6,2,12,14,15,2,12,23,22,4,15,23,14,22,6]
def cycle7_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle7_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle7_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle7_3 : CycleData E W := ⟨2,![8,12,5,4],![12,23,15,14]⟩
def cycle7_4 : CycleData E W := ⟨1,![14,9,13],![14,22,23]⟩
def data7 : PartitionData E W := ⟨5,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,6,2,12,14,15,4,22,12,23,6,14,22,15,23]
def dst8 : E → W := ![4,6,2,12,14,15,2,22,12,23,4,14,22,15,23,6]
def cycle8_0 : CycleData E W := ⟨6,![6,14,9,8,12,11,1,0],![2,15,23,12,22,14,6,4]⟩
def cycle8_1 : CycleData E W := ⟨6,![3,4,5,13,7,10,15,2],![2,12,14,15,22,4,23,6]⟩
def data8 : PartitionData E W := ⟨2,![cycle8_0,cycle8_1]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![2,4,6,2,12,14,15,4,22,12,23,6,14,23,15,22]
def dst9 : E → W := ![4,6,2,12,14,15,2,22,12,23,4,14,23,15,22,6]
def cycle9_0 : CycleData E W := ⟨6,![6,14,8,9,12,11,1,0],![2,15,22,12,23,14,6,4]⟩
def cycle9_1 : CycleData E W := ⟨6,![3,4,5,13,10,7,15,2],![2,12,14,15,23,4,22,6]⟩
def data9 : PartitionData E W := ⟨2,![cycle9_0,cycle9_1]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![2,4,6,2,12,14,15,4,22,12,23,6,15,22,14,23]
def dst10 : E → W := ![4,6,2,12,14,15,2,22,12,23,4,15,22,14,23,6]
def cycle10_0 : CycleData E W := ⟨2,![3,8,7,0],![2,12,22,4]⟩
def cycle10_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle10_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle10_3 : CycleData E W := ⟨1,![9,14,4],![12,23,14]⟩
def cycle10_4 : CycleData E W := ⟨1,![13,12,5],![14,22,15]⟩
def data10 : PartitionData E W := ⟨5,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![2,4,6,2,12,14,15,4,22,12,23,6,15,23,14,22]
def dst11 : E → W := ![4,6,2,12,14,15,2,22,12,23,4,15,23,14,22,6]
def cycle11_0 : CycleData E W := ⟨2,![3,9,10,0],![2,12,23,4]⟩
def cycle11_1 : CycleData E W := ⟨1,![7,15,1],![4,22,6]⟩
def cycle11_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle11_3 : CycleData E W := ⟨1,![8,14,4],![12,22,14]⟩
def cycle11_4 : CycleData E W := ⟨1,![13,12,5],![14,23,15]⟩
def data11 : PartitionData E W := ⟨5,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![2,4,6,2,12,15,14,4,12,22,23,6,14,22,15,23]
def dst12 : E → W := ![4,6,2,12,15,14,2,12,22,23,4,14,22,15,23,6]
def cycle12_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle12_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle12_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle12_3 : CycleData E W := ⟨2,![8,12,5,4],![12,22,14,15]⟩
def cycle12_4 : CycleData E W := ⟨1,![14,9,13],![15,23,22]⟩
def data12 : PartitionData E W := ⟨5,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![2,4,6,2,12,15,14,4,12,22,23,6,14,23,15,22]
def dst13 : E → W := ![4,6,2,12,15,14,2,12,22,23,4,14,23,15,22,6]
def cycle13_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle13_1 : CycleData E W := ⟨2,![10,9,15,1],![4,23,22,6]⟩
def cycle13_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle13_3 : CycleData E W := ⟨1,![8,14,4],![12,22,15]⟩
def cycle13_4 : CycleData E W := ⟨1,![12,13,5],![14,23,15]⟩
def data13 : PartitionData E W := ⟨5,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![2,4,6,2,12,15,14,4,12,22,23,6,15,22,14,23]
def dst14 : E → W := ![4,6,2,12,15,14,2,12,22,23,4,15,22,14,23,6]
def cycle14_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle14_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle14_2 : CycleData E W := ⟨2,![6,5,11,2],![2,14,15,6]⟩
def cycle14_3 : CycleData E W := ⟨1,![8,12,4],![12,22,15]⟩
def cycle14_4 : CycleData E W := ⟨1,![14,9,13],![14,23,22]⟩
def data14 : PartitionData E W := ⟨5,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![2,4,6,2,12,15,14,4,12,22,23,6,15,23,14,22]
def dst15 : E → W := ![4,6,2,12,15,14,2,12,22,23,4,15,23,14,22,6]
def cycle15_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,14,23,22,12,15,6,4]⟩
def cycle15_1 : CycleData E W := ⟨6,![3,7,10,12,5,14,15,2],![2,12,4,23,15,14,22,6]⟩
def data15 : PartitionData E W := ⟨2,![cycle15_0,cycle15_1]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def src16 : E → W := ![2,4,6,2,12,15,14,4,12,23,22,6,14,22,15,23]
def dst16 : E → W := ![4,6,2,12,15,14,2,12,23,22,4,14,22,15,23,6]
def cycle16_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle16_1 : CycleData E W := ⟨2,![10,9,15,1],![4,22,23,6]⟩
def cycle16_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle16_3 : CycleData E W := ⟨1,![8,14,4],![12,23,15]⟩
def cycle16_4 : CycleData E W := ⟨1,![12,13,5],![14,22,15]⟩
def data16 : PartitionData E W := ⟨5,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4]⟩
lemma valid_data16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel

def src17 : E → W := ![2,4,6,2,12,15,14,4,12,23,22,6,14,23,15,22]
def dst17 : E → W := ![4,6,2,12,15,14,2,12,23,22,4,14,23,15,22,6]
def cycle17_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle17_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle17_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle17_3 : CycleData E W := ⟨2,![8,12,5,4],![12,23,14,15]⟩
def cycle17_4 : CycleData E W := ⟨1,![14,9,13],![15,22,23]⟩
def data17 : PartitionData E W := ⟨5,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4]⟩
lemma valid_data17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel

def src18 : E → W := ![2,4,6,2,12,15,14,4,12,23,22,6,15,22,14,23]
def dst18 : E → W := ![4,6,2,12,15,14,2,12,23,22,4,15,22,14,23,6]
def cycle18_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,14,22,23,12,15,6,4]⟩
def cycle18_1 : CycleData E W := ⟨6,![3,7,10,12,5,14,15,2],![2,12,4,22,15,14,23,6]⟩
def data18 : PartitionData E W := ⟨2,![cycle18_0,cycle18_1]⟩
lemma valid_data18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel

def src19 : E → W := ![2,4,6,2,12,15,14,4,12,23,22,6,15,23,14,22]
def dst19 : E → W := ![4,6,2,12,15,14,2,12,23,22,4,15,23,14,22,6]
def cycle19_0 : CycleData E W := ⟨1,![3,7,0],![2,12,4]⟩
def cycle19_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle19_2 : CycleData E W := ⟨2,![6,5,11,2],![2,14,15,6]⟩
def cycle19_3 : CycleData E W := ⟨1,![8,12,4],![12,23,15]⟩
def cycle19_4 : CycleData E W := ⟨1,![14,9,13],![14,22,23]⟩
def data19 : PartitionData E W := ⟨5,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4]⟩
lemma valid_data19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel

def src20 : E → W := ![2,4,6,2,12,15,14,4,22,12,23,6,14,22,15,23]
def dst20 : E → W := ![4,6,2,12,15,14,2,22,12,23,4,14,22,15,23,6]
def cycle20_0 : CycleData E W := ⟨2,![3,8,7,0],![2,12,22,4]⟩
def cycle20_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle20_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle20_3 : CycleData E W := ⟨1,![9,14,4],![12,23,15]⟩
def cycle20_4 : CycleData E W := ⟨1,![12,13,5],![14,22,15]⟩
def data20 : PartitionData E W := ⟨5,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4]⟩
lemma valid_data20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel

def src21 : E → W := ![2,4,6,2,12,15,14,4,22,12,23,6,14,23,15,22]
def dst21 : E → W := ![4,6,2,12,15,14,2,22,12,23,4,14,23,15,22,6]
def cycle21_0 : CycleData E W := ⟨2,![3,9,10,0],![2,12,23,4]⟩
def cycle21_1 : CycleData E W := ⟨1,![7,15,1],![4,22,6]⟩
def cycle21_2 : CycleData E W := ⟨1,![6,11,2],![2,14,6]⟩
def cycle21_3 : CycleData E W := ⟨1,![8,14,4],![12,22,15]⟩
def cycle21_4 : CycleData E W := ⟨1,![12,13,5],![14,23,15]⟩
def data21 : PartitionData E W := ⟨5,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4]⟩
lemma valid_data21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel

def src22 : E → W := ![2,4,6,2,12,15,14,4,22,12,23,6,15,22,14,23]
def dst22 : E → W := ![4,6,2,12,15,14,2,22,12,23,4,15,22,14,23,6]
def cycle22_0 : CycleData E W := ⟨6,![6,14,9,8,12,11,1,0],![2,14,23,12,22,15,6,4]⟩
def cycle22_1 : CycleData E W := ⟨6,![3,4,5,13,7,10,15,2],![2,12,15,14,22,4,23,6]⟩
def data22 : PartitionData E W := ⟨2,![cycle22_0,cycle22_1]⟩
lemma valid_data22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel

def src23 : E → W := ![2,4,6,2,12,15,14,4,22,12,23,6,15,23,14,22]
def dst23 : E → W := ![4,6,2,12,15,14,2,22,12,23,4,15,23,14,22,6]
def cycle23_0 : CycleData E W := ⟨6,![6,14,8,9,12,11,1,0],![2,14,22,12,23,15,6,4]⟩
def cycle23_1 : CycleData E W := ⟨6,![3,4,5,13,10,7,15,2],![2,12,15,14,23,4,22,6]⟩
def data23 : PartitionData E W := ⟨2,![cycle23_0,cycle23_1]⟩
lemma valid_data23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel

def src24 : E → W := ![2,4,6,2,14,12,15,4,12,22,23,6,14,22,15,23]
def dst24 : E → W := ![4,6,2,14,12,15,2,12,22,23,4,14,22,15,23,6]
def cycle24_0 : CycleData E W := ⟨2,![6,5,7,0],![2,15,12,4]⟩
def cycle24_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle24_2 : CycleData E W := ⟨1,![3,11,2],![2,14,6]⟩
def cycle24_3 : CycleData E W := ⟨1,![8,12,4],![12,22,14]⟩
def cycle24_4 : CycleData E W := ⟨1,![14,9,13],![15,23,22]⟩
def data24 : PartitionData E W := ⟨5,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4]⟩
lemma valid_data24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel

def src25 : E → W := ![2,4,6,2,14,12,15,4,12,22,23,6,14,23,15,22]
def dst25 : E → W := ![4,6,2,14,12,15,2,12,22,23,4,14,23,15,22,6]
def cycle25_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,15,23,22,12,14,6,4]⟩
def cycle25_1 : CycleData E W := ⟨6,![3,12,10,7,5,14,15,2],![2,14,23,4,12,15,22,6]⟩
def data25 : PartitionData E W := ⟨2,![cycle25_0,cycle25_1]⟩
lemma valid_data25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel

def src26 : E → W := ![2,4,6,2,14,12,15,4,12,22,23,6,15,22,14,23]
def dst26 : E → W := ![4,6,2,14,12,15,2,12,22,23,4,15,22,14,23,6]
def cycle26_0 : CycleData E W := ⟨2,![3,4,7,0],![2,14,12,4]⟩
def cycle26_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle26_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle26_3 : CycleData E W := ⟨1,![8,12,5],![12,22,15]⟩
def cycle26_4 : CycleData E W := ⟨1,![14,9,13],![14,23,22]⟩
def data26 : PartitionData E W := ⟨5,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4]⟩
lemma valid_data26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel

def src27 : E → W := ![2,4,6,2,14,12,15,4,12,22,23,6,15,23,14,22]
def dst27 : E → W := ![4,6,2,14,12,15,2,12,22,23,4,15,23,14,22,6]
def cycle27_0 : CycleData E W := ⟨6,![3,13,9,8,5,11,1,0],![2,14,23,22,12,15,6,4]⟩
def cycle27_1 : CycleData E W := ⟨6,![6,12,10,7,4,14,15,2],![2,15,23,4,12,14,22,6]⟩
def data27 : PartitionData E W := ⟨2,![cycle27_0,cycle27_1]⟩
lemma valid_data27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel

def src28 : E → W := ![2,4,6,2,14,12,15,4,12,23,22,6,14,22,15,23]
def dst28 : E → W := ![4,6,2,14,12,15,2,12,23,22,4,14,22,15,23,6]
def cycle28_0 : CycleData E W := ⟨6,![6,13,9,8,4,11,1,0],![2,15,22,23,12,14,6,4]⟩
def cycle28_1 : CycleData E W := ⟨6,![3,12,10,7,5,14,15,2],![2,14,22,4,12,15,23,6]⟩
def data28 : PartitionData E W := ⟨2,![cycle28_0,cycle28_1]⟩
lemma valid_data28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel

def src29 : E → W := ![2,4,6,2,14,12,15,4,12,23,22,6,14,23,15,22]
def dst29 : E → W := ![4,6,2,14,12,15,2,12,23,22,4,14,23,15,22,6]
def cycle29_0 : CycleData E W := ⟨2,![6,5,7,0],![2,15,12,4]⟩
def cycle29_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle29_2 : CycleData E W := ⟨1,![3,11,2],![2,14,6]⟩
def cycle29_3 : CycleData E W := ⟨1,![8,12,4],![12,23,14]⟩
def cycle29_4 : CycleData E W := ⟨1,![14,9,13],![15,22,23]⟩
def data29 : PartitionData E W := ⟨5,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4]⟩
lemma valid_data29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel

def src30 : E → W := ![2,4,6,2,14,12,15,4,12,23,22,6,15,22,14,23]
def dst30 : E → W := ![4,6,2,14,12,15,2,12,23,22,4,15,22,14,23,6]
def cycle30_0 : CycleData E W := ⟨6,![3,13,9,8,5,11,1,0],![2,14,22,23,12,15,6,4]⟩
def cycle30_1 : CycleData E W := ⟨6,![6,12,10,7,4,14,15,2],![2,15,22,4,12,14,23,6]⟩
def data30 : PartitionData E W := ⟨2,![cycle30_0,cycle30_1]⟩
lemma valid_data30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel

def src31 : E → W := ![2,4,6,2,14,12,15,4,12,23,22,6,15,23,14,22]
def dst31 : E → W := ![4,6,2,14,12,15,2,12,23,22,4,15,23,14,22,6]
def cycle31_0 : CycleData E W := ⟨2,![3,4,7,0],![2,14,12,4]⟩
def cycle31_1 : CycleData E W := ⟨1,![10,15,1],![4,22,6]⟩
def cycle31_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle31_3 : CycleData E W := ⟨1,![8,12,5],![12,23,15]⟩
def cycle31_4 : CycleData E W := ⟨1,![14,9,13],![14,22,23]⟩
def data31 : PartitionData E W := ⟨5,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4]⟩
lemma valid_data31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel

def src32 : E → W := ![2,4,6,2,14,12,15,4,22,12,23,6,14,22,15,23]
def dst32 : E → W := ![4,6,2,14,12,15,2,22,12,23,4,14,22,15,23,6]
def cycle32_0 : CycleData E W := ⟨2,![6,13,7,0],![2,15,22,4]⟩
def cycle32_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle32_2 : CycleData E W := ⟨1,![3,11,2],![2,14,6]⟩
def cycle32_3 : CycleData E W := ⟨1,![8,12,4],![12,22,14]⟩
def cycle32_4 : CycleData E W := ⟨1,![9,14,5],![12,23,15]⟩
def data32 : PartitionData E W := ⟨5,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4]⟩
lemma valid_data32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel

def src33 : E → W := ![2,4,6,2,14,12,15,4,22,12,23,6,14,23,15,22]
def dst33 : E → W := ![4,6,2,14,12,15,2,22,12,23,4,14,23,15,22,6]
def cycle33_0 : CycleData E W := ⟨2,![6,13,10,0],![2,15,23,4]⟩
def cycle33_1 : CycleData E W := ⟨1,![7,15,1],![4,22,6]⟩
def cycle33_2 : CycleData E W := ⟨1,![3,11,2],![2,14,6]⟩
def cycle33_3 : CycleData E W := ⟨1,![9,12,4],![12,23,14]⟩
def cycle33_4 : CycleData E W := ⟨1,![8,14,5],![12,22,15]⟩
def data33 : PartitionData E W := ⟨5,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4]⟩
lemma valid_data33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel

def src34 : E → W := ![2,4,6,2,14,12,15,4,22,12,23,6,15,22,14,23]
def dst34 : E → W := ![4,6,2,14,12,15,2,22,12,23,4,15,22,14,23,6]
def cycle34_0 : CycleData E W := ⟨2,![3,13,7,0],![2,14,22,4]⟩
def cycle34_1 : CycleData E W := ⟨1,![10,15,1],![4,23,6]⟩
def cycle34_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle34_3 : CycleData E W := ⟨1,![9,14,4],![12,23,14]⟩
def cycle34_4 : CycleData E W := ⟨1,![8,12,5],![12,22,15]⟩
def data34 : PartitionData E W := ⟨5,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4]⟩
lemma valid_data34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel

def src35 : E → W := ![2,4,6,2,14,12,15,4,22,12,23,6,15,23,14,22]
def dst35 : E → W := ![4,6,2,14,12,15,2,22,12,23,4,15,23,14,22,6]
def cycle35_0 : CycleData E W := ⟨2,![3,13,10,0],![2,14,23,4]⟩
def cycle35_1 : CycleData E W := ⟨1,![7,15,1],![4,22,6]⟩
def cycle35_2 : CycleData E W := ⟨1,![6,11,2],![2,15,6]⟩
def cycle35_3 : CycleData E W := ⟨1,![8,14,4],![12,22,14]⟩
def cycle35_4 : CycleData E W := ⟨1,![9,12,5],![12,23,15]⟩
def data35 : PartitionData E W := ⟨5,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4]⟩
lemma valid_data35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
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

def srcTable (k : ℕ) : E → W :=
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

def dstTable (k : ℕ) : E → W :=
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

lemma table_valid (k : Fin 36) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
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

lemma src_table_row : ∀ (k : Fin 36) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 36) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 36) := {1,4,8,9,15,18,22,23,25,27,28,30}
lemma size_mem : ∀ k : Fin 36, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 36, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows4

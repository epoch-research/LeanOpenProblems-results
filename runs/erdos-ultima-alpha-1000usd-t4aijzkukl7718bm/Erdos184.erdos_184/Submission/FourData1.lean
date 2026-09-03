import Submission.FourRows1

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,13,22,6,14,7,15,22]
def dst0 : E → W := ![6,5,7,4,14,13,15,12,12,5,13,22,4,14,7,15,22,6]
def cycle0_0 : CycleData E W := ⟨1,![12,17,0],![4,22,6]⟩
def cycle0_1 : CycleData E W := ⟨2,![9,4,13,1],![5,12,14,6]⟩
def cycle0_2 : CycleData E W := ⟨2,![10,5,14,2],![5,13,14,7]⟩
def cycle0_3 : CycleData E W := ⟨2,![8,7,15,3],![4,12,15,7]⟩
def cycle0_4 : CycleData E W := ⟨1,![11,16,6],![13,22,15]⟩
def data0 : PartitionData E W := ⟨5,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,13,22,6,14,7,22,15]
def dst1 : E → W := ![6,5,7,4,14,13,15,12,12,5,13,22,4,14,7,22,15,6]
def cycle1_0 : CycleData E W := ⟨2,![8,9,1,0],![4,12,5,6]⟩
def cycle1_1 : CycleData E W := ⟨2,![10,5,14,2],![5,13,14,7]⟩
def cycle1_2 : CycleData E W := ⟨1,![12,15,3],![4,22,7]⟩
def cycle1_3 : CycleData E W := ⟨2,![17,7,4,13],![6,15,12,14]⟩
def cycle1_4 : CycleData E W := ⟨1,![11,16,6],![13,22,15]⟩
def data1 : PartitionData E W := ⟨5,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,13,22,6,14,22,7,15]
def dst2 : E → W := ![6,5,7,4,14,13,15,12,12,5,13,22,4,14,22,7,15,6]
def cycle2_0 : CycleData E W := ⟨2,![8,9,1,0],![4,12,5,6]⟩
def cycle2_1 : CycleData E W := ⟨2,![10,6,16,2],![5,13,15,7]⟩
def cycle2_2 : CycleData E W := ⟨1,![12,15,3],![4,22,7]⟩
def cycle2_3 : CycleData E W := ⟨2,![17,7,4,13],![6,15,12,14]⟩
def cycle2_4 : CycleData E W := ⟨1,![11,14,5],![13,22,14]⟩
def data2 : PartitionData E W := ⟨5,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,13,22,6,15,7,14,22]
def dst3 : E → W := ![6,5,7,4,14,13,15,12,12,5,13,22,4,15,7,14,22,6]
def cycle3_0 : CycleData E W := ⟨1,![12,17,0],![4,22,6]⟩
def cycle3_1 : CycleData E W := ⟨2,![10,6,13,1],![5,13,15,6]⟩
def cycle3_2 : CycleData E W := ⟨2,![8,9,2,3],![4,12,5,7]⟩
def cycle3_3 : CycleData E W := ⟨2,![15,4,7,14],![7,14,12,15]⟩
def cycle3_4 : CycleData E W := ⟨1,![11,16,5],![13,22,14]⟩
def data3 : PartitionData E W := ⟨5,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,22,13,6,14,7,15,22]
def dst4 : E → W := ![6,5,7,4,14,13,15,12,12,5,22,13,4,14,7,15,22,6]
def cycle4_0 : CycleData E W := ⟨2,![8,4,13,0],![4,12,14,6]⟩
def cycle4_1 : CycleData E W := ⟨1,![10,17,1],![5,22,6]⟩
def cycle4_2 : CycleData E W := ⟨2,![9,7,15,2],![5,12,15,7]⟩
def cycle4_3 : CycleData E W := ⟨2,![12,5,14,3],![4,13,14,7]⟩
def cycle4_4 : CycleData E W := ⟨1,![11,16,6],![13,22,15]⟩
def data4 : PartitionData E W := ⟨5,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,22,13,6,14,7,22,15]
def dst5 : E → W := ![6,5,7,4,14,13,15,12,12,5,22,13,4,14,7,22,15,6]
def cycle5_0 : CycleData E W := ⟨2,![8,9,1,0],![4,12,5,6]⟩
def cycle5_1 : CycleData E W := ⟨1,![10,15,2],![5,22,7]⟩
def cycle5_2 : CycleData E W := ⟨2,![12,5,14,3],![4,13,14,7]⟩
def cycle5_3 : CycleData E W := ⟨2,![17,7,4,13],![6,15,12,14]⟩
def cycle5_4 : CycleData E W := ⟨1,![11,16,6],![13,22,15]⟩
def data5 : PartitionData E W := ⟨5,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,22,13,6,14,22,7,15]
def dst6 : E → W := ![6,5,7,4,14,13,15,12,12,5,22,13,4,14,22,7,15,6]
def cycle6_0 : CycleData E W := ⟨2,![8,9,1,0],![4,12,5,6]⟩
def cycle6_1 : CycleData E W := ⟨1,![10,15,2],![5,22,7]⟩
def cycle6_2 : CycleData E W := ⟨2,![12,6,16,3],![4,13,15,7]⟩
def cycle6_3 : CycleData E W := ⟨2,![17,7,4,13],![6,15,12,14]⟩
def cycle6_4 : CycleData E W := ⟨1,![11,14,5],![13,22,14]⟩
def data6 : PartitionData E W := ⟨5,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![4,6,5,7,12,14,13,15,4,12,5,22,13,6,15,7,14,22]
def dst7 : E → W := ![6,5,7,4,14,13,15,12,12,5,22,13,4,15,7,14,22,6]
def cycle7_0 : CycleData E W := ⟨2,![12,6,13,0],![4,13,15,6]⟩
def cycle7_1 : CycleData E W := ⟨1,![10,17,1],![5,22,6]⟩
def cycle7_2 : CycleData E W := ⟨2,![8,9,2,3],![4,12,5,7]⟩
def cycle7_3 : CycleData E W := ⟨2,![15,4,7,14],![7,14,12,15]⟩
def cycle7_4 : CycleData E W := ⟨1,![11,16,5],![13,22,14]⟩
def data7 : PartitionData E W := ⟨5,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![4,6,5,7,12,14,13,15,4,12,22,5,13,6,14,7,15,22]
def dst8 : E → W := ![6,5,7,4,14,13,15,12,12,22,5,13,4,14,7,15,22,6]
def cycle8_0 : CycleData E W := ⟨2,![8,4,13,0],![4,12,14,6]⟩
def cycle8_1 : CycleData E W := ⟨1,![10,17,1],![5,22,6]⟩
def cycle8_2 : CycleData E W := ⟨2,![12,11,2,3],![4,13,5,7]⟩
def cycle8_3 : CycleData E W := ⟨2,![15,6,5,14],![7,15,13,14]⟩
def cycle8_4 : CycleData E W := ⟨1,![9,16,7],![12,22,15]⟩
def data8 : PartitionData E W := ⟨5,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def src9 : E → W := ![4,6,5,7,12,14,13,15,4,12,22,5,13,6,14,7,22,15]
def dst9 : E → W := ![6,5,7,4,14,13,15,12,12,22,5,13,4,14,7,22,15,6]
def cycle9_0 : CycleData E W := ⟨2,![12,11,1,0],![4,13,5,6]⟩
def cycle9_1 : CycleData E W := ⟨1,![10,15,2],![5,22,7]⟩
def cycle9_2 : CycleData E W := ⟨2,![8,4,14,3],![4,12,14,7]⟩
def cycle9_3 : CycleData E W := ⟨2,![17,6,5,13],![6,15,13,14]⟩
def cycle9_4 : CycleData E W := ⟨1,![9,16,7],![12,22,15]⟩
def data9 : PartitionData E W := ⟨5,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4]⟩
lemma valid_data9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel

def src10 : E → W := ![4,6,5,7,12,14,13,15,4,12,22,5,13,6,14,22,7,15]
def dst10 : E → W := ![6,5,7,4,14,13,15,12,12,22,5,13,4,14,22,7,15,6]
def cycle10_0 : CycleData E W := ⟨2,![12,11,1,0],![4,13,5,6]⟩
def cycle10_1 : CycleData E W := ⟨1,![10,15,2],![5,22,7]⟩
def cycle10_2 : CycleData E W := ⟨2,![8,7,16,3],![4,12,15,7]⟩
def cycle10_3 : CycleData E W := ⟨1,![9,14,4],![12,22,14]⟩
def cycle10_4 : CycleData E W := ⟨2,![17,6,5,13],![6,15,13,14]⟩
def data10 : PartitionData E W := ⟨5,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4]⟩
lemma valid_data10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel

def src11 : E → W := ![4,6,5,7,12,14,13,15,4,12,22,5,13,6,15,7,14,22]
def dst11 : E → W := ![6,5,7,4,14,13,15,12,12,22,5,13,4,15,7,14,22,6]
def cycle11_0 : CycleData E W := ⟨2,![12,6,13,0],![4,13,15,6]⟩
def cycle11_1 : CycleData E W := ⟨1,![10,17,1],![5,22,6]⟩
def cycle11_2 : CycleData E W := ⟨2,![11,5,15,2],![5,13,14,7]⟩
def cycle11_3 : CycleData E W := ⟨2,![8,7,14,3],![4,12,15,7]⟩
def cycle11_4 : CycleData E W := ⟨1,![9,16,4],![12,22,14]⟩
def data11 : PartitionData E W := ⟨5,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4]⟩
lemma valid_data11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel

def src12 : E → W := ![4,6,5,7,12,14,13,15,4,13,5,12,22,6,14,7,15,22]
def dst12 : E → W := ![6,5,7,4,14,13,15,12,13,5,12,22,4,14,7,15,22,6]
def cycle12_0 : CycleData E W := ⟨1,![12,17,0],![4,22,6]⟩
def cycle12_1 : CycleData E W := ⟨2,![10,4,13,1],![5,12,14,6]⟩
def cycle12_2 : CycleData E W := ⟨2,![8,9,2,3],![4,13,5,7]⟩
def cycle12_3 : CycleData E W := ⟨2,![15,6,5,14],![7,15,13,14]⟩
def cycle12_4 : CycleData E W := ⟨1,![11,16,7],![12,22,15]⟩
def data12 : PartitionData E W := ⟨5,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4]⟩
lemma valid_data12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel

def src13 : E → W := ![4,6,5,7,12,14,13,15,4,13,5,12,22,6,14,7,22,15]
def dst13 : E → W := ![6,5,7,4,14,13,15,12,13,5,12,22,4,14,7,22,15,6]
def cycle13_0 : CycleData E W := ⟨2,![8,9,1,0],![4,13,5,6]⟩
def cycle13_1 : CycleData E W := ⟨2,![10,4,14,2],![5,12,14,7]⟩
def cycle13_2 : CycleData E W := ⟨1,![12,15,3],![4,22,7]⟩
def cycle13_3 : CycleData E W := ⟨2,![17,6,5,13],![6,15,13,14]⟩
def cycle13_4 : CycleData E W := ⟨1,![11,16,7],![12,22,15]⟩
def data13 : PartitionData E W := ⟨5,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4]⟩
lemma valid_data13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel

def src14 : E → W := ![4,6,5,7,12,14,13,15,4,13,5,12,22,6,14,22,7,15]
def dst14 : E → W := ![6,5,7,4,14,13,15,12,13,5,12,22,4,14,22,7,15,6]
def cycle14_0 : CycleData E W := ⟨2,![8,9,1,0],![4,13,5,6]⟩
def cycle14_1 : CycleData E W := ⟨2,![10,7,16,2],![5,12,15,7]⟩
def cycle14_2 : CycleData E W := ⟨1,![12,15,3],![4,22,7]⟩
def cycle14_3 : CycleData E W := ⟨1,![11,14,4],![12,22,14]⟩
def cycle14_4 : CycleData E W := ⟨2,![17,6,5,13],![6,15,13,14]⟩
def data14 : PartitionData E W := ⟨5,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4]⟩
lemma valid_data14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel

def src15 : E → W := ![4,6,5,7,12,14,13,15,4,13,5,12,22,6,15,7,14,22]
def dst15 : E → W := ![6,5,7,4,14,13,15,12,13,5,12,22,4,15,7,14,22,6]
def cycle15_0 : CycleData E W := ⟨1,![12,17,0],![4,22,6]⟩
def cycle15_1 : CycleData E W := ⟨2,![9,6,13,1],![5,13,15,6]⟩
def cycle15_2 : CycleData E W := ⟨2,![10,7,14,2],![5,12,15,7]⟩
def cycle15_3 : CycleData E W := ⟨2,![8,5,15,3],![4,13,14,7]⟩
def cycle15_4 : CycleData E W := ⟨1,![11,16,4],![12,22,14]⟩
def data15 : PartitionData E W := ⟨5,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4]⟩
lemma valid_data15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
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

def srcTable (k : ℕ) : E → W :=
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

def dstTable (k : ℕ) : E → W :=
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

lemma table_valid (k : Fin 16) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
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

lemma src_table_row : ∀ (k : Fin 16) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 16) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 16) := ∅
lemma size_mem : ∀ k : Fin 16, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 16, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows1

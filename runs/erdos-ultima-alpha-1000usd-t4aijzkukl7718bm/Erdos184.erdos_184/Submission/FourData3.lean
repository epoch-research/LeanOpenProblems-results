import Submission.FourRows3

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,2,12,14,4,12,22,23,6,14,22,23]
def dst0 : E → W := ![4,6,2,12,14,2,12,22,23,4,14,22,23,6]
def cycle0_0 : CycleData E W := ⟨1,![3,6,0],![2,12,4]⟩
def cycle0_1 : CycleData E W := ⟨1,![9,13,1],![4,23,6]⟩
def cycle0_2 : CycleData E W := ⟨1,![5,10,2],![2,14,6]⟩
def cycle0_3 : CycleData E W := ⟨1,![7,11,4],![12,22,14]⟩
def cycle0_4 : CycleData E W := ⟨0,![12,8],![22,23]⟩
def data0 : PartitionData E W := ⟨5,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def src1 : E → W := ![2,4,6,2,12,14,4,12,22,23,6,14,23,22]
def dst1 : E → W := ![4,6,2,12,14,2,12,22,23,4,14,23,22,6]
def cycle1_0 : CycleData E W := ⟨5,![3,7,8,11,10,1,0],![2,12,22,23,14,6,4]⟩
def cycle1_1 : CycleData E W := ⟨5,![5,4,6,9,12,13,2],![2,14,12,4,23,22,6]⟩
def data1 : PartitionData E W := ⟨2,![cycle1_0,cycle1_1]⟩
lemma valid_data1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel

def src2 : E → W := ![2,4,6,2,12,14,4,12,22,23,6,22,14,23]
def dst2 : E → W := ![4,6,2,12,14,2,12,22,23,4,22,14,23,6]
def cycle2_0 : CycleData E W := ⟨5,![3,4,12,8,10,1,0],![2,12,14,23,22,6,4]⟩
def cycle2_1 : CycleData E W := ⟨5,![5,11,7,6,9,13,2],![2,14,22,12,4,23,6]⟩
def data2 : PartitionData E W := ⟨2,![cycle2_0,cycle2_1]⟩
lemma valid_data2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel

def src3 : E → W := ![2,4,6,2,12,14,4,12,23,22,6,14,22,23]
def dst3 : E → W := ![4,6,2,12,14,2,12,23,22,4,14,22,23,6]
def cycle3_0 : CycleData E W := ⟨5,![3,7,8,11,10,1,0],![2,12,23,22,14,6,4]⟩
def cycle3_1 : CycleData E W := ⟨5,![5,4,6,9,12,13,2],![2,14,12,4,22,23,6]⟩
def data3 : PartitionData E W := ⟨2,![cycle3_0,cycle3_1]⟩
lemma valid_data3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel

def src4 : E → W := ![2,4,6,2,12,14,4,12,23,22,6,14,23,22]
def dst4 : E → W := ![4,6,2,12,14,2,12,23,22,4,14,23,22,6]
def cycle4_0 : CycleData E W := ⟨1,![3,6,0],![2,12,4]⟩
def cycle4_1 : CycleData E W := ⟨1,![9,13,1],![4,22,6]⟩
def cycle4_2 : CycleData E W := ⟨1,![5,10,2],![2,14,6]⟩
def cycle4_3 : CycleData E W := ⟨1,![7,11,4],![12,23,14]⟩
def cycle4_4 : CycleData E W := ⟨0,![12,8],![22,23]⟩
def data4 : PartitionData E W := ⟨5,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4]⟩
lemma valid_data4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel

def src5 : E → W := ![2,4,6,2,12,14,4,12,23,22,6,22,14,23]
def dst5 : E → W := ![4,6,2,12,14,2,12,23,22,4,22,14,23,6]
def cycle5_0 : CycleData E W := ⟨5,![5,4,7,8,10,1,0],![2,14,12,23,22,6,4]⟩
def cycle5_1 : CycleData E W := ⟨5,![3,6,9,11,12,13,2],![2,12,4,22,14,23,6]⟩
def data5 : PartitionData E W := ⟨2,![cycle5_0,cycle5_1]⟩
lemma valid_data5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel

def src6 : E → W := ![2,4,6,2,12,14,4,22,12,23,6,14,22,23]
def dst6 : E → W := ![4,6,2,12,14,2,22,12,23,4,14,22,23,6]
def cycle6_0 : CycleData E W := ⟨5,![3,8,12,11,10,1,0],![2,12,23,22,14,6,4]⟩
def cycle6_1 : CycleData E W := ⟨5,![5,4,7,6,9,13,2],![2,14,12,22,4,23,6]⟩
def data6 : PartitionData E W := ⟨2,![cycle6_0,cycle6_1]⟩
lemma valid_data6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel

def src7 : E → W := ![2,4,6,2,12,14,4,22,12,23,6,14,23,22]
def dst7 : E → W := ![4,6,2,12,14,2,22,12,23,4,14,23,22,6]
def cycle7_0 : CycleData E W := ⟨5,![3,7,12,11,10,1,0],![2,12,22,23,14,6,4]⟩
def cycle7_1 : CycleData E W := ⟨5,![5,4,8,9,6,13,2],![2,14,12,23,4,22,6]⟩
def data7 : PartitionData E W := ⟨2,![cycle7_0,cycle7_1]⟩
lemma valid_data7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel

def src8 : E → W := ![2,4,6,2,12,14,4,22,12,23,6,22,14,23]
def dst8 : E → W := ![4,6,2,12,14,2,22,12,23,4,22,14,23,6]
def cycle8_0 : CycleData E W := ⟨5,![5,12,8,7,10,1,0],![2,14,23,12,22,6,4]⟩
def cycle8_1 : CycleData E W := ⟨5,![3,4,11,6,9,13,2],![2,12,14,22,4,23,6]⟩
def data8 : PartitionData E W := ⟨2,![cycle8_0,cycle8_1]⟩
lemma valid_data8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
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

def srcTable (k : ℕ) : E → W :=
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

def dstTable (k : ℕ) : E → W :=
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

lemma table_valid (k : Fin 9) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
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

lemma src_table_row : ∀ (k : Fin 9) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 9) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 9) := {1,2,3,5,6,7,8}
lemma size_mem : ∀ k : Fin 9, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 9, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows3

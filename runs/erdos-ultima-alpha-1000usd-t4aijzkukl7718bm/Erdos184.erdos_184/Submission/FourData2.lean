import Submission.FourRows2

/-! Independent finite circuit-partition certificates for the locally allowed
row tuples. Every certificate gives either two circuits or more than four. -/
namespace Erdos184Work.FourRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,6,2,12,14,4,12,22,6,14,22]
def dst0 : E → W := ![4,6,2,12,14,2,12,22,4,14,22,6]
def cycle0_0 : CycleData E W := ⟨4,![3,7,10,9,1,0],![2,12,22,14,6,4]⟩
def cycle0_1 : CycleData E W := ⟨4,![5,4,6,8,11,2],![2,14,12,4,22,6]⟩
def data0 : PartitionData E W := ⟨2,![cycle0_0,cycle0_1]⟩
lemma valid_data0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel

def lookup (k : ℕ) : PartitionData E W :=
  data0

def srcTable (k : ℕ) : E → W :=
  src0

def dstTable (k : ℕ) : E → W :=
  dst0

lemma table_valid (k : Fin 1) : (lookup k.val).Valid (srcTable k.val) (dstTable k.val) Finset.univ := by
  fin_cases k
  · exact valid_data0

lemma src_table_row : ∀ (k : Fin 1) (e : E), srcTable k.val e = srcAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

lemma dst_table_row : ∀ (k : Fin 1) (e : E), dstTable k.val e = dstAt (digit0 k.val) (digit1 k.val) (digit2 k.val) (digit3 k.val) e := by decide +kernel

def good : Finset (Fin 1) := {0}
lemma size_mem : ∀ k : Fin 1, (lookup k.val).size ≤ 4 ↔ k ∈ good := by decide +kernel
lemma size_two : ∀ k : Fin 1, (lookup k.val).size ≤ 4 → (lookup k.val).size = 2 := by decide +kernel

#print axioms table_valid
#print axioms size_two
end Erdos184Work.FourRows2

import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2200 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2200 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2200_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2200_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2200_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2200_3 : CycleData E W := ⟨4,![4,3,6,12,18,9],![2,6,3,14,27,16]⟩
def cycle2200_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2200_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2200 : PartitionData E W := ⟨6,![cycle2200_0,cycle2200_1,cycle2200_2,cycle2200_3,cycle2200_4,cycle2200_5]⟩
lemma valid_data2200 : data2200.Valid src2200 dst2200 Finset.univ := by decide +kernel

def src2201 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2201 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2201_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2201_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2201_2 : CycleData E W := ⟨3,![2,23,16,15,3],![3,8,38,26,6]⟩
def cycle2201_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2201_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,27,28,18]⟩
def cycle2201_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2201 : PartitionData E W := ⟨6,![cycle2201_0,cycle2201_1,cycle2201_2,cycle2201_3,cycle2201_4,cycle2201_5]⟩
lemma valid_data2201 : data2201.Valid src2201 dst2201 Finset.univ := by decide +kernel

def src2202 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2202 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2202_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2202_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2202_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2202_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2202_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,26,16]⟩
def cycle2202_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2202 : PartitionData E W := ⟨6,![cycle2202_0,cycle2202_1,cycle2202_2,cycle2202_3,cycle2202_4,cycle2202_5]⟩
lemma valid_data2202 : data2202.Valid src2202 dst2202 Finset.univ := by decide +kernel

def src2203 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2203 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2203_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2203_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2203_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2203_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2203_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,26,16]⟩
def cycle2203_5 : CycleData E W := ⟨3,![8,21,22,13,16],![16,18,38,28,27]⟩
def data2203 : PartitionData E W := ⟨6,![cycle2203_0,cycle2203_1,cycle2203_2,cycle2203_3,cycle2203_4,cycle2203_5]⟩
lemma valid_data2203 : data2203.Valid src2203 dst2203 Finset.univ := by decide +kernel

def src2204 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2204 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2204_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2204_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2204_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2204_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2204_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,27,28,18]⟩
def cycle2204_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2204 : PartitionData E W := ⟨6,![cycle2204_0,cycle2204_1,cycle2204_2,cycle2204_3,cycle2204_4,cycle2204_5]⟩
lemma valid_data2204 : data2204.Valid src2204 dst2204 Finset.univ := by decide +kernel

def src2205 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst2205 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle2205_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2205_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2205_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2205_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2205_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,38,16]⟩
def cycle2205_5 : CycleData E W := ⟨3,![8,21,13,16,17],![16,18,28,27,26]⟩
def data2205 : PartitionData E W := ⟨6,![cycle2205_0,cycle2205_1,cycle2205_2,cycle2205_3,cycle2205_4,cycle2205_5]⟩
lemma valid_data2205 : data2205.Valid src2205 dst2205 Finset.univ := by decide +kernel

def src2206 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst2206 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle2206_0 : CycleData E W := ⟨2,![0,10,17,9],![2,4,26,16]⟩
def cycle2206_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2206_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2206_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2206_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2206_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2206_6 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2206 : PartitionData E W := ⟨7,![cycle2206_0,cycle2206_1,cycle2206_2,cycle2206_3,cycle2206_4,cycle2206_5,cycle2206_6]⟩
lemma valid_data2206 : data2206.Valid src2206 dst2206 Finset.univ := by decide +kernel

def src2207 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst2207 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle2207_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2207_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2207_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2207_3 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,27,26,16]⟩
def cycle2207_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,27,28,18]⟩
def cycle2207_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2207 : PartitionData E W := ⟨6,![cycle2207_0,cycle2207_1,cycle2207_2,cycle2207_3,cycle2207_4,cycle2207_5]⟩
lemma valid_data2207 : data2207.Valid src2207 dst2207 Finset.univ := by decide +kernel

def src2208 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst2208 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle2208_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2208_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2208_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2208_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2208_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle2208_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2208 : PartitionData E W := ⟨6,![cycle2208_0,cycle2208_1,cycle2208_2,cycle2208_3,cycle2208_4,cycle2208_5]⟩
lemma valid_data2208 : data2208.Valid src2208 dst2208 Finset.univ := by decide +kernel

def src2209 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst2209 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle2209_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2209_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2209_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2209_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle2209_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle2209_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2209 : PartitionData E W := ⟨6,![cycle2209_0,cycle2209_1,cycle2209_2,cycle2209_3,cycle2209_4,cycle2209_5]⟩
lemma valid_data2209 : data2209.Valid src2209 dst2209 Finset.univ := by decide +kernel

def src2210 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst2210 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle2210_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2210_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2210_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2210_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2210_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle2210_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2210 : PartitionData E W := ⟨6,![cycle2210_0,cycle2210_1,cycle2210_2,cycle2210_3,cycle2210_4,cycle2210_5]⟩
lemma valid_data2210 : data2210.Valid src2210 dst2210 Finset.univ := by decide +kernel

def src2211 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst2211 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle2211_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2211_1 : CycleData E W := ⟨3,![3,19,23,20,7],![3,6,38,8,18]⟩
def cycle2211_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2211_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2211_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2211_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2211 : PartitionData E W := ⟨6,![cycle2211_0,cycle2211_1,cycle2211_2,cycle2211_3,cycle2211_4,cycle2211_5]⟩
lemma valid_data2211 : data2211.Valid src2211 dst2211 Finset.univ := by decide +kernel

def src2212 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst2212 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle2212_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2212_1 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2212_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2212_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle2212_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2212_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2212 : PartitionData E W := ⟨6,![cycle2212_0,cycle2212_1,cycle2212_2,cycle2212_3,cycle2212_4,cycle2212_5]⟩
lemma valid_data2212 : data2212.Valid src2212 dst2212 Finset.univ := by decide +kernel

def src2213 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst2213 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle2213_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2213_1 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2213_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2213_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2213_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2213_5 : CycleData E W := ⟨3,![20,12,11,18,23],![8,28,14,26,38]⟩
def data2213 : PartitionData E W := ⟨6,![cycle2213_0,cycle2213_1,cycle2213_2,cycle2213_3,cycle2213_4,cycle2213_5]⟩
lemma valid_data2213 : data2213.Valid src2213 dst2213 Finset.univ := by decide +kernel

def src2214 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst2214 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle2214_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2214_1 : CycleData E W := ⟨3,![1,20,8,16,14],![4,8,18,16,27]⟩
def cycle2214_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2214_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2214_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2214_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2214 : PartitionData E W := ⟨6,![cycle2214_0,cycle2214_1,cycle2214_2,cycle2214_3,cycle2214_4,cycle2214_5]⟩
lemma valid_data2214 : data2214.Valid src2214 dst2214 Finset.univ := by decide +kernel

def src2215 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst2215 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle2215_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2215_1 : CycleData E W := ⟨3,![1,20,8,16,14],![4,8,18,16,27]⟩
def cycle2215_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2215_3 : CycleData E W := ⟨3,![3,19,18,21,7],![3,6,26,38,18]⟩
def cycle2215_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2215_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2215 : PartitionData E W := ⟨6,![cycle2215_0,cycle2215_1,cycle2215_2,cycle2215_3,cycle2215_4,cycle2215_5]⟩
lemma valid_data2215 : data2215.Valid src2215 dst2215 Finset.univ := by decide +kernel

def src2216 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst2216 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle2216_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2216_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2216_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2216_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2216_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2216_5 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def data2216 : PartitionData E W := ⟨6,![cycle2216_0,cycle2216_1,cycle2216_2,cycle2216_3,cycle2216_4,cycle2216_5]⟩
lemma valid_data2216 : data2216.Valid src2216 dst2216 Finset.univ := by decide +kernel

def src2217 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst2217 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle2217_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2217_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,27,28,18]⟩
def cycle2217_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2217_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2217_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2217_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2217 : PartitionData E W := ⟨6,![cycle2217_0,cycle2217_1,cycle2217_2,cycle2217_3,cycle2217_4,cycle2217_5]⟩
lemma valid_data2217 : data2217.Valid src2217 dst2217 Finset.univ := by decide +kernel

def src2218 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst2218 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle2218_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2218_1 : CycleData E W := ⟨4,![3,19,13,23,20,7],![3,6,27,28,8,18]⟩
def cycle2218_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2218_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2218_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2218_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2218 : PartitionData E W := ⟨6,![cycle2218_0,cycle2218_1,cycle2218_2,cycle2218_3,cycle2218_4,cycle2218_5]⟩
lemma valid_data2218 : data2218.Valid src2218 dst2218 Finset.univ := by decide +kernel

def src2219 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst2219 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle2219_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2219_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,27,28,18]⟩
def cycle2219_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2219_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2219_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2219_5 : CycleData E W := ⟨3,![20,12,11,17,23],![8,28,14,26,38]⟩
def data2219 : PartitionData E W := ⟨6,![cycle2219_0,cycle2219_1,cycle2219_2,cycle2219_3,cycle2219_4,cycle2219_5]⟩
lemma valid_data2219 : data2219.Valid src2219 dst2219 Finset.univ := by decide +kernel

def src2220 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2220 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2220_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2220_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2220_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2220_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2220_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2220_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2220 : PartitionData E W := ⟨6,![cycle2220_0,cycle2220_1,cycle2220_2,cycle2220_3,cycle2220_4,cycle2220_5]⟩
lemma valid_data2220 : data2220.Valid src2220 dst2220 Finset.univ := by decide +kernel

def src2221 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2221 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2221_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2221_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2221_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2221_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2221_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2221_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2221 : PartitionData E W := ⟨6,![cycle2221_0,cycle2221_1,cycle2221_2,cycle2221_3,cycle2221_4,cycle2221_5]⟩
lemma valid_data2221 : data2221.Valid src2221 dst2221 Finset.univ := by decide +kernel

def src2222 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2222 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2222_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2222_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2222_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2222_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2222_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2222_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2222 : PartitionData E W := ⟨6,![cycle2222_0,cycle2222_1,cycle2222_2,cycle2222_3,cycle2222_4,cycle2222_5]⟩
lemma valid_data2222 : data2222.Valid src2222 dst2222 Finset.univ := by decide +kernel

def src2223 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst2223 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle2223_0 : CycleData E W := ⟨2,![0,14,17,9],![2,4,27,16]⟩
def cycle2223_1 : CycleData E W := ⟨3,![1,23,19,15,10],![4,8,38,6,26]⟩
def cycle2223_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2223_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2223_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle2223_5 : CycleData E W := ⟨2,![11,16,13,12],![14,26,27,28]⟩
def data2223 : PartitionData E W := ⟨6,![cycle2223_0,cycle2223_1,cycle2223_2,cycle2223_3,cycle2223_4,cycle2223_5]⟩
lemma valid_data2223 : data2223.Valid src2223 dst2223 Finset.univ := by decide +kernel

def src2224 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst2224 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle2224_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2224_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2224_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2224_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2224_4 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,26,27,16]⟩
def cycle2224_5 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def data2224 : PartitionData E W := ⟨6,![cycle2224_0,cycle2224_1,cycle2224_2,cycle2224_3,cycle2224_4,cycle2224_5]⟩
lemma valid_data2224 : data2224.Valid src2224 dst2224 Finset.univ := by decide +kernel

def src2225 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst2225 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle2225_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2225_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2225_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2225_3 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,26,27,16]⟩
def cycle2225_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2225_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2225 : PartitionData E W := ⟨6,![cycle2225_0,cycle2225_1,cycle2225_2,cycle2225_3,cycle2225_4,cycle2225_5]⟩
lemma valid_data2225 : data2225.Valid src2225 dst2225 Finset.univ := by decide +kernel

def src2226 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2226 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2226_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,27,28,14]⟩
def cycle2226_1 : CycleData E W := ⟨2,![1,23,16,10],![4,8,38,26]⟩
def cycle2226_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2226_3 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2226_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2226_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data2226 : PartitionData E W := ⟨6,![cycle2226_0,cycle2226_1,cycle2226_2,cycle2226_3,cycle2226_4,cycle2226_5]⟩
lemma valid_data2226 : data2226.Valid src2226 dst2226 Finset.univ := by decide +kernel

def src2227 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2227 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2227_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2227_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2227_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2227_3 : CycleData E W := ⟨4,![3,15,16,22,12,6],![3,6,26,38,28,14]⟩
def cycle2227_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2227_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def data2227 : PartitionData E W := ⟨6,![cycle2227_0,cycle2227_1,cycle2227_2,cycle2227_3,cycle2227_4,cycle2227_5]⟩
lemma valid_data2227 : data2227.Valid src2227 dst2227 Finset.univ := by decide +kernel

def src2228 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2228 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2228_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2228_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2228_2 : CycleData E W := ⟨3,![2,23,16,15,3],![3,8,38,26,6]⟩
def cycle2228_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2228_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2228_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2228 : PartitionData E W := ⟨6,![cycle2228_0,cycle2228_1,cycle2228_2,cycle2228_3,cycle2228_4,cycle2228_5]⟩
lemma valid_data2228 : data2228.Valid src2228 dst2228 Finset.univ := by decide +kernel

def src2229 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2229 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2229_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2229_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2229_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2229_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2229_4 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2229_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2229 : PartitionData E W := ⟨6,![cycle2229_0,cycle2229_1,cycle2229_2,cycle2229_3,cycle2229_4,cycle2229_5]⟩
lemma valid_data2229 : data2229.Valid src2229 dst2229 Finset.univ := by decide +kernel

def src2230 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2230 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2230_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2230_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2230_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2230_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2230_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2230_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def data2230 : PartitionData E W := ⟨6,![cycle2230_0,cycle2230_1,cycle2230_2,cycle2230_3,cycle2230_4,cycle2230_5]⟩
lemma valid_data2230 : data2230.Valid src2230 dst2230 Finset.univ := by decide +kernel

def src2231 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2231 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2231_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2231_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2231_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2231_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2231_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2231_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2231 : PartitionData E W := ⟨6,![cycle2231_0,cycle2231_1,cycle2231_2,cycle2231_3,cycle2231_4,cycle2231_5]⟩
lemma valid_data2231 : data2231.Valid src2231 dst2231 Finset.univ := by decide +kernel

def src2232 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst2232 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle2232_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2232_1 : CycleData E W := ⟨3,![1,23,18,11,10],![4,8,38,27,26]⟩
def cycle2232_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2232_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2232_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2232_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data2232 : PartitionData E W := ⟨6,![cycle2232_0,cycle2232_1,cycle2232_2,cycle2232_3,cycle2232_4,cycle2232_5]⟩
lemma valid_data2232 : data2232.Valid src2232 dst2232 Finset.univ := by decide +kernel

def src2233 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst2233 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle2233_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle2233_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2233_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2233_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2233_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2233_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2233_6 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2233 : PartitionData E W := ⟨7,![cycle2233_0,cycle2233_1,cycle2233_2,cycle2233_3,cycle2233_4,cycle2233_5,cycle2233_6]⟩
lemma valid_data2233 : data2233.Valid src2233 dst2233 Finset.univ := by decide +kernel

def src2234 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst2234 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle2234_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,27,14]⟩
def cycle2234_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2234_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2234_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2234_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2234_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2234 : PartitionData E W := ⟨6,![cycle2234_0,cycle2234_1,cycle2234_2,cycle2234_3,cycle2234_4,cycle2234_5]⟩
lemma valid_data2234 : data2234.Valid src2234 dst2234 Finset.univ := by decide +kernel

def src2235 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst2235 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle2235_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2235_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2235_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2235_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2235_4 : CycleData E W := ⟨4,![4,19,22,21,8,9],![2,6,38,28,18,16]⟩
def cycle2235_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2235 : PartitionData E W := ⟨6,![cycle2235_0,cycle2235_1,cycle2235_2,cycle2235_3,cycle2235_4,cycle2235_5]⟩
lemma valid_data2235 : data2235.Valid src2235 dst2235 Finset.univ := by decide +kernel

def src2236 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst2236 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle2236_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,27,14]⟩
def cycle2236_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2236_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2236_3 : CycleData E W := ⟨3,![3,19,22,13,6],![3,6,38,28,14]⟩
def cycle2236_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2236_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def data2236 : PartitionData E W := ⟨6,![cycle2236_0,cycle2236_1,cycle2236_2,cycle2236_3,cycle2236_4,cycle2236_5]⟩
lemma valid_data2236 : data2236.Valid src2236 dst2236 Finset.univ := by decide +kernel

def src2237 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst2237 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle2237_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,27,14]⟩
def cycle2237_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2237_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2237_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2237_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2237_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2237 : PartitionData E W := ⟨6,![cycle2237_0,cycle2237_1,cycle2237_2,cycle2237_3,cycle2237_4,cycle2237_5]⟩
lemma valid_data2237 : data2237.Valid src2237 dst2237 Finset.univ := by decide +kernel

def src2238 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst2238 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle2238_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2238_1 : CycleData E W := ⟨3,![3,19,23,20,7],![3,6,38,8,18]⟩
def cycle2238_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2238_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2238_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2238_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2238 : PartitionData E W := ⟨6,![cycle2238_0,cycle2238_1,cycle2238_2,cycle2238_3,cycle2238_4,cycle2238_5]⟩
lemma valid_data2238 : data2238.Valid src2238 dst2238 Finset.univ := by decide +kernel

def src2239 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst2239 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle2239_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2239_1 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2239_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2239_3 : CycleData E W := ⟨3,![20,8,16,11,23],![8,18,16,26,28]⟩
def cycle2239_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2239_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2239 : PartitionData E W := ⟨6,![cycle2239_0,cycle2239_1,cycle2239_2,cycle2239_3,cycle2239_4,cycle2239_5]⟩
lemma valid_data2239 : data2239.Valid src2239 dst2239 Finset.univ := by decide +kernel

def src2240 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst2240 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle2240_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2240_1 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2240_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2240_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2240_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2240_5 : CycleData E W := ⟨3,![20,12,13,18,23],![8,28,14,27,38]⟩
def data2240 : PartitionData E W := ⟨6,![cycle2240_0,cycle2240_1,cycle2240_2,cycle2240_3,cycle2240_4,cycle2240_5]⟩
lemma valid_data2240 : data2240.Valid src2240 dst2240 Finset.univ := by decide +kernel

def src2241 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst2241 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle2241_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2241_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2241_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2241_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2241_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2241_5 : CycleData E W := ⟨3,![8,21,22,17,16],![16,18,28,38,26]⟩
def data2241 : PartitionData E W := ⟨6,![cycle2241_0,cycle2241_1,cycle2241_2,cycle2241_3,cycle2241_4,cycle2241_5]⟩
lemma valid_data2241 : data2241.Valid src2241 dst2241 Finset.univ := by decide +kernel

def src2242 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst2242 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle2242_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2242_1 : CycleData E W := ⟨3,![1,23,22,18,14],![4,8,28,38,27]⟩
def cycle2242_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2242_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2242_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2242_5 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def data2242 : PartitionData E W := ⟨6,![cycle2242_0,cycle2242_1,cycle2242_2,cycle2242_3,cycle2242_4,cycle2242_5]⟩
lemma valid_data2242 : data2242.Valid src2242 dst2242 Finset.univ := by decide +kernel

def src2243 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst2243 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle2243_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2243_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2243_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle2243_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2243_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2243_5 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def data2243 : PartitionData E W := ⟨6,![cycle2243_0,cycle2243_1,cycle2243_2,cycle2243_3,cycle2243_4,cycle2243_5]⟩
lemma valid_data2243 : data2243.Valid src2243 dst2243 Finset.univ := by decide +kernel

def src2244 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst2244 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle2244_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2244_1 : CycleData E W := ⟨3,![2,1,10,19,3],![3,8,4,26,6]⟩
def cycle2244_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2244_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2244_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle2244_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2244 : PartitionData E W := ⟨6,![cycle2244_0,cycle2244_1,cycle2244_2,cycle2244_3,cycle2244_4,cycle2244_5]⟩
lemma valid_data2244 : data2244.Valid src2244 dst2244 Finset.univ := by decide +kernel

def src2245 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst2245 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle2245_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2245_1 : CycleData E W := ⟨3,![2,1,10,19,3],![3,8,4,26,6]⟩
def cycle2245_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2245_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle2245_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle2245_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2245 : PartitionData E W := ⟨6,![cycle2245_0,cycle2245_1,cycle2245_2,cycle2245_3,cycle2245_4,cycle2245_5]⟩
lemma valid_data2245 : data2245.Valid src2245 dst2245 Finset.univ := by decide +kernel

def src2246 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst2246 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle2246_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2246_1 : CycleData E W := ⟨3,![2,1,10,19,3],![3,8,4,26,6]⟩
def cycle2246_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2246_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2246_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle2246_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data2246 : PartitionData E W := ⟨6,![cycle2246_0,cycle2246_1,cycle2246_2,cycle2246_3,cycle2246_4,cycle2246_5]⟩
lemma valid_data2246 : data2246.Valid src2246 dst2246 Finset.univ := by decide +kernel

def src2247 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst2247 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle2247_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2247_1 : CycleData E W := ⟨3,![3,19,11,21,7],![3,6,26,28,18]⟩
def cycle2247_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2247_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2247_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2247_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2247 : PartitionData E W := ⟨6,![cycle2247_0,cycle2247_1,cycle2247_2,cycle2247_3,cycle2247_4,cycle2247_5]⟩
lemma valid_data2247 : data2247.Valid src2247 dst2247 Finset.univ := by decide +kernel

def src2248 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst2248 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle2248_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2248_1 : CycleData E W := ⟨4,![3,19,11,23,20,7],![3,6,26,28,8,18]⟩
def cycle2248_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2248_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2248_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2248_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2248 : PartitionData E W := ⟨6,![cycle2248_0,cycle2248_1,cycle2248_2,cycle2248_3,cycle2248_4,cycle2248_5]⟩
lemma valid_data2248 : data2248.Valid src2248 dst2248 Finset.univ := by decide +kernel

def src2249 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst2249 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle2249_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2249_1 : CycleData E W := ⟨3,![3,19,11,21,7],![3,6,26,28,18]⟩
def cycle2249_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2249_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2249_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2249_5 : CycleData E W := ⟨3,![20,12,13,17,23],![8,28,14,27,38]⟩
def data2249 : PartitionData E W := ⟨6,![cycle2249_0,cycle2249_1,cycle2249_2,cycle2249_3,cycle2249_4,cycle2249_5]⟩
lemma valid_data2249 : data2249.Valid src2249 dst2249 Finset.univ := by decide +kernel

def src2250 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2250 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2250_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2250_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2250_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2250_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2250_4 : CycleData E W := ⟨2,![5,13,17,9],![2,14,27,16]⟩
def cycle2250_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data2250 : PartitionData E W := ⟨6,![cycle2250_0,cycle2250_1,cycle2250_2,cycle2250_3,cycle2250_4,cycle2250_5]⟩
lemma valid_data2250 : data2250.Valid src2250 dst2250 Finset.univ := by decide +kernel

def src2251 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2251 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2251_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2251_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2251_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2251_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2251_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2251_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def data2251 : PartitionData E W := ⟨6,![cycle2251_0,cycle2251_1,cycle2251_2,cycle2251_3,cycle2251_4,cycle2251_5]⟩
lemma valid_data2251 : data2251.Valid src2251 dst2251 Finset.univ := by decide +kernel

def src2252 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2252 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2252_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2252_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2252_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2252_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2252_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2252_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2252 : PartitionData E W := ⟨6,![cycle2252_0,cycle2252_1,cycle2252_2,cycle2252_3,cycle2252_4,cycle2252_5]⟩
lemma valid_data2252 : data2252.Valid src2252 dst2252 Finset.univ := by decide +kernel

def src2253 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2253 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2253_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2253_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2253_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2253_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2253_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2253_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data2253 : PartitionData E W := ⟨6,![cycle2253_0,cycle2253_1,cycle2253_2,cycle2253_3,cycle2253_4,cycle2253_5]⟩
lemma valid_data2253 : data2253.Valid src2253 dst2253 Finset.univ := by decide +kernel

def src2254 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2254 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2254_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2254_1 : CycleData E W := ⟨3,![1,23,22,18,14],![4,8,28,38,27]⟩
def cycle2254_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2254_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2254_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2254_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def data2254 : PartitionData E W := ⟨6,![cycle2254_0,cycle2254_1,cycle2254_2,cycle2254_3,cycle2254_4,cycle2254_5]⟩
lemma valid_data2254 : data2254.Valid src2254 dst2254 Finset.univ := by decide +kernel

def src2255 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2255 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2255_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2255_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2255_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle2255_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2255_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2255_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2255 : PartitionData E W := ⟨6,![cycle2255_0,cycle2255_1,cycle2255_2,cycle2255_3,cycle2255_4,cycle2255_5]⟩
lemma valid_data2255 : data2255.Valid src2255 dst2255 Finset.univ := by decide +kernel

def src2256 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2256 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2256_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2256_1 : CycleData E W := ⟨3,![1,20,8,17,10],![4,8,18,16,26]⟩
def cycle2256_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2256_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2256_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2256_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2256 : PartitionData E W := ⟨6,![cycle2256_0,cycle2256_1,cycle2256_2,cycle2256_3,cycle2256_4,cycle2256_5]⟩
lemma valid_data2256 : data2256.Valid src2256 dst2256 Finset.univ := by decide +kernel

def src2257 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2257 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2257_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2257_1 : CycleData E W := ⟨3,![1,20,8,17,10],![4,8,18,16,26]⟩
def cycle2257_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2257_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2257_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2257_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2257 : PartitionData E W := ⟨6,![cycle2257_0,cycle2257_1,cycle2257_2,cycle2257_3,cycle2257_4,cycle2257_5]⟩
lemma valid_data2257 : data2257.Valid src2257 dst2257 Finset.univ := by decide +kernel

def src2258 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2258 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2258_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2258_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2258_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2258_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2258_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2258_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2258 : PartitionData E W := ⟨6,![cycle2258_0,cycle2258_1,cycle2258_2,cycle2258_3,cycle2258_4,cycle2258_5]⟩
lemma valid_data2258 : data2258.Valid src2258 dst2258 Finset.univ := by decide +kernel

def src2259 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst2259 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle2259_0 : CycleData E W := ⟨2,![0,10,17,9],![2,4,26,16]⟩
def cycle2259_1 : CycleData E W := ⟨3,![1,23,19,15,14],![4,8,38,6,27]⟩
def cycle2259_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2259_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2259_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle2259_5 : CycleData E W := ⟨2,![12,11,16,13],![14,28,26,27]⟩
def data2259 : PartitionData E W := ⟨6,![cycle2259_0,cycle2259_1,cycle2259_2,cycle2259_3,cycle2259_4,cycle2259_5]⟩
lemma valid_data2259 : data2259.Valid src2259 dst2259 Finset.univ := by decide +kernel

def src2260 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst2260 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle2260_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2260_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2260_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2260_3 : CycleData E W := ⟨3,![3,19,22,12,6],![3,6,38,28,14]⟩
def cycle2260_4 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,27,26,16]⟩
def cycle2260_5 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def data2260 : PartitionData E W := ⟨6,![cycle2260_0,cycle2260_1,cycle2260_2,cycle2260_3,cycle2260_4,cycle2260_5]⟩
lemma valid_data2260 : data2260.Valid src2260 dst2260 Finset.univ := by decide +kernel

def src2261 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst2261 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle2261_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2261_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2261_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2261_3 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,27,26,16]⟩
def cycle2261_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2261_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2261 : PartitionData E W := ⟨6,![cycle2261_0,cycle2261_1,cycle2261_2,cycle2261_3,cycle2261_4,cycle2261_5]⟩
lemma valid_data2261 : data2261.Valid src2261 dst2261 Finset.univ := by decide +kernel

def src2262 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst2262 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle2262_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2262_1 : CycleData E W := ⟨3,![3,19,23,20,7],![3,6,38,8,18]⟩
def cycle2262_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2262_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2262_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2262_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2262 : PartitionData E W := ⟨6,![cycle2262_0,cycle2262_1,cycle2262_2,cycle2262_3,cycle2262_4,cycle2262_5]⟩
lemma valid_data2262 : data2262.Valid src2262 dst2262 Finset.univ := by decide +kernel

def src2263 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst2263 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle2263_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2263_1 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2263_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2263_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,26,28]⟩
def cycle2263_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2263_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2263 : PartitionData E W := ⟨6,![cycle2263_0,cycle2263_1,cycle2263_2,cycle2263_3,cycle2263_4,cycle2263_5]⟩
lemma valid_data2263 : data2263.Valid src2263 dst2263 Finset.univ := by decide +kernel

def src2264 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst2264 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle2264_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2264_1 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2264_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2264_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2264_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,27,38,8,28]⟩
def cycle2264_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2264 : PartitionData E W := ⟨6,![cycle2264_0,cycle2264_1,cycle2264_2,cycle2264_3,cycle2264_4,cycle2264_5]⟩
lemma valid_data2264 : data2264.Valid src2264 dst2264 Finset.univ := by decide +kernel

def src2265 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst2265 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle2265_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2265_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2265_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2265_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2265_4 : CycleData E W := ⟨3,![6,12,16,8,7],![3,14,26,16,18]⟩
def cycle2265_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2265 : PartitionData E W := ⟨6,![cycle2265_0,cycle2265_1,cycle2265_2,cycle2265_3,cycle2265_4,cycle2265_5]⟩
lemma valid_data2265 : data2265.Valid src2265 dst2265 Finset.univ := by decide +kernel

def src2266 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst2266 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle2266_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2266_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2266_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2266_3 : CycleData E W := ⟨4,![4,3,6,12,16,9],![2,6,3,14,26,16]⟩
def cycle2266_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle2266_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2266 : PartitionData E W := ⟨6,![cycle2266_0,cycle2266_1,cycle2266_2,cycle2266_3,cycle2266_4,cycle2266_5]⟩
lemma valid_data2266 : data2266.Valid src2266 dst2266 Finset.univ := by decide +kernel

def src2267 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst2267 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle2267_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2267_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2267_2 : CycleData E W := ⟨3,![2,23,17,12,6],![3,8,38,26,14]⟩
def cycle2267_3 : CycleData E W := ⟨3,![3,19,18,22,7],![3,6,27,38,18]⟩
def cycle2267_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2267_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2267 : PartitionData E W := ⟨6,![cycle2267_0,cycle2267_1,cycle2267_2,cycle2267_3,cycle2267_4,cycle2267_5]⟩
lemma valid_data2267 : data2267.Valid src2267 dst2267 Finset.univ := by decide +kernel

def src2268 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst2268 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle2268_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2268_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2268_2 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2268_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2268_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle2268_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2268 : PartitionData E W := ⟨6,![cycle2268_0,cycle2268_1,cycle2268_2,cycle2268_3,cycle2268_4,cycle2268_5]⟩
lemma valid_data2268 : data2268.Valid src2268 dst2268 Finset.univ := by decide +kernel

def src2269 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst2269 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle2269_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2269_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2269_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2269_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2269_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2269_5 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle2269_6 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2269 : PartitionData E W := ⟨7,![cycle2269_0,cycle2269_1,cycle2269_2,cycle2269_3,cycle2269_4,cycle2269_5,cycle2269_6]⟩
lemma valid_data2269 : data2269.Valid src2269 dst2269 Finset.univ := by decide +kernel

def src2270 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst2270 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle2270_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2270_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2270_2 : CycleData E W := ⟨4,![2,23,17,16,8,7],![3,8,38,27,16,18]⟩
def cycle2270_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2270_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2270_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data2270 : PartitionData E W := ⟨6,![cycle2270_0,cycle2270_1,cycle2270_2,cycle2270_3,cycle2270_4,cycle2270_5]⟩
lemma valid_data2270 : data2270.Valid src2270 dst2270 Finset.univ := by decide +kernel

def src2271 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst2271 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle2271_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2271_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,26,28,18]⟩
def cycle2271_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2271_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2271_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle2271_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2271 : PartitionData E W := ⟨6,![cycle2271_0,cycle2271_1,cycle2271_2,cycle2271_3,cycle2271_4,cycle2271_5]⟩
lemma valid_data2271 : data2271.Valid src2271 dst2271 Finset.univ := by decide +kernel

def src2272 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst2272 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle2272_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2272_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2272_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2272_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2272_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2272_5 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2272_6 : CycleData E W := ⟨2,![13,22,17,18],![26,28,38,27]⟩
def data2272 : PartitionData E W := ⟨7,![cycle2272_0,cycle2272_1,cycle2272_2,cycle2272_3,cycle2272_4,cycle2272_5,cycle2272_6]⟩
lemma valid_data2272 : data2272.Valid src2272 dst2272 Finset.univ := by decide +kernel

def src2273 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst2273 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle2273_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2273_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,26,28,18]⟩
def cycle2273_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2273_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2273_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,27,38,8,28]⟩
def cycle2273_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2273 : PartitionData E W := ⟨6,![cycle2273_0,cycle2273_1,cycle2273_2,cycle2273_3,cycle2273_4,cycle2273_5]⟩
lemma valid_data2273 : data2273.Valid src2273 dst2273 Finset.univ := by decide +kernel

def src2274 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2274 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2274_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2274_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2274_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2274_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2274_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,27,16]⟩
def cycle2274_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2274 : PartitionData E W := ⟨6,![cycle2274_0,cycle2274_1,cycle2274_2,cycle2274_3,cycle2274_4,cycle2274_5]⟩
lemma valid_data2274 : data2274.Valid src2274 dst2274 Finset.univ := by decide +kernel

def src2275 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2275 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2275_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2275_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2275_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2275_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2275_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,27,16]⟩
def cycle2275_5 : CycleData E W := ⟨3,![8,21,22,13,16],![16,18,38,28,26]⟩
def data2275 : PartitionData E W := ⟨6,![cycle2275_0,cycle2275_1,cycle2275_2,cycle2275_3,cycle2275_4,cycle2275_5]⟩
lemma valid_data2275 : data2275.Valid src2275 dst2275 Finset.univ := by decide +kernel

def src2276 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2276 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2276_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2276_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2276_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2276_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2276_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,26,28,18]⟩
def cycle2276_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2276 : PartitionData E W := ⟨6,![cycle2276_0,cycle2276_1,cycle2276_2,cycle2276_3,cycle2276_4,cycle2276_5]⟩
lemma valid_data2276 : data2276.Valid src2276 dst2276 Finset.univ := by decide +kernel

def src2277 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2277 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2277_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2277_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2277_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2277_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2277_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,27,38,16]⟩
def cycle2277_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2277 : PartitionData E W := ⟨6,![cycle2277_0,cycle2277_1,cycle2277_2,cycle2277_3,cycle2277_4,cycle2277_5]⟩
lemma valid_data2277 : data2277.Valid src2277 dst2277 Finset.univ := by decide +kernel

def src2278 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2278 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2278_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2278_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2278_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2278_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2278_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,27,38,16]⟩
def cycle2278_5 : CycleData E W := ⟨3,![8,21,22,13,16],![16,18,38,28,26]⟩
def data2278 : PartitionData E W := ⟨6,![cycle2278_0,cycle2278_1,cycle2278_2,cycle2278_3,cycle2278_4,cycle2278_5]⟩
lemma valid_data2278 : data2278.Valid src2278 dst2278 Finset.univ := by decide +kernel

def src2279 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2279 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2279_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2279_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2279_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2279_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2279_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,26,28,18]⟩
def cycle2279_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2279 : PartitionData E W := ⟨6,![cycle2279_0,cycle2279_1,cycle2279_2,cycle2279_3,cycle2279_4,cycle2279_5]⟩
lemma valid_data2279 : data2279.Valid src2279 dst2279 Finset.univ := by decide +kernel

def src2280 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst2280 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle2280_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2280_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2280_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2280_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2280_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,38,16]⟩
def cycle2280_5 : CycleData E W := ⟨3,![8,21,13,16,17],![16,18,28,26,27]⟩
def data2280 : PartitionData E W := ⟨6,![cycle2280_0,cycle2280_1,cycle2280_2,cycle2280_3,cycle2280_4,cycle2280_5]⟩
lemma valid_data2280 : data2280.Valid src2280 dst2280 Finset.univ := by decide +kernel

def src2281 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst2281 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle2281_0 : CycleData E W := ⟨2,![0,10,17,9],![2,4,27,16]⟩
def cycle2281_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2281_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2281_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2281_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2281_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2281_6 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2281 : PartitionData E W := ⟨7,![cycle2281_0,cycle2281_1,cycle2281_2,cycle2281_3,cycle2281_4,cycle2281_5,cycle2281_6]⟩
lemma valid_data2281 : data2281.Valid src2281 dst2281 Finset.univ := by decide +kernel

def src2282 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst2282 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle2282_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2282_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2282_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2282_3 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,26,27,16]⟩
def cycle2282_4 : CycleData E W := ⟨3,![6,12,13,21,7],![3,14,26,28,18]⟩
def cycle2282_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2282 : PartitionData E W := ⟨6,![cycle2282_0,cycle2282_1,cycle2282_2,cycle2282_3,cycle2282_4,cycle2282_5]⟩
lemma valid_data2282 : data2282.Valid src2282 dst2282 Finset.univ := by decide +kernel

def src2283 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2283 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2283_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2283_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2283_2 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2283_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2283_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2283_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2283 : PartitionData E W := ⟨6,![cycle2283_0,cycle2283_1,cycle2283_2,cycle2283_3,cycle2283_4,cycle2283_5]⟩
lemma valid_data2283 : data2283.Valid src2283 dst2283 Finset.univ := by decide +kernel

def src2284 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2284 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2284_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2284_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2284_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2284_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2284_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2284_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2284_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2284 : PartitionData E W := ⟨7,![cycle2284_0,cycle2284_1,cycle2284_2,cycle2284_3,cycle2284_4,cycle2284_5,cycle2284_6]⟩
lemma valid_data2284 : data2284.Valid src2284 dst2284 Finset.univ := by decide +kernel

def src2285 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2285 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2285_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2285_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2285_2 : CycleData E W := ⟨3,![2,23,16,12,6],![3,8,38,26,14]⟩
def cycle2285_3 : CycleData E W := ⟨3,![3,15,13,21,7],![3,6,26,28,18]⟩
def cycle2285_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2285_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2285 : PartitionData E W := ⟨6,![cycle2285_0,cycle2285_1,cycle2285_2,cycle2285_3,cycle2285_4,cycle2285_5]⟩
lemma valid_data2285 : data2285.Valid src2285 dst2285 Finset.univ := by decide +kernel

def src2286 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst2286 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle2286_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2286_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2286_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2286_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2286_4 : CycleData E W := ⟨4,![4,19,22,21,8,9],![2,6,38,28,18,16]⟩
def cycle2286_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2286 : PartitionData E W := ⟨6,![cycle2286_0,cycle2286_1,cycle2286_2,cycle2286_3,cycle2286_4,cycle2286_5]⟩
lemma valid_data2286 : data2286.Valid src2286 dst2286 Finset.univ := by decide +kernel

def src2287 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst2287 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle2287_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,27,26,14]⟩
def cycle2287_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2287_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2287_3 : CycleData E W := ⟨3,![3,19,22,13,6],![3,6,38,28,14]⟩
def cycle2287_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2287_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def data2287 : PartitionData E W := ⟨6,![cycle2287_0,cycle2287_1,cycle2287_2,cycle2287_3,cycle2287_4,cycle2287_5]⟩
lemma valid_data2287 : data2287.Valid src2287 dst2287 Finset.univ := by decide +kernel

def src2288 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst2288 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle2288_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,27,26,14]⟩
def cycle2288_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2288_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2288_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2288_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2288_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2288 : PartitionData E W := ⟨6,![cycle2288_0,cycle2288_1,cycle2288_2,cycle2288_3,cycle2288_4,cycle2288_5]⟩
lemma valid_data2288 : data2288.Valid src2288 dst2288 Finset.univ := by decide +kernel

def src2289 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst2289 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle2289_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2289_1 : CycleData E W := ⟨3,![1,23,16,11,10],![4,8,38,26,27]⟩
def cycle2289_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2289_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2289_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2289_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data2289 : PartitionData E W := ⟨6,![cycle2289_0,cycle2289_1,cycle2289_2,cycle2289_3,cycle2289_4,cycle2289_5]⟩
lemma valid_data2289 : data2289.Valid src2289 dst2289 Finset.univ := by decide +kernel

def src2290 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst2290 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle2290_0 : CycleData E W := ⟨2,![0,10,18,9],![2,4,27,16]⟩
def cycle2290_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2290_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2290_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2290_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2290_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2290_6 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2290 : PartitionData E W := ⟨7,![cycle2290_0,cycle2290_1,cycle2290_2,cycle2290_3,cycle2290_4,cycle2290_5,cycle2290_6]⟩
lemma valid_data2290 : data2290.Valid src2290 dst2290 Finset.univ := by decide +kernel

def src2291 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst2291 : E → W := ![4,8,3,6,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle2291_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,27,26,14]⟩
def cycle2291_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2291_2 : CycleData E W := ⟨3,![2,23,16,15,3],![3,8,38,26,6]⟩
def cycle2291_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2291_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2291_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2291 : PartitionData E W := ⟨6,![cycle2291_0,cycle2291_1,cycle2291_2,cycle2291_3,cycle2291_4,cycle2291_5]⟩
lemma valid_data2291 : data2291.Valid src2291 dst2291 Finset.univ := by decide +kernel

def src2292 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2292 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2292_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2292_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2292_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2292_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2292_4 : CycleData E W := ⟨3,![15,16,6,12,19],![6,26,16,14,27]⟩
def cycle2292_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2292 : PartitionData E W := ⟨6,![cycle2292_0,cycle2292_1,cycle2292_2,cycle2292_3,cycle2292_4,cycle2292_5]⟩
lemma valid_data2292 : data2292.Valid src2292 dst2292 Finset.univ := by decide +kernel

def src2293 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2293 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2293_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2293_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2293_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2293_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2293_4 : CycleData E W := ⟨5,![4,19,12,6,17,21,9],![2,6,27,14,16,38,18]⟩
def cycle2293_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2293 : PartitionData E W := ⟨6,![cycle2293_0,cycle2293_1,cycle2293_2,cycle2293_3,cycle2293_4,cycle2293_5]⟩
lemma valid_data2293 : data2293.Valid src2293 dst2293 Finset.univ := by decide +kernel

def src2294 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2294 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2294_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2294_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2294_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2294_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2294_4 : CycleData E W := ⟨3,![15,16,6,12,19],![6,26,16,14,27]⟩
def cycle2294_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2294 : PartitionData E W := ⟨6,![cycle2294_0,cycle2294_1,cycle2294_2,cycle2294_3,cycle2294_4,cycle2294_5]⟩
lemma valid_data2294 : data2294.Valid src2294 dst2294 Finset.univ := by decide +kernel

def src2295 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2295 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2295_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2295_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2295_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2295_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2295_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle2295_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2295 : PartitionData E W := ⟨6,![cycle2295_0,cycle2295_1,cycle2295_2,cycle2295_3,cycle2295_4,cycle2295_5]⟩
lemma valid_data2295 : data2295.Valid src2295 dst2295 Finset.univ := by decide +kernel

def src2296 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2296 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2296_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2296_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2296_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2296_3 : CycleData E W := ⟨3,![3,15,16,17,7],![3,6,26,38,16]⟩
def cycle2296_4 : CycleData E W := ⟨4,![4,19,13,22,21,9],![2,6,27,28,38,18]⟩
def cycle2296_5 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def data2296 : PartitionData E W := ⟨6,![cycle2296_0,cycle2296_1,cycle2296_2,cycle2296_3,cycle2296_4,cycle2296_5]⟩
lemma valid_data2296 : data2296.Valid src2296 dst2296 Finset.univ := by decide +kernel

def src2297 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2297 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2297_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2297_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2297_2 : CycleData E W := ⟨3,![2,23,16,15,3],![3,8,38,26,6]⟩
def cycle2297_3 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2297_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle2297_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data2297 : PartitionData E W := ⟨6,![cycle2297_0,cycle2297_1,cycle2297_2,cycle2297_3,cycle2297_4,cycle2297_5]⟩
lemma valid_data2297 : data2297.Valid src2297 dst2297 Finset.univ := by decide +kernel

def src2298 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2298 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2298_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2298_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2298_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,26,16]⟩
def cycle2298_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2298_4 : CycleData E W := ⟨1,![6,16,12],![14,16,27]⟩
def cycle2298_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2298 : PartitionData E W := ⟨6,![cycle2298_0,cycle2298_1,cycle2298_2,cycle2298_3,cycle2298_4,cycle2298_5]⟩
lemma valid_data2298 : data2298.Valid src2298 dst2298 Finset.univ := by decide +kernel

def src2299 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2299 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2299_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2299_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2299_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2299_3 : CycleData E W := ⟨3,![3,15,12,6,7],![3,6,27,14,16]⟩
def cycle2299_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2299_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data2299 : PartitionData E W := ⟨6,![cycle2299_0,cycle2299_1,cycle2299_2,cycle2299_3,cycle2299_4,cycle2299_5]⟩
lemma valid_data2299 : data2299.Valid src2299 dst2299 Finset.univ := by decide +kernel

def src2300 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2300 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2300_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2300_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2300_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,26,16]⟩
def cycle2300_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2300_4 : CycleData E W := ⟨1,![6,16,12],![14,16,27]⟩
def cycle2300_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2300 : PartitionData E W := ⟨6,![cycle2300_0,cycle2300_1,cycle2300_2,cycle2300_3,cycle2300_4,cycle2300_5]⟩
lemma valid_data2300 : data2300.Valid src2300 dst2300 Finset.univ := by decide +kernel

def src2301 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2301 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2301_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2301_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2301_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2301_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2301_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2301_5 : CycleData E W := ⟨2,![6,17,13,12],![14,16,27,28]⟩
def data2301 : PartitionData E W := ⟨6,![cycle2301_0,cycle2301_1,cycle2301_2,cycle2301_3,cycle2301_4,cycle2301_5]⟩
lemma valid_data2301 : data2301.Valid src2301 dst2301 Finset.univ := by decide +kernel

def src2302 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2302 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2302_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2302_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2302_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2302_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2302_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2302_5 : CycleData E W := ⟨3,![6,17,18,22,12],![14,16,27,38,28]⟩
def data2302 : PartitionData E W := ⟨6,![cycle2302_0,cycle2302_1,cycle2302_2,cycle2302_3,cycle2302_4,cycle2302_5]⟩
lemma valid_data2302 : data2302.Valid src2302 dst2302 Finset.univ := by decide +kernel

def src2303 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2303 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2303_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2303_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2303_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2303_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2303_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2303_5 : CycleData E W := ⟨2,![6,17,13,12],![14,16,27,28]⟩
def data2303 : PartitionData E W := ⟨6,![cycle2303_0,cycle2303_1,cycle2303_2,cycle2303_3,cycle2303_4,cycle2303_5]⟩
lemma valid_data2303 : data2303.Valid src2303 dst2303 Finset.univ := by decide +kernel

def src2304 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2304 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2304_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2304_1 : CycleData E W := ⟨3,![1,23,22,13,14],![4,8,38,28,27]⟩
def cycle2304_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2304_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2304_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2304_5 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def data2304 : PartitionData E W := ⟨6,![cycle2304_0,cycle2304_1,cycle2304_2,cycle2304_3,cycle2304_4,cycle2304_5]⟩
lemma valid_data2304 : data2304.Valid src2304 dst2304 Finset.univ := by decide +kernel

def src2305 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2305 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2305_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2305_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2305_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2305_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2305_4 : CycleData E W := ⟨3,![4,15,16,21,9],![2,6,26,38,18]⟩
def cycle2305_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data2305 : PartitionData E W := ⟨6,![cycle2305_0,cycle2305_1,cycle2305_2,cycle2305_3,cycle2305_4,cycle2305_5]⟩
lemma valid_data2305 : data2305.Valid src2305 dst2305 Finset.univ := by decide +kernel

def src2306 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2306 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2306_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2306_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2306_2 : CycleData E W := ⟨2,![2,23,22,8],![3,8,38,18]⟩
def cycle2306_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2306_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2306_5 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def data2306 : PartitionData E W := ⟨6,![cycle2306_0,cycle2306_1,cycle2306_2,cycle2306_3,cycle2306_4,cycle2306_5]⟩
lemma valid_data2306 : data2306.Valid src2306 dst2306 Finset.univ := by decide +kernel

def src2307 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2307 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2307_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,27,28,14]⟩
def cycle2307_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2307_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2307_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2307_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2307_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2307 : PartitionData E W := ⟨6,![cycle2307_0,cycle2307_1,cycle2307_2,cycle2307_3,cycle2307_4,cycle2307_5]⟩
lemma valid_data2307 : data2307.Valid src2307 dst2307 Finset.univ := by decide +kernel

def src2308 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2308 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2308_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2308_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2308_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2308_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2308_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2308_5 : CycleData E W := ⟨3,![6,17,18,22,12],![14,16,26,38,28]⟩
def data2308 : PartitionData E W := ⟨6,![cycle2308_0,cycle2308_1,cycle2308_2,cycle2308_3,cycle2308_4,cycle2308_5]⟩
lemma valid_data2308 : data2308.Valid src2308 dst2308 Finset.univ := by decide +kernel

def src2309 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2309 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2309_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,27,28,14]⟩
def cycle2309_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2309_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2309_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2309_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2309_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2309 : PartitionData E W := ⟨6,![cycle2309_0,cycle2309_1,cycle2309_2,cycle2309_3,cycle2309_4,cycle2309_5]⟩
lemma valid_data2309 : data2309.Valid src2309 dst2309 Finset.univ := by decide +kernel

def src2310 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2310 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2310_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2310_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2310_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2310_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2310_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2310_5 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def data2310 : PartitionData E W := ⟨6,![cycle2310_0,cycle2310_1,cycle2310_2,cycle2310_3,cycle2310_4,cycle2310_5]⟩
lemma valid_data2310 : data2310.Valid src2310 dst2310 Finset.univ := by decide +kernel

def src2311 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2311 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2311_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2311_1 : CycleData E W := ⟨3,![1,23,22,18,14],![4,8,28,38,27]⟩
def cycle2311_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2311_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2311_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2311_5 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def data2311 : PartitionData E W := ⟨6,![cycle2311_0,cycle2311_1,cycle2311_2,cycle2311_3,cycle2311_4,cycle2311_5]⟩
lemma valid_data2311 : data2311.Valid src2311 dst2311 Finset.univ := by decide +kernel

def src2312 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2312 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2312_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,26,28,14]⟩
def cycle2312_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2312_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2312_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2312_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2312_5 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def data2312 : PartitionData E W := ⟨6,![cycle2312_0,cycle2312_1,cycle2312_2,cycle2312_3,cycle2312_4,cycle2312_5]⟩
lemma valid_data2312 : data2312.Valid src2312 dst2312 Finset.univ := by decide +kernel

def src2313 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2313 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2313_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2313_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2313_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2313_3 : CycleData E W := ⟨3,![3,19,13,6,7],![3,6,27,14,16]⟩
def cycle2313_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2313_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data2313 : PartitionData E W := ⟨6,![cycle2313_0,cycle2313_1,cycle2313_2,cycle2313_3,cycle2313_4,cycle2313_5]⟩
lemma valid_data2313 : data2313.Valid src2313 dst2313 Finset.univ := by decide +kernel

def src2314 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2314 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2314_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2314_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2314_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2314_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2314_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2314_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data2314 : PartitionData E W := ⟨6,![cycle2314_0,cycle2314_1,cycle2314_2,cycle2314_3,cycle2314_4,cycle2314_5]⟩
lemma valid_data2314 : data2314.Valid src2314 dst2314 Finset.univ := by decide +kernel

def src2315 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2315 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2315_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2315_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2315_2 : CycleData E W := ⟨2,![2,23,22,8],![3,8,38,18]⟩
def cycle2315_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2315_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2315_5 : CycleData E W := ⟨2,![6,17,18,13],![14,16,38,27]⟩
def data2315 : PartitionData E W := ⟨6,![cycle2315_0,cycle2315_1,cycle2315_2,cycle2315_3,cycle2315_4,cycle2315_5]⟩
lemma valid_data2315 : data2315.Valid src2315 dst2315 Finset.univ := by decide +kernel

def src2316 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2316 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2316_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2316_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2316_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2316_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2316_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2316_5 : CycleData E W := ⟨2,![6,17,11,12],![14,16,26,28]⟩
def data2316 : PartitionData E W := ⟨6,![cycle2316_0,cycle2316_1,cycle2316_2,cycle2316_3,cycle2316_4,cycle2316_5]⟩
lemma valid_data2316 : data2316.Valid src2316 dst2316 Finset.univ := by decide +kernel

def src2317 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2317 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2317_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2317_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2317_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2317_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2317_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2317_5 : CycleData E W := ⟨3,![6,17,18,22,12],![14,16,26,38,28]⟩
def data2317 : PartitionData E W := ⟨6,![cycle2317_0,cycle2317_1,cycle2317_2,cycle2317_3,cycle2317_4,cycle2317_5]⟩
lemma valid_data2317 : data2317.Valid src2317 dst2317 Finset.univ := by decide +kernel

def src2318 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2318 : E → W := ![4,8,3,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2318_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2318_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2318_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2318_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2318_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2318_5 : CycleData E W := ⟨2,![6,17,11,12],![14,16,26,28]⟩
def data2318 : PartitionData E W := ⟨6,![cycle2318_0,cycle2318_1,cycle2318_2,cycle2318_3,cycle2318_4,cycle2318_5]⟩
lemma valid_data2318 : data2318.Valid src2318 dst2318 Finset.univ := by decide +kernel

def src2319 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2319 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2319_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2319_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2319_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,27,16]⟩
def cycle2319_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2319_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle2319_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2319 : PartitionData E W := ⟨6,![cycle2319_0,cycle2319_1,cycle2319_2,cycle2319_3,cycle2319_4,cycle2319_5]⟩
lemma valid_data2319 : data2319.Valid src2319 dst2319 Finset.univ := by decide +kernel

def src2320 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2320 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2320_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2320_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2320_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2320_3 : CycleData E W := ⟨3,![3,15,12,6,7],![3,6,26,14,16]⟩
def cycle2320_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2320_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data2320 : PartitionData E W := ⟨6,![cycle2320_0,cycle2320_1,cycle2320_2,cycle2320_3,cycle2320_4,cycle2320_5]⟩
lemma valid_data2320 : data2320.Valid src2320 dst2320 Finset.univ := by decide +kernel

def src2321 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2321 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2321_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2321_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2321_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,27,16]⟩
def cycle2321_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2321_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle2321_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2321 : PartitionData E W := ⟨6,![cycle2321_0,cycle2321_1,cycle2321_2,cycle2321_3,cycle2321_4,cycle2321_5]⟩
lemma valid_data2321 : data2321.Valid src2321 dst2321 Finset.univ := by decide +kernel

def src2322 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2322 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2322_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2322_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2322_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2322_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2322_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle2322_5 : CycleData E W := ⟨3,![15,13,22,18,19],![6,26,28,38,27]⟩
def data2322 : PartitionData E W := ⟨6,![cycle2322_0,cycle2322_1,cycle2322_2,cycle2322_3,cycle2322_4,cycle2322_5]⟩
lemma valid_data2322 : data2322.Valid src2322 dst2322 Finset.univ := by decide +kernel

def src2323 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2323 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2323_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2323_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2323_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2323_3 : CycleData E W := ⟨3,![3,15,12,6,7],![3,6,26,14,16]⟩
def cycle2323_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2323_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2323 : PartitionData E W := ⟨6,![cycle2323_0,cycle2323_1,cycle2323_2,cycle2323_3,cycle2323_4,cycle2323_5]⟩
lemma valid_data2323 : data2323.Valid src2323 dst2323 Finset.univ := by decide +kernel

def src2324 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2324 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2324_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2324_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2324_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2324_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2324_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle2324_5 : CycleData E W := ⟨4,![15,13,21,22,18,19],![6,26,28,18,38,27]⟩
def data2324 : PartitionData E W := ⟨6,![cycle2324_0,cycle2324_1,cycle2324_2,cycle2324_3,cycle2324_4,cycle2324_5]⟩
lemma valid_data2324 : data2324.Valid src2324 dst2324 Finset.univ := by decide +kernel

def src2325 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2325 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2325_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2325_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2325_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2325_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2325_4 : CycleData E W := ⟨3,![15,12,6,18,19],![6,26,14,16,27]⟩
def cycle2325_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2325 : PartitionData E W := ⟨6,![cycle2325_0,cycle2325_1,cycle2325_2,cycle2325_3,cycle2325_4,cycle2325_5]⟩
lemma valid_data2325 : data2325.Valid src2325 dst2325 Finset.univ := by decide +kernel

def src2326 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2326 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2326_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2326_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2326_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2326_3 : CycleData E W := ⟨3,![3,15,12,6,7],![3,6,26,14,16]⟩
def cycle2326_4 : CycleData E W := ⟨4,![4,19,18,17,21,9],![2,6,27,16,38,18]⟩
def cycle2326_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2326 : PartitionData E W := ⟨6,![cycle2326_0,cycle2326_1,cycle2326_2,cycle2326_3,cycle2326_4,cycle2326_5]⟩
lemma valid_data2326 : data2326.Valid src2326 dst2326 Finset.univ := by decide +kernel

def src2327 : E → W := ![2,4,8,3,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2327 : E → W := ![4,8,3,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2327_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2327_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2327_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2327_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2327_4 : CycleData E W := ⟨3,![15,12,6,18,19],![6,26,14,16,27]⟩
def cycle2327_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2327 : PartitionData E W := ⟨6,![cycle2327_0,cycle2327_1,cycle2327_2,cycle2327_3,cycle2327_4,cycle2327_5]⟩
lemma valid_data2327 : data2327.Valid src2327 dst2327 Finset.univ := by decide +kernel

def src2328 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst2328 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2328_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2328_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2328_2 : CycleData E W := ⟨3,![2,23,16,11,7],![3,8,38,26,14]⟩
def cycle2328_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2328_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2328_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2328 : PartitionData E W := ⟨6,![cycle2328_0,cycle2328_1,cycle2328_2,cycle2328_3,cycle2328_4,cycle2328_5]⟩
lemma valid_data2328 : data2328.Valid src2328 dst2328 Finset.univ := by decide +kernel

def src2329 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst2329 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2329_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2329_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2329_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2329_3 : CycleData E W := ⟨2,![8,21,16,11],![14,18,38,26]⟩
def cycle2329_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2329_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2329 : PartitionData E W := ⟨6,![cycle2329_0,cycle2329_1,cycle2329_2,cycle2329_3,cycle2329_4,cycle2329_5]⟩
lemma valid_data2329 : data2329.Valid src2329 dst2329 Finset.univ := by decide +kernel

def src2330 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst2330 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2330_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2330_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2330_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2330_3 : CycleData E W := ⟨3,![5,18,13,21,9],![2,16,27,28,18]⟩
def cycle2330_4 : CycleData E W := ⟨2,![8,22,16,11],![14,18,38,26]⟩
def cycle2330_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2330 : PartitionData E W := ⟨6,![cycle2330_0,cycle2330_1,cycle2330_2,cycle2330_3,cycle2330_4,cycle2330_5]⟩
lemma valid_data2330 : data2330.Valid src2330 dst2330 Finset.univ := by decide +kernel

def src2331 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst2331 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2331_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2331_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2331_2 : CycleData E W := ⟨3,![2,23,18,11,7],![3,8,38,26,14]⟩
def cycle2331_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2331_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2331_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2331 : PartitionData E W := ⟨6,![cycle2331_0,cycle2331_1,cycle2331_2,cycle2331_3,cycle2331_4,cycle2331_5]⟩
lemma valid_data2331 : data2331.Valid src2331 dst2331 Finset.univ := by decide +kernel

def src2332 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst2332 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2332_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2332_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2332_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2332_3 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,26]⟩
def cycle2332_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2332_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2332 : PartitionData E W := ⟨6,![cycle2332_0,cycle2332_1,cycle2332_2,cycle2332_3,cycle2332_4,cycle2332_5]⟩
lemma valid_data2332 : data2332.Valid src2332 dst2332 Finset.univ := by decide +kernel

def src2333 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst2333 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2333_0 : CycleData E W := ⟨3,![0,10,7,6,5],![2,4,14,3,16]⟩
def cycle2333_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2333_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2333_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle2333_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,26]⟩
def cycle2333_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data2333 : PartitionData E W := ⟨6,![cycle2333_0,cycle2333_1,cycle2333_2,cycle2333_3,cycle2333_4,cycle2333_5]⟩
lemma valid_data2333 : data2333.Valid src2333 dst2333 Finset.univ := by decide +kernel

def src2334 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst2334 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2334_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,27,16]⟩
def cycle2334_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2334_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2334_3 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2334_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle2334_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2334 : PartitionData E W := ⟨6,![cycle2334_0,cycle2334_1,cycle2334_2,cycle2334_3,cycle2334_4,cycle2334_5]⟩
lemma valid_data2334 : data2334.Valid src2334 dst2334 Finset.univ := by decide +kernel

def src2335 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst2335 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2335_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,27,16]⟩
def cycle2335_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2335_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2335_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2335_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,26,28]⟩
def cycle2335_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2335 : PartitionData E W := ⟨6,![cycle2335_0,cycle2335_1,cycle2335_2,cycle2335_3,cycle2335_4,cycle2335_5]⟩
lemma valid_data2335 : data2335.Valid src2335 dst2335 Finset.univ := by decide +kernel

def src2336 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst2336 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2336_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,27,16]⟩
def cycle2336_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2336_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2336_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2336_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle2336_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2336 : PartitionData E W := ⟨6,![cycle2336_0,cycle2336_1,cycle2336_2,cycle2336_3,cycle2336_4,cycle2336_5]⟩
lemma valid_data2336 : data2336.Valid src2336 dst2336 Finset.univ := by decide +kernel

def src2337 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst2337 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle2337_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2337_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2337_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2337_3 : CycleData E W := ⟨3,![5,17,23,20,9],![2,16,38,8,18]⟩
def cycle2337_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle2337_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2337 : PartitionData E W := ⟨6,![cycle2337_0,cycle2337_1,cycle2337_2,cycle2337_3,cycle2337_4,cycle2337_5]⟩
lemma valid_data2337 : data2337.Valid src2337 dst2337 Finset.univ := by decide +kernel

def src2338 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst2338 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle2338_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2338_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2338_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2338_3 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2338_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,26,28]⟩
def cycle2338_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2338 : PartitionData E W := ⟨6,![cycle2338_0,cycle2338_1,cycle2338_2,cycle2338_3,cycle2338_4,cycle2338_5]⟩
lemma valid_data2338 : data2338.Valid src2338 dst2338 Finset.univ := by decide +kernel

def src2339 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst2339 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle2339_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2339_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2339_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2339_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2339_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle2339_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2339 : PartitionData E W := ⟨6,![cycle2339_0,cycle2339_1,cycle2339_2,cycle2339_3,cycle2339_4,cycle2339_5]⟩
lemma valid_data2339 : data2339.Valid src2339 dst2339 Finset.univ := by decide +kernel

def src2340 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst2340 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2340_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2340_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,27]⟩
def cycle2340_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2340_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2340_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2340_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2340 : PartitionData E W := ⟨6,![cycle2340_0,cycle2340_1,cycle2340_2,cycle2340_3,cycle2340_4,cycle2340_5]⟩
lemma valid_data2340 : data2340.Valid src2340 dst2340 Finset.univ := by decide +kernel

def src2341 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst2341 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2341_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2341_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2341_2 : CycleData E W := ⟨3,![2,20,21,17,6],![3,8,18,38,16]⟩
def cycle2341_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2341_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2341_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2341 : PartitionData E W := ⟨6,![cycle2341_0,cycle2341_1,cycle2341_2,cycle2341_3,cycle2341_4,cycle2341_5]⟩
lemma valid_data2341 : data2341.Valid src2341 dst2341 Finset.univ := by decide +kernel

def src2342 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst2342 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2342_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2342_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2342_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2342_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2342_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2342_5 : CycleData E W := ⟨2,![21,12,16,22],![18,28,26,38]⟩
def data2342 : PartitionData E W := ⟨6,![cycle2342_0,cycle2342_1,cycle2342_2,cycle2342_3,cycle2342_4,cycle2342_5]⟩
lemma valid_data2342 : data2342.Valid src2342 dst2342 Finset.univ := by decide +kernel

def src2343 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst2343 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2343_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2343_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,27]⟩
def cycle2343_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2343_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle2343_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2343_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2343 : PartitionData E W := ⟨6,![cycle2343_0,cycle2343_1,cycle2343_2,cycle2343_3,cycle2343_4,cycle2343_5]⟩
lemma valid_data2343 : data2343.Valid src2343 dst2343 Finset.univ := by decide +kernel

def src2344 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst2344 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2344_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2344_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2344_2 : CycleData E W := ⟨3,![2,20,21,19,3],![3,8,18,38,6]⟩
def cycle2344_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle2344_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2344_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2344 : PartitionData E W := ⟨6,![cycle2344_0,cycle2344_1,cycle2344_2,cycle2344_3,cycle2344_4,cycle2344_5]⟩
lemma valid_data2344 : data2344.Valid src2344 dst2344 Finset.univ := by decide +kernel

def src2345 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst2345 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2345_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2345_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2345_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2345_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle2345_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2345_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,26,38]⟩
def data2345 : PartitionData E W := ⟨6,![cycle2345_0,cycle2345_1,cycle2345_2,cycle2345_3,cycle2345_4,cycle2345_5]⟩
lemma valid_data2345 : data2345.Valid src2345 dst2345 Finset.univ := by decide +kernel

def src2346 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst2346 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2346_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2346_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2346_2 : CycleData E W := ⟨3,![2,23,18,11,7],![3,8,38,27,14]⟩
def cycle2346_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2346_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2346_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2346 : PartitionData E W := ⟨6,![cycle2346_0,cycle2346_1,cycle2346_2,cycle2346_3,cycle2346_4,cycle2346_5]⟩
lemma valid_data2346 : data2346.Valid src2346 dst2346 Finset.univ := by decide +kernel

def src2347 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst2347 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2347_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2347_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2347_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2347_3 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle2347_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2347_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2347 : PartitionData E W := ⟨6,![cycle2347_0,cycle2347_1,cycle2347_2,cycle2347_3,cycle2347_4,cycle2347_5]⟩
lemma valid_data2347 : data2347.Valid src2347 dst2347 Finset.univ := by decide +kernel

def src2348 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2348 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2348_0 : CycleData E W := ⟨3,![0,10,7,6,5],![2,4,14,3,16]⟩
def cycle2348_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2348_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2348_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle2348_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def cycle2348_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data2348 : PartitionData E W := ⟨6,![cycle2348_0,cycle2348_1,cycle2348_2,cycle2348_3,cycle2348_4,cycle2348_5]⟩
lemma valid_data2348 : data2348.Valid src2348 dst2348 Finset.univ := by decide +kernel

def src2349 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2349 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2349_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2349_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2349_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2349_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2349_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2349_5 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data2349 : PartitionData E W := ⟨6,![cycle2349_0,cycle2349_1,cycle2349_2,cycle2349_3,cycle2349_4,cycle2349_5]⟩
lemma valid_data2349 : data2349.Valid src2349 dst2349 Finset.univ := by decide +kernel

def src2350 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2350 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2350_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2350_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2350_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2350_3 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle2350_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2350_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2350 : PartitionData E W := ⟨6,![cycle2350_0,cycle2350_1,cycle2350_2,cycle2350_3,cycle2350_4,cycle2350_5]⟩
lemma valid_data2350 : data2350.Valid src2350 dst2350 Finset.univ := by decide +kernel

def src2351 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2351 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2351_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2351_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2351_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2351_3 : CycleData E W := ⟨3,![5,16,13,21,9],![2,16,26,28,18]⟩
def cycle2351_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def cycle2351_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2351 : PartitionData E W := ⟨6,![cycle2351_0,cycle2351_1,cycle2351_2,cycle2351_3,cycle2351_4,cycle2351_5]⟩
lemma valid_data2351 : data2351.Valid src2351 dst2351 Finset.univ := by decide +kernel

def src2352 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst2352 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle2352_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2352_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,26]⟩
def cycle2352_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2352_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2352_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle2352_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2352 : PartitionData E W := ⟨6,![cycle2352_0,cycle2352_1,cycle2352_2,cycle2352_3,cycle2352_4,cycle2352_5]⟩
lemma valid_data2352 : data2352.Valid src2352 dst2352 Finset.univ := by decide +kernel

def src2353 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst2353 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle2353_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2353_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,26]⟩
def cycle2353_2 : CycleData E W := ⟨3,![2,20,21,19,3],![3,8,18,38,6]⟩
def cycle2353_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2353_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle2353_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2353 : PartitionData E W := ⟨6,![cycle2353_0,cycle2353_1,cycle2353_2,cycle2353_3,cycle2353_4,cycle2353_5]⟩
lemma valid_data2353 : data2353.Valid src2353 dst2353 Finset.univ := by decide +kernel

def src2354 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst2354 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle2354_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2354_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,26]⟩
def cycle2354_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2354_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2354_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle2354_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data2354 : PartitionData E W := ⟨6,![cycle2354_0,cycle2354_1,cycle2354_2,cycle2354_3,cycle2354_4,cycle2354_5]⟩
lemma valid_data2354 : data2354.Valid src2354 dst2354 Finset.univ := by decide +kernel

def src2355 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst2355 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle2355_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2355_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,26]⟩
def cycle2355_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2355_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2355_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2355_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2355 : PartitionData E W := ⟨6,![cycle2355_0,cycle2355_1,cycle2355_2,cycle2355_3,cycle2355_4,cycle2355_5]⟩
lemma valid_data2355 : data2355.Valid src2355 dst2355 Finset.univ := by decide +kernel

def src2356 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst2356 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle2356_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2356_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,26]⟩
def cycle2356_2 : CycleData E W := ⟨3,![2,20,21,17,6],![3,8,18,38,16]⟩
def cycle2356_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2356_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2356_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2356 : PartitionData E W := ⟨6,![cycle2356_0,cycle2356_1,cycle2356_2,cycle2356_3,cycle2356_4,cycle2356_5]⟩
lemma valid_data2356 : data2356.Valid src2356 dst2356 Finset.univ := by decide +kernel

def src2357 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst2357 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle2357_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2357_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,26]⟩
def cycle2357_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2357_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2357_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2357_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data2357 : PartitionData E W := ⟨6,![cycle2357_0,cycle2357_1,cycle2357_2,cycle2357_3,cycle2357_4,cycle2357_5]⟩
lemma valid_data2357 : data2357.Valid src2357 dst2357 Finset.univ := by decide +kernel

def src2358 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst2358 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle2358_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle2358_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2358_2 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2358_3 : CycleData E W := ⟨3,![5,17,23,20,9],![2,16,38,8,18]⟩
def cycle2358_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle2358_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2358 : PartitionData E W := ⟨6,![cycle2358_0,cycle2358_1,cycle2358_2,cycle2358_3,cycle2358_4,cycle2358_5]⟩
lemma valid_data2358 : data2358.Valid src2358 dst2358 Finset.univ := by decide +kernel

def src2359 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst2359 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle2359_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle2359_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2359_2 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2359_3 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2359_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,27,28]⟩
def cycle2359_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2359 : PartitionData E W := ⟨6,![cycle2359_0,cycle2359_1,cycle2359_2,cycle2359_3,cycle2359_4,cycle2359_5]⟩
lemma valid_data2359 : data2359.Valid src2359 dst2359 Finset.univ := by decide +kernel

def src2360 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst2360 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle2360_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle2360_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2360_2 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2360_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2360_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle2360_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data2360 : PartitionData E W := ⟨6,![cycle2360_0,cycle2360_1,cycle2360_2,cycle2360_3,cycle2360_4,cycle2360_5]⟩
lemma valid_data2360 : data2360.Valid src2360 dst2360 Finset.univ := by decide +kernel

def src2361 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst2361 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle2361_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,26,16]⟩
def cycle2361_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2361_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2361_3 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2361_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle2361_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2361 : PartitionData E W := ⟨6,![cycle2361_0,cycle2361_1,cycle2361_2,cycle2361_3,cycle2361_4,cycle2361_5]⟩
lemma valid_data2361 : data2361.Valid src2361 dst2361 Finset.univ := by decide +kernel

def src2362 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst2362 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle2362_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,26,16]⟩
def cycle2362_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2362_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2362_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2362_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,27,28]⟩
def cycle2362_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2362 : PartitionData E W := ⟨6,![cycle2362_0,cycle2362_1,cycle2362_2,cycle2362_3,cycle2362_4,cycle2362_5]⟩
lemma valid_data2362 : data2362.Valid src2362 dst2362 Finset.univ := by decide +kernel

def src2363 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst2363 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle2363_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,26,16]⟩
def cycle2363_1 : CycleData E W := ⟨2,![2,1,10,7],![3,8,4,14]⟩
def cycle2363_2 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2363_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2363_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle2363_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data2363 : PartitionData E W := ⟨6,![cycle2363_0,cycle2363_1,cycle2363_2,cycle2363_3,cycle2363_4,cycle2363_5]⟩
lemma valid_data2363 : data2363.Valid src2363 dst2363 Finset.univ := by decide +kernel

def src2364 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst2364 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle2364_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2364_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2364_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2364_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2364_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle2364_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2364 : PartitionData E W := ⟨6,![cycle2364_0,cycle2364_1,cycle2364_2,cycle2364_3,cycle2364_4,cycle2364_5]⟩
lemma valid_data2364 : data2364.Valid src2364 dst2364 Finset.univ := by decide +kernel

def src2365 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst2365 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle2365_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2365_1 : CycleData E W := ⟨3,![1,20,21,18,14],![4,8,18,38,27]⟩
def cycle2365_2 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle2365_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2365_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle2365_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2365 : PartitionData E W := ⟨6,![cycle2365_0,cycle2365_1,cycle2365_2,cycle2365_3,cycle2365_4,cycle2365_5]⟩
lemma valid_data2365 : data2365.Valid src2365 dst2365 Finset.univ := by decide +kernel

def src2366 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst2366 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle2366_0 : CycleData E W := ⟨3,![0,10,7,6,5],![2,4,14,3,16]⟩
def cycle2366_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2366_2 : CycleData E W := ⟨3,![2,20,12,15,3],![3,8,28,26,6]⟩
def cycle2366_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2366_4 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2366_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2366 : PartitionData E W := ⟨6,![cycle2366_0,cycle2366_1,cycle2366_2,cycle2366_3,cycle2366_4,cycle2366_5]⟩
lemma valid_data2366 : data2366.Valid src2366 dst2366 Finset.univ := by decide +kernel

def src2367 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst2367 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle2367_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2367_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2367_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2367_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2367_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle2367_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2367 : PartitionData E W := ⟨6,![cycle2367_0,cycle2367_1,cycle2367_2,cycle2367_3,cycle2367_4,cycle2367_5]⟩
lemma valid_data2367 : data2367.Valid src2367 dst2367 Finset.univ := by decide +kernel

def src2368 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst2368 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle2368_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2368_1 : CycleData E W := ⟨3,![1,20,21,18,14],![4,8,18,38,27]⟩
def cycle2368_2 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle2368_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2368_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle2368_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2368 : PartitionData E W := ⟨6,![cycle2368_0,cycle2368_1,cycle2368_2,cycle2368_3,cycle2368_4,cycle2368_5]⟩
lemma valid_data2368 : data2368.Valid src2368 dst2368 Finset.univ := by decide +kernel

def src2369 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst2369 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle2369_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2369_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2369_2 : CycleData E W := ⟨3,![2,20,12,16,6],![3,8,28,26,16]⟩
def cycle2369_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2369_4 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2369_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2369 : PartitionData E W := ⟨6,![cycle2369_0,cycle2369_1,cycle2369_2,cycle2369_3,cycle2369_4,cycle2369_5]⟩
lemma valid_data2369 : data2369.Valid src2369 dst2369 Finset.univ := by decide +kernel

def src2370 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst2370 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle2370_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2370_1 : CycleData E W := ⟨2,![1,23,16,14],![4,8,38,26]⟩
def cycle2370_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2370_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2370_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle2370_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2370 : PartitionData E W := ⟨6,![cycle2370_0,cycle2370_1,cycle2370_2,cycle2370_3,cycle2370_4,cycle2370_5]⟩
lemma valid_data2370 : data2370.Valid src2370 dst2370 Finset.univ := by decide +kernel

def src2371 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst2371 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle2371_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2371_1 : CycleData E W := ⟨3,![1,20,21,16,14],![4,8,18,38,26]⟩
def cycle2371_2 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle2371_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2371_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle2371_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2371 : PartitionData E W := ⟨6,![cycle2371_0,cycle2371_1,cycle2371_2,cycle2371_3,cycle2371_4,cycle2371_5]⟩
lemma valid_data2371 : data2371.Valid src2371 dst2371 Finset.univ := by decide +kernel

def src2372 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst2372 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle2372_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2372_1 : CycleData E W := ⟨2,![1,23,16,14],![4,8,38,26]⟩
def cycle2372_2 : CycleData E W := ⟨3,![2,20,12,18,6],![3,8,28,27,16]⟩
def cycle2372_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2372_4 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2372_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2372 : PartitionData E W := ⟨6,![cycle2372_0,cycle2372_1,cycle2372_2,cycle2372_3,cycle2372_4,cycle2372_5]⟩
lemma valid_data2372 : data2372.Valid src2372 dst2372 Finset.univ := by decide +kernel

def src2373 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst2373 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle2373_0 : CycleData E W := ⟨3,![0,10,7,3,4],![2,4,14,3,6]⟩
def cycle2373_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,26]⟩
def cycle2373_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2373_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2373_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle2373_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2373 : PartitionData E W := ⟨6,![cycle2373_0,cycle2373_1,cycle2373_2,cycle2373_3,cycle2373_4,cycle2373_5]⟩
lemma valid_data2373 : data2373.Valid src2373 dst2373 Finset.univ := by decide +kernel

def src2374 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst2374 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle2374_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle2374_1 : CycleData E W := ⟨3,![1,20,21,18,14],![4,8,18,38,26]⟩
def cycle2374_2 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle2374_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,16]⟩
def cycle2374_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle2374_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2374 : PartitionData E W := ⟨6,![cycle2374_0,cycle2374_1,cycle2374_2,cycle2374_3,cycle2374_4,cycle2374_5]⟩
lemma valid_data2374 : data2374.Valid src2374 dst2374 Finset.univ := by decide +kernel

def src2375 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst2375 : E → W := ![4,8,3,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle2375_0 : CycleData E W := ⟨3,![0,10,7,6,5],![2,4,14,3,16]⟩
def cycle2375_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,26]⟩
def cycle2375_2 : CycleData E W := ⟨3,![2,20,12,15,3],![3,8,28,27,6]⟩
def cycle2375_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2375_4 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle2375_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2375 : PartitionData E W := ⟨6,![cycle2375_0,cycle2375_1,cycle2375_2,cycle2375_3,cycle2375_4,cycle2375_5]⟩
lemma valid_data2375 : data2375.Valid src2375 dst2375 Finset.univ := by decide +kernel

def src2376 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst2376 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle2376_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2376_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2376_2 : CycleData E W := ⟨3,![2,23,17,16,6],![3,8,38,26,16]⟩
def cycle2376_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2376_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2376_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2376 : PartitionData E W := ⟨6,![cycle2376_0,cycle2376_1,cycle2376_2,cycle2376_3,cycle2376_4,cycle2376_5]⟩
lemma valid_data2376 : data2376.Valid src2376 dst2376 Finset.univ := by decide +kernel

def src2377 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst2377 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle2377_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2377_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2377_2 : CycleData E W := ⟨4,![2,20,21,17,16,6],![3,8,18,38,26,16]⟩
def cycle2377_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2377_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2377_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2377 : PartitionData E W := ⟨6,![cycle2377_0,cycle2377_1,cycle2377_2,cycle2377_3,cycle2377_4,cycle2377_5]⟩
lemma valid_data2377 : data2377.Valid src2377 dst2377 Finset.univ := by decide +kernel

def src2378 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst2378 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle2378_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2378_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2378_2 : CycleData E W := ⟨3,![2,23,17,16,6],![3,8,38,26,16]⟩
def cycle2378_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2378_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2378_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2378 : PartitionData E W := ⟨6,![cycle2378_0,cycle2378_1,cycle2378_2,cycle2378_3,cycle2378_4,cycle2378_5]⟩
lemma valid_data2378 : data2378.Valid src2378 dst2378 Finset.univ := by decide +kernel

def src2379 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst2379 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle2379_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2379_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2379_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2379_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2379_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2379_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2379 : PartitionData E W := ⟨6,![cycle2379_0,cycle2379_1,cycle2379_2,cycle2379_3,cycle2379_4,cycle2379_5]⟩
lemma valid_data2379 : data2379.Valid src2379 dst2379 Finset.univ := by decide +kernel

def src2380 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst2380 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle2380_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2380_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2380_2 : CycleData E W := ⟨3,![2,20,21,19,3],![3,8,18,38,6]⟩
def cycle2380_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2380_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2380_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2380 : PartitionData E W := ⟨6,![cycle2380_0,cycle2380_1,cycle2380_2,cycle2380_3,cycle2380_4,cycle2380_5]⟩
lemma valid_data2380 : data2380.Valid src2380 dst2380 Finset.univ := by decide +kernel

def src2381 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst2381 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle2381_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2381_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2381_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2381_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2381_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2381_5 : CycleData E W := ⟨3,![21,13,17,18,22],![18,28,27,26,38]⟩
def data2381 : PartitionData E W := ⟨6,![cycle2381_0,cycle2381_1,cycle2381_2,cycle2381_3,cycle2381_4,cycle2381_5]⟩
lemma valid_data2381 : data2381.Valid src2381 dst2381 Finset.univ := by decide +kernel

def src2382 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst2382 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle2382_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2382_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2382_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2382_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2382_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2382_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2382 : PartitionData E W := ⟨6,![cycle2382_0,cycle2382_1,cycle2382_2,cycle2382_3,cycle2382_4,cycle2382_5]⟩
lemma valid_data2382 : data2382.Valid src2382 dst2382 Finset.univ := by decide +kernel

def src2383 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst2383 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle2383_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2383_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2383_2 : CycleData E W := ⟨4,![2,20,21,18,19,3],![3,8,18,38,26,6]⟩
def cycle2383_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2383_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2383_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2383 : PartitionData E W := ⟨6,![cycle2383_0,cycle2383_1,cycle2383_2,cycle2383_3,cycle2383_4,cycle2383_5]⟩
lemma valid_data2383 : data2383.Valid src2383 dst2383 Finset.univ := by decide +kernel

def src2384 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst2384 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle2384_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2384_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2384_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2384_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2384_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle2384_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data2384 : PartitionData E W := ⟨6,![cycle2384_0,cycle2384_1,cycle2384_2,cycle2384_3,cycle2384_4,cycle2384_5]⟩
lemma valid_data2384 : data2384.Valid src2384 dst2384 Finset.univ := by decide +kernel

def src2385 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst2385 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle2385_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2385_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2385_2 : CycleData E W := ⟨2,![2,23,16,6],![3,8,38,16]⟩
def cycle2385_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2385_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2385_5 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2385 : PartitionData E W := ⟨6,![cycle2385_0,cycle2385_1,cycle2385_2,cycle2385_3,cycle2385_4,cycle2385_5]⟩
lemma valid_data2385 : data2385.Valid src2385 dst2385 Finset.univ := by decide +kernel

def src2386 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst2386 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle2386_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2386_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2386_2 : CycleData E W := ⟨3,![2,20,21,16,6],![3,8,18,38,16]⟩
def cycle2386_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2386_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2386_5 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2386 : PartitionData E W := ⟨6,![cycle2386_0,cycle2386_1,cycle2386_2,cycle2386_3,cycle2386_4,cycle2386_5]⟩
lemma valid_data2386 : data2386.Valid src2386 dst2386 Finset.univ := by decide +kernel

def src2387 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst2387 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle2387_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2387_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2387_2 : CycleData E W := ⟨2,![2,23,16,6],![3,8,38,16]⟩
def cycle2387_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2387_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2387_5 : CycleData E W := ⟨3,![21,13,18,17,22],![18,28,27,26,38]⟩
def data2387 : PartitionData E W := ⟨6,![cycle2387_0,cycle2387_1,cycle2387_2,cycle2387_3,cycle2387_4,cycle2387_5]⟩
lemma valid_data2387 : data2387.Valid src2387 dst2387 Finset.univ := by decide +kernel

def src2388 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2388 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2388_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2388_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2388_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2388_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2388_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2388_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2388 : PartitionData E W := ⟨6,![cycle2388_0,cycle2388_1,cycle2388_2,cycle2388_3,cycle2388_4,cycle2388_5]⟩
lemma valid_data2388 : data2388.Valid src2388 dst2388 Finset.univ := by decide +kernel

def src2389 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2389 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2389_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2389_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2389_2 : CycleData E W := ⟨3,![2,20,21,17,6],![3,8,18,38,16]⟩
def cycle2389_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2389_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2389_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2389 : PartitionData E W := ⟨6,![cycle2389_0,cycle2389_1,cycle2389_2,cycle2389_3,cycle2389_4,cycle2389_5]⟩
lemma valid_data2389 : data2389.Valid src2389 dst2389 Finset.univ := by decide +kernel

def src2390 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2390 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2390_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle2390_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2390_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2390_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2390_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2390_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2390 : PartitionData E W := ⟨6,![cycle2390_0,cycle2390_1,cycle2390_2,cycle2390_3,cycle2390_4,cycle2390_5]⟩
lemma valid_data2390 : data2390.Valid src2390 dst2390 Finset.univ := by decide +kernel

def src2391 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2391 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2391_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2391_1 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2391_2 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2391_3 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2391_4 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def cycle2391_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data2391 : PartitionData E W := ⟨6,![cycle2391_0,cycle2391_1,cycle2391_2,cycle2391_3,cycle2391_4,cycle2391_5]⟩
lemma valid_data2391 : data2391.Valid src2391 dst2391 Finset.univ := by decide +kernel

def src2392 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2392 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2392_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2392_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2392_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2392_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2392_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2392_5 : CycleData E W := ⟨3,![11,16,22,13,12],![14,26,38,28,27]⟩
def data2392 : PartitionData E W := ⟨6,![cycle2392_0,cycle2392_1,cycle2392_2,cycle2392_3,cycle2392_4,cycle2392_5]⟩
lemma valid_data2392 : data2392.Valid src2392 dst2392 Finset.univ := by decide +kernel

def src2393 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2393 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2393_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2393_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2393_2 : CycleData E W := ⟨3,![2,23,16,11,7],![3,8,38,26,14]⟩
def cycle2393_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2393_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2393_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data2393 : PartitionData E W := ⟨6,![cycle2393_0,cycle2393_1,cycle2393_2,cycle2393_3,cycle2393_4,cycle2393_5]⟩
lemma valid_data2393 : data2393.Valid src2393 dst2393 Finset.univ := by decide +kernel

def src2394 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2394 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2394_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2394_1 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2394_2 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle2394_3 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2394_4 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def cycle2394_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data2394 : PartitionData E W := ⟨6,![cycle2394_0,cycle2394_1,cycle2394_2,cycle2394_3,cycle2394_4,cycle2394_5]⟩
lemma valid_data2394 : data2394.Valid src2394 dst2394 Finset.univ := by decide +kernel

def src2395 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2395 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2395_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,26,16]⟩
def cycle2395_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2395_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2395_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2395_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2395_5 : CycleData E W := ⟨3,![11,18,22,13,12],![14,26,38,28,27]⟩
def data2395 : PartitionData E W := ⟨6,![cycle2395_0,cycle2395_1,cycle2395_2,cycle2395_3,cycle2395_4,cycle2395_5]⟩
lemma valid_data2395 : data2395.Valid src2395 dst2395 Finset.univ := by decide +kernel

def src2396 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2396 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2396_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,26,16]⟩
def cycle2396_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2396_2 : CycleData E W := ⟨3,![2,23,18,11,7],![3,8,38,26,14]⟩
def cycle2396_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2396_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2396_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data2396 : PartitionData E W := ⟨6,![cycle2396_0,cycle2396_1,cycle2396_2,cycle2396_3,cycle2396_4,cycle2396_5]⟩
lemma valid_data2396 : data2396.Valid src2396 dst2396 Finset.univ := by decide +kernel

def src2397 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst2397 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle2397_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,26,16]⟩
def cycle2397_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2397_2 : CycleData E W := ⟨2,![2,23,18,6],![3,8,38,16]⟩
def cycle2397_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,14,18]⟩
def cycle2397_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2397_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2397 : PartitionData E W := ⟨6,![cycle2397_0,cycle2397_1,cycle2397_2,cycle2397_3,cycle2397_4,cycle2397_5]⟩
lemma valid_data2397 : data2397.Valid src2397 dst2397 Finset.univ := by decide +kernel

def src2398 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst2398 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle2398_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,26,16]⟩
def cycle2398_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2398_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2398_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,38,16]⟩
def cycle2398_4 : CycleData E W := ⟨4,![4,15,13,22,21,9],![2,6,27,28,38,18]⟩
def cycle2398_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data2398 : PartitionData E W := ⟨6,![cycle2398_0,cycle2398_1,cycle2398_2,cycle2398_3,cycle2398_4,cycle2398_5]⟩
lemma valid_data2398 : data2398.Valid src2398 dst2398 Finset.univ := by decide +kernel

def src2399 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst2399 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle2399_0 : CycleData E W := ⟨3,![0,10,16,15,4],![2,4,26,27,6]⟩
def cycle2399_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2399_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2399_3 : CycleData E W := ⟨2,![5,18,22,9],![2,16,38,18]⟩
def cycle2399_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2399_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data2399 : PartitionData E W := ⟨6,![cycle2399_0,cycle2399_1,cycle2399_2,cycle2399_3,cycle2399_4,cycle2399_5]⟩
lemma valid_data2399 : data2399.Valid src2399 dst2399 Finset.univ := by decide +kernel

def lookupB11 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data2200 else (if j < 2 then data2201 else data2202)) else (if j < 4 then data2203 else (if j < 5 then data2204 else data2205))) else (if j < 9 then (if j < 7 then data2206 else (if j < 8 then data2207 else data2208)) else (if j < 10 then data2209 else (if j < 11 then data2210 else data2211)))) else (if j < 18 then (if j < 15 then (if j < 13 then data2212 else (if j < 14 then data2213 else data2214)) else (if j < 16 then data2215 else (if j < 17 then data2216 else data2217))) else (if j < 21 then (if j < 19 then data2218 else (if j < 20 then data2219 else data2220)) else (if j < 23 then (if j < 22 then data2221 else data2222) else (if j < 24 then data2223 else data2224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data2225 else (if j < 27 then data2226 else data2227)) else (if j < 29 then data2228 else (if j < 30 then data2229 else data2230))) else (if j < 34 then (if j < 32 then data2231 else (if j < 33 then data2232 else data2233)) else (if j < 35 then data2234 else (if j < 36 then data2235 else data2236)))) else (if j < 43 then (if j < 40 then (if j < 38 then data2237 else (if j < 39 then data2238 else data2239)) else (if j < 41 then data2240 else (if j < 42 then data2241 else data2242))) else (if j < 46 then (if j < 44 then data2243 else (if j < 45 then data2244 else data2245)) else (if j < 48 then (if j < 47 then data2246 else data2247) else (if j < 49 then data2248 else data2249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data2250 else (if j < 52 then data2251 else data2252)) else (if j < 54 then data2253 else (if j < 55 then data2254 else data2255))) else (if j < 59 then (if j < 57 then data2256 else (if j < 58 then data2257 else data2258)) else (if j < 60 then data2259 else (if j < 61 then data2260 else data2261)))) else (if j < 68 then (if j < 65 then (if j < 63 then data2262 else (if j < 64 then data2263 else data2264)) else (if j < 66 then data2265 else (if j < 67 then data2266 else data2267))) else (if j < 71 then (if j < 69 then data2268 else (if j < 70 then data2269 else data2270)) else (if j < 73 then (if j < 72 then data2271 else data2272) else (if j < 74 then data2273 else data2274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data2275 else (if j < 77 then data2276 else data2277)) else (if j < 79 then data2278 else (if j < 80 then data2279 else data2280))) else (if j < 84 then (if j < 82 then data2281 else (if j < 83 then data2282 else data2283)) else (if j < 85 then data2284 else (if j < 86 then data2285 else data2286)))) else (if j < 93 then (if j < 90 then (if j < 88 then data2287 else (if j < 89 then data2288 else data2289)) else (if j < 91 then data2290 else (if j < 92 then data2291 else data2292))) else (if j < 96 then (if j < 94 then data2293 else (if j < 95 then data2294 else data2295)) else (if j < 98 then (if j < 97 then data2296 else data2297) else (if j < 99 then data2298 else data2299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data2300 else (if j < 102 then data2301 else data2302)) else (if j < 104 then data2303 else (if j < 105 then data2304 else data2305))) else (if j < 109 then (if j < 107 then data2306 else (if j < 108 then data2307 else data2308)) else (if j < 110 then data2309 else (if j < 111 then data2310 else data2311)))) else (if j < 118 then (if j < 115 then (if j < 113 then data2312 else (if j < 114 then data2313 else data2314)) else (if j < 116 then data2315 else (if j < 117 then data2316 else data2317))) else (if j < 121 then (if j < 119 then data2318 else (if j < 120 then data2319 else data2320)) else (if j < 123 then (if j < 122 then data2321 else data2322) else (if j < 124 then data2323 else data2324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data2325 else (if j < 127 then data2326 else data2327)) else (if j < 129 then data2328 else (if j < 130 then data2329 else data2330))) else (if j < 134 then (if j < 132 then data2331 else (if j < 133 then data2332 else data2333)) else (if j < 135 then data2334 else (if j < 136 then data2335 else data2336)))) else (if j < 143 then (if j < 140 then (if j < 138 then data2337 else (if j < 139 then data2338 else data2339)) else (if j < 141 then data2340 else (if j < 142 then data2341 else data2342))) else (if j < 146 then (if j < 144 then data2343 else (if j < 145 then data2344 else data2345)) else (if j < 148 then (if j < 147 then data2346 else data2347) else (if j < 149 then data2348 else data2349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data2350 else (if j < 152 then data2351 else data2352)) else (if j < 154 then data2353 else (if j < 155 then data2354 else data2355))) else (if j < 159 then (if j < 157 then data2356 else (if j < 158 then data2357 else data2358)) else (if j < 160 then data2359 else (if j < 161 then data2360 else data2361)))) else (if j < 168 then (if j < 165 then (if j < 163 then data2362 else (if j < 164 then data2363 else data2364)) else (if j < 166 then data2365 else (if j < 167 then data2366 else data2367))) else (if j < 171 then (if j < 169 then data2368 else (if j < 170 then data2369 else data2370)) else (if j < 173 then (if j < 172 then data2371 else data2372) else (if j < 174 then data2373 else data2374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data2375 else (if j < 177 then data2376 else data2377)) else (if j < 179 then data2378 else (if j < 180 then data2379 else data2380))) else (if j < 184 then (if j < 182 then data2381 else (if j < 183 then data2382 else data2383)) else (if j < 185 then data2384 else (if j < 186 then data2385 else data2386)))) else (if j < 193 then (if j < 190 then (if j < 188 then data2387 else (if j < 189 then data2388 else data2389)) else (if j < 191 then data2390 else (if j < 192 then data2391 else data2392))) else (if j < 196 then (if j < 194 then data2393 else (if j < 195 then data2394 else data2395)) else (if j < 198 then (if j < 197 then data2396 else data2397) else (if j < 199 then data2398 else data2399))))))))

def srcTableB11 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src2200 else (if j < 2 then src2201 else src2202)) else (if j < 4 then src2203 else (if j < 5 then src2204 else src2205))) else (if j < 9 then (if j < 7 then src2206 else (if j < 8 then src2207 else src2208)) else (if j < 10 then src2209 else (if j < 11 then src2210 else src2211)))) else (if j < 18 then (if j < 15 then (if j < 13 then src2212 else (if j < 14 then src2213 else src2214)) else (if j < 16 then src2215 else (if j < 17 then src2216 else src2217))) else (if j < 21 then (if j < 19 then src2218 else (if j < 20 then src2219 else src2220)) else (if j < 23 then (if j < 22 then src2221 else src2222) else (if j < 24 then src2223 else src2224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src2225 else (if j < 27 then src2226 else src2227)) else (if j < 29 then src2228 else (if j < 30 then src2229 else src2230))) else (if j < 34 then (if j < 32 then src2231 else (if j < 33 then src2232 else src2233)) else (if j < 35 then src2234 else (if j < 36 then src2235 else src2236)))) else (if j < 43 then (if j < 40 then (if j < 38 then src2237 else (if j < 39 then src2238 else src2239)) else (if j < 41 then src2240 else (if j < 42 then src2241 else src2242))) else (if j < 46 then (if j < 44 then src2243 else (if j < 45 then src2244 else src2245)) else (if j < 48 then (if j < 47 then src2246 else src2247) else (if j < 49 then src2248 else src2249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src2250 else (if j < 52 then src2251 else src2252)) else (if j < 54 then src2253 else (if j < 55 then src2254 else src2255))) else (if j < 59 then (if j < 57 then src2256 else (if j < 58 then src2257 else src2258)) else (if j < 60 then src2259 else (if j < 61 then src2260 else src2261)))) else (if j < 68 then (if j < 65 then (if j < 63 then src2262 else (if j < 64 then src2263 else src2264)) else (if j < 66 then src2265 else (if j < 67 then src2266 else src2267))) else (if j < 71 then (if j < 69 then src2268 else (if j < 70 then src2269 else src2270)) else (if j < 73 then (if j < 72 then src2271 else src2272) else (if j < 74 then src2273 else src2274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src2275 else (if j < 77 then src2276 else src2277)) else (if j < 79 then src2278 else (if j < 80 then src2279 else src2280))) else (if j < 84 then (if j < 82 then src2281 else (if j < 83 then src2282 else src2283)) else (if j < 85 then src2284 else (if j < 86 then src2285 else src2286)))) else (if j < 93 then (if j < 90 then (if j < 88 then src2287 else (if j < 89 then src2288 else src2289)) else (if j < 91 then src2290 else (if j < 92 then src2291 else src2292))) else (if j < 96 then (if j < 94 then src2293 else (if j < 95 then src2294 else src2295)) else (if j < 98 then (if j < 97 then src2296 else src2297) else (if j < 99 then src2298 else src2299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src2300 else (if j < 102 then src2301 else src2302)) else (if j < 104 then src2303 else (if j < 105 then src2304 else src2305))) else (if j < 109 then (if j < 107 then src2306 else (if j < 108 then src2307 else src2308)) else (if j < 110 then src2309 else (if j < 111 then src2310 else src2311)))) else (if j < 118 then (if j < 115 then (if j < 113 then src2312 else (if j < 114 then src2313 else src2314)) else (if j < 116 then src2315 else (if j < 117 then src2316 else src2317))) else (if j < 121 then (if j < 119 then src2318 else (if j < 120 then src2319 else src2320)) else (if j < 123 then (if j < 122 then src2321 else src2322) else (if j < 124 then src2323 else src2324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src2325 else (if j < 127 then src2326 else src2327)) else (if j < 129 then src2328 else (if j < 130 then src2329 else src2330))) else (if j < 134 then (if j < 132 then src2331 else (if j < 133 then src2332 else src2333)) else (if j < 135 then src2334 else (if j < 136 then src2335 else src2336)))) else (if j < 143 then (if j < 140 then (if j < 138 then src2337 else (if j < 139 then src2338 else src2339)) else (if j < 141 then src2340 else (if j < 142 then src2341 else src2342))) else (if j < 146 then (if j < 144 then src2343 else (if j < 145 then src2344 else src2345)) else (if j < 148 then (if j < 147 then src2346 else src2347) else (if j < 149 then src2348 else src2349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src2350 else (if j < 152 then src2351 else src2352)) else (if j < 154 then src2353 else (if j < 155 then src2354 else src2355))) else (if j < 159 then (if j < 157 then src2356 else (if j < 158 then src2357 else src2358)) else (if j < 160 then src2359 else (if j < 161 then src2360 else src2361)))) else (if j < 168 then (if j < 165 then (if j < 163 then src2362 else (if j < 164 then src2363 else src2364)) else (if j < 166 then src2365 else (if j < 167 then src2366 else src2367))) else (if j < 171 then (if j < 169 then src2368 else (if j < 170 then src2369 else src2370)) else (if j < 173 then (if j < 172 then src2371 else src2372) else (if j < 174 then src2373 else src2374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src2375 else (if j < 177 then src2376 else src2377)) else (if j < 179 then src2378 else (if j < 180 then src2379 else src2380))) else (if j < 184 then (if j < 182 then src2381 else (if j < 183 then src2382 else src2383)) else (if j < 185 then src2384 else (if j < 186 then src2385 else src2386)))) else (if j < 193 then (if j < 190 then (if j < 188 then src2387 else (if j < 189 then src2388 else src2389)) else (if j < 191 then src2390 else (if j < 192 then src2391 else src2392))) else (if j < 196 then (if j < 194 then src2393 else (if j < 195 then src2394 else src2395)) else (if j < 198 then (if j < 197 then src2396 else src2397) else (if j < 199 then src2398 else src2399))))))))

def dstTableB11 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst2200 else (if j < 2 then dst2201 else dst2202)) else (if j < 4 then dst2203 else (if j < 5 then dst2204 else dst2205))) else (if j < 9 then (if j < 7 then dst2206 else (if j < 8 then dst2207 else dst2208)) else (if j < 10 then dst2209 else (if j < 11 then dst2210 else dst2211)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst2212 else (if j < 14 then dst2213 else dst2214)) else (if j < 16 then dst2215 else (if j < 17 then dst2216 else dst2217))) else (if j < 21 then (if j < 19 then dst2218 else (if j < 20 then dst2219 else dst2220)) else (if j < 23 then (if j < 22 then dst2221 else dst2222) else (if j < 24 then dst2223 else dst2224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst2225 else (if j < 27 then dst2226 else dst2227)) else (if j < 29 then dst2228 else (if j < 30 then dst2229 else dst2230))) else (if j < 34 then (if j < 32 then dst2231 else (if j < 33 then dst2232 else dst2233)) else (if j < 35 then dst2234 else (if j < 36 then dst2235 else dst2236)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst2237 else (if j < 39 then dst2238 else dst2239)) else (if j < 41 then dst2240 else (if j < 42 then dst2241 else dst2242))) else (if j < 46 then (if j < 44 then dst2243 else (if j < 45 then dst2244 else dst2245)) else (if j < 48 then (if j < 47 then dst2246 else dst2247) else (if j < 49 then dst2248 else dst2249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst2250 else (if j < 52 then dst2251 else dst2252)) else (if j < 54 then dst2253 else (if j < 55 then dst2254 else dst2255))) else (if j < 59 then (if j < 57 then dst2256 else (if j < 58 then dst2257 else dst2258)) else (if j < 60 then dst2259 else (if j < 61 then dst2260 else dst2261)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst2262 else (if j < 64 then dst2263 else dst2264)) else (if j < 66 then dst2265 else (if j < 67 then dst2266 else dst2267))) else (if j < 71 then (if j < 69 then dst2268 else (if j < 70 then dst2269 else dst2270)) else (if j < 73 then (if j < 72 then dst2271 else dst2272) else (if j < 74 then dst2273 else dst2274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst2275 else (if j < 77 then dst2276 else dst2277)) else (if j < 79 then dst2278 else (if j < 80 then dst2279 else dst2280))) else (if j < 84 then (if j < 82 then dst2281 else (if j < 83 then dst2282 else dst2283)) else (if j < 85 then dst2284 else (if j < 86 then dst2285 else dst2286)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst2287 else (if j < 89 then dst2288 else dst2289)) else (if j < 91 then dst2290 else (if j < 92 then dst2291 else dst2292))) else (if j < 96 then (if j < 94 then dst2293 else (if j < 95 then dst2294 else dst2295)) else (if j < 98 then (if j < 97 then dst2296 else dst2297) else (if j < 99 then dst2298 else dst2299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst2300 else (if j < 102 then dst2301 else dst2302)) else (if j < 104 then dst2303 else (if j < 105 then dst2304 else dst2305))) else (if j < 109 then (if j < 107 then dst2306 else (if j < 108 then dst2307 else dst2308)) else (if j < 110 then dst2309 else (if j < 111 then dst2310 else dst2311)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst2312 else (if j < 114 then dst2313 else dst2314)) else (if j < 116 then dst2315 else (if j < 117 then dst2316 else dst2317))) else (if j < 121 then (if j < 119 then dst2318 else (if j < 120 then dst2319 else dst2320)) else (if j < 123 then (if j < 122 then dst2321 else dst2322) else (if j < 124 then dst2323 else dst2324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst2325 else (if j < 127 then dst2326 else dst2327)) else (if j < 129 then dst2328 else (if j < 130 then dst2329 else dst2330))) else (if j < 134 then (if j < 132 then dst2331 else (if j < 133 then dst2332 else dst2333)) else (if j < 135 then dst2334 else (if j < 136 then dst2335 else dst2336)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst2337 else (if j < 139 then dst2338 else dst2339)) else (if j < 141 then dst2340 else (if j < 142 then dst2341 else dst2342))) else (if j < 146 then (if j < 144 then dst2343 else (if j < 145 then dst2344 else dst2345)) else (if j < 148 then (if j < 147 then dst2346 else dst2347) else (if j < 149 then dst2348 else dst2349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst2350 else (if j < 152 then dst2351 else dst2352)) else (if j < 154 then dst2353 else (if j < 155 then dst2354 else dst2355))) else (if j < 159 then (if j < 157 then dst2356 else (if j < 158 then dst2357 else dst2358)) else (if j < 160 then dst2359 else (if j < 161 then dst2360 else dst2361)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst2362 else (if j < 164 then dst2363 else dst2364)) else (if j < 166 then dst2365 else (if j < 167 then dst2366 else dst2367))) else (if j < 171 then (if j < 169 then dst2368 else (if j < 170 then dst2369 else dst2370)) else (if j < 173 then (if j < 172 then dst2371 else dst2372) else (if j < 174 then dst2373 else dst2374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst2375 else (if j < 177 then dst2376 else dst2377)) else (if j < 179 then dst2378 else (if j < 180 then dst2379 else dst2380))) else (if j < 184 then (if j < 182 then dst2381 else (if j < 183 then dst2382 else dst2383)) else (if j < 185 then dst2384 else (if j < 186 then dst2385 else dst2386)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst2387 else (if j < 189 then dst2388 else dst2389)) else (if j < 191 then dst2390 else (if j < 192 then dst2391 else dst2392))) else (if j < 196 then (if j < 194 then dst2393 else (if j < 195 then dst2394 else dst2395)) else (if j < 198 then (if j < 197 then dst2396 else dst2397) else (if j < 199 then dst2398 else dst2399))))))))

def caseB11 (i : Fin 200) : Cases := ⟨2200 + i.val,by have := i.isLt; omega⟩
lemma tableB11_valid (i : Fin 200) :
    (lookupB11 i.val).Valid (srcTableB11 i.val) (dstTableB11 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data2200
  · exact valid_data2201
  · exact valid_data2202
  · exact valid_data2203
  · exact valid_data2204
  · exact valid_data2205
  · exact valid_data2206
  · exact valid_data2207
  · exact valid_data2208
  · exact valid_data2209
  · exact valid_data2210
  · exact valid_data2211
  · exact valid_data2212
  · exact valid_data2213
  · exact valid_data2214
  · exact valid_data2215
  · exact valid_data2216
  · exact valid_data2217
  · exact valid_data2218
  · exact valid_data2219
  · exact valid_data2220
  · exact valid_data2221
  · exact valid_data2222
  · exact valid_data2223
  · exact valid_data2224
  · exact valid_data2225
  · exact valid_data2226
  · exact valid_data2227
  · exact valid_data2228
  · exact valid_data2229
  · exact valid_data2230
  · exact valid_data2231
  · exact valid_data2232
  · exact valid_data2233
  · exact valid_data2234
  · exact valid_data2235
  · exact valid_data2236
  · exact valid_data2237
  · exact valid_data2238
  · exact valid_data2239
  · exact valid_data2240
  · exact valid_data2241
  · exact valid_data2242
  · exact valid_data2243
  · exact valid_data2244
  · exact valid_data2245
  · exact valid_data2246
  · exact valid_data2247
  · exact valid_data2248
  · exact valid_data2249
  · exact valid_data2250
  · exact valid_data2251
  · exact valid_data2252
  · exact valid_data2253
  · exact valid_data2254
  · exact valid_data2255
  · exact valid_data2256
  · exact valid_data2257
  · exact valid_data2258
  · exact valid_data2259
  · exact valid_data2260
  · exact valid_data2261
  · exact valid_data2262
  · exact valid_data2263
  · exact valid_data2264
  · exact valid_data2265
  · exact valid_data2266
  · exact valid_data2267
  · exact valid_data2268
  · exact valid_data2269
  · exact valid_data2270
  · exact valid_data2271
  · exact valid_data2272
  · exact valid_data2273
  · exact valid_data2274
  · exact valid_data2275
  · exact valid_data2276
  · exact valid_data2277
  · exact valid_data2278
  · exact valid_data2279
  · exact valid_data2280
  · exact valid_data2281
  · exact valid_data2282
  · exact valid_data2283
  · exact valid_data2284
  · exact valid_data2285
  · exact valid_data2286
  · exact valid_data2287
  · exact valid_data2288
  · exact valid_data2289
  · exact valid_data2290
  · exact valid_data2291
  · exact valid_data2292
  · exact valid_data2293
  · exact valid_data2294
  · exact valid_data2295
  · exact valid_data2296
  · exact valid_data2297
  · exact valid_data2298
  · exact valid_data2299
  · exact valid_data2300
  · exact valid_data2301
  · exact valid_data2302
  · exact valid_data2303
  · exact valid_data2304
  · exact valid_data2305
  · exact valid_data2306
  · exact valid_data2307
  · exact valid_data2308
  · exact valid_data2309
  · exact valid_data2310
  · exact valid_data2311
  · exact valid_data2312
  · exact valid_data2313
  · exact valid_data2314
  · exact valid_data2315
  · exact valid_data2316
  · exact valid_data2317
  · exact valid_data2318
  · exact valid_data2319
  · exact valid_data2320
  · exact valid_data2321
  · exact valid_data2322
  · exact valid_data2323
  · exact valid_data2324
  · exact valid_data2325
  · exact valid_data2326
  · exact valid_data2327
  · exact valid_data2328
  · exact valid_data2329
  · exact valid_data2330
  · exact valid_data2331
  · exact valid_data2332
  · exact valid_data2333
  · exact valid_data2334
  · exact valid_data2335
  · exact valid_data2336
  · exact valid_data2337
  · exact valid_data2338
  · exact valid_data2339
  · exact valid_data2340
  · exact valid_data2341
  · exact valid_data2342
  · exact valid_data2343
  · exact valid_data2344
  · exact valid_data2345
  · exact valid_data2346
  · exact valid_data2347
  · exact valid_data2348
  · exact valid_data2349
  · exact valid_data2350
  · exact valid_data2351
  · exact valid_data2352
  · exact valid_data2353
  · exact valid_data2354
  · exact valid_data2355
  · exact valid_data2356
  · exact valid_data2357
  · exact valid_data2358
  · exact valid_data2359
  · exact valid_data2360
  · exact valid_data2361
  · exact valid_data2362
  · exact valid_data2363
  · exact valid_data2364
  · exact valid_data2365
  · exact valid_data2366
  · exact valid_data2367
  · exact valid_data2368
  · exact valid_data2369
  · exact valid_data2370
  · exact valid_data2371
  · exact valid_data2372
  · exact valid_data2373
  · exact valid_data2374
  · exact valid_data2375
  · exact valid_data2376
  · exact valid_data2377
  · exact valid_data2378
  · exact valid_data2379
  · exact valid_data2380
  · exact valid_data2381
  · exact valid_data2382
  · exact valid_data2383
  · exact valid_data2384
  · exact valid_data2385
  · exact valid_data2386
  · exact valid_data2387
  · exact valid_data2388
  · exact valid_data2389
  · exact valid_data2390
  · exact valid_data2391
  · exact valid_data2392
  · exact valid_data2393
  · exact valid_data2394
  · exact valid_data2395
  · exact valid_data2396
  · exact valid_data2397
  · exact valid_data2398
  · exact valid_data2399

lemma srcB11_row : ∀ (i : Fin 200) (e : E),
    srcTableB11 i.val e = caseSource (caseB11 i) e := by decide +kernel

lemma dstB11_row : ∀ (i : Fin 200) (e : E),
    dstTableB11 i.val e = caseTarget (caseB11 i) e := by decide +kernel

lemma sizeB11 : ∀ i : Fin 200, (lookupB11 i.val).size ≤ 5 →
    (lookupB11 i.val).size = 2 ∧
      (⟨caseKey (caseB11 i),caseKey_lt (caseB11 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB11 (i : Fin 200) : Certificate (caseB11 i) := by
  refine ⟨lookupB11 i.val,?_,sizeB11 i⟩
  have hv := tableB11_valid i
  rw [funext (srcB11_row i),funext (dstB11_row i)] at hv
  exact hv
lemma certificateInterval11 : FiniteIntervals.Covers CertificateAt 2200 2400 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2200 200 (fun i _ => certificateB11 i)
#print axioms certificateInterval11
end Erdos184Work.FiveRows3

import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src3200 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3200 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3200_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3200_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3200_2 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle3200_3 : CycleData E W := ⟨3,![3,23,18,11,6],![3,8,38,27,14]⟩
def cycle3200_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3200_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data3200 : PartitionData E W := ⟨6,![cycle3200_0,cycle3200_1,cycle3200_2,cycle3200_3,cycle3200_4,cycle3200_5]⟩
lemma valid_data3200 : data3200.Valid src3200 dst3200 Finset.univ := by decide +kernel

def src3201 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3201 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3201_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3201_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3201_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3201_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle3201_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3201_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3201 : PartitionData E W := ⟨6,![cycle3201_0,cycle3201_1,cycle3201_2,cycle3201_3,cycle3201_4,cycle3201_5]⟩
lemma valid_data3201 : data3201.Valid src3201 dst3201 Finset.univ := by decide +kernel

def src3202 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3202 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3202_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3202_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3202_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3202_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3202_4 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle3202_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3202_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3202 : PartitionData E W := ⟨7,![cycle3202_0,cycle3202_1,cycle3202_2,cycle3202_3,cycle3202_4,cycle3202_5,cycle3202_6]⟩
lemma valid_data3202 : data3202.Valid src3202 dst3202 Finset.univ := by decide +kernel

def src3203 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3203 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3203_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3203_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3203_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3203_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,18]⟩
def cycle3203_4 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle3203_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3203 : PartitionData E W := ⟨6,![cycle3203_0,cycle3203_1,cycle3203_2,cycle3203_3,cycle3203_4,cycle3203_5]⟩
lemma valid_data3203 : data3203.Valid src3203 dst3203 Finset.univ := by decide +kernel

def src3204 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3204 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3204_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3204_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3204_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3204_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle3204_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3204_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3204 : PartitionData E W := ⟨6,![cycle3204_0,cycle3204_1,cycle3204_2,cycle3204_3,cycle3204_4,cycle3204_5]⟩
lemma valid_data3204 : data3204.Valid src3204 dst3204 Finset.univ := by decide +kernel

def src3205 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3205 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3205_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3205_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3205_2 : CycleData E W := ⟨4,![4,23,14,10,16,9],![2,8,28,4,26,16]⟩
def cycle3205_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3205_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3205_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3205 : PartitionData E W := ⟨6,![cycle3205_0,cycle3205_1,cycle3205_2,cycle3205_3,cycle3205_4,cycle3205_5]⟩
lemma valid_data3205 : data3205.Valid src3205 dst3205 Finset.univ := by decide +kernel

def src3206 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3206 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3206_0 : CycleData E W := ⟨3,![0,1,10,16,9],![2,6,4,26,16]⟩
def cycle3206_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3206_2 : CycleData E W := ⟨2,![4,3,6,5],![2,8,3,14]⟩
def cycle3206_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle3206_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3206_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data3206 : PartitionData E W := ⟨6,![cycle3206_0,cycle3206_1,cycle3206_2,cycle3206_3,cycle3206_4,cycle3206_5]⟩
lemma valid_data3206 : data3206.Valid src3206 dst3206 Finset.univ := by decide +kernel

def src3207 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3207 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3207_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3207_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3207_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3207_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle3207_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle3207_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data3207 : PartitionData E W := ⟨6,![cycle3207_0,cycle3207_1,cycle3207_2,cycle3207_3,cycle3207_4,cycle3207_5]⟩
lemma valid_data3207 : data3207.Valid src3207 dst3207 Finset.univ := by decide +kernel

def src3208 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3208 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3208_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3208_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3208_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle3208_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3208_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle3208_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data3208 : PartitionData E W := ⟨6,![cycle3208_0,cycle3208_1,cycle3208_2,cycle3208_3,cycle3208_4,cycle3208_5]⟩
lemma valid_data3208 : data3208.Valid src3208 dst3208 Finset.univ := by decide +kernel

def src3209 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3209 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3209_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle3209_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3209_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3209_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3209_4 : CycleData E W := ⟨3,![6,11,16,22,7],![3,14,26,38,18]⟩
def cycle3209_5 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def data3209 : PartitionData E W := ⟨6,![cycle3209_0,cycle3209_1,cycle3209_2,cycle3209_3,cycle3209_4,cycle3209_5]⟩
lemma valid_data3209 : data3209.Valid src3209 dst3209 Finset.univ := by decide +kernel

def src3210 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3210 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3210_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle3210_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3210_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3210_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3210_4 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,26,16]⟩
def cycle3210_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3210 : PartitionData E W := ⟨6,![cycle3210_0,cycle3210_1,cycle3210_2,cycle3210_3,cycle3210_4,cycle3210_5]⟩
lemma valid_data3210 : data3210.Valid src3210 dst3210 Finset.univ := by decide +kernel

def src3211 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3211 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3211_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle3211_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3211_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3211_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3211_4 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle3211_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def data3211 : PartitionData E W := ⟨6,![cycle3211_0,cycle3211_1,cycle3211_2,cycle3211_3,cycle3211_4,cycle3211_5]⟩
lemma valid_data3211 : data3211.Valid src3211 dst3211 Finset.univ := by decide +kernel

def src3212 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3212 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3212_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3212_1 : CycleData E W := ⟨2,![1,15,13,14],![4,6,27,28]⟩
def cycle3212_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3212_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3212_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,27,16]⟩
def cycle3212_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data3212 : PartitionData E W := ⟨6,![cycle3212_0,cycle3212_1,cycle3212_2,cycle3212_3,cycle3212_4,cycle3212_5]⟩
lemma valid_data3212 : data3212.Valid src3212 dst3212 Finset.univ := by decide +kernel

def src3213 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3213 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3213_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3213_1 : CycleData E W := ⟨3,![2,1,19,23,3],![3,4,6,38,8]⟩
def cycle3213_2 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle3213_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle3213_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3213_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3213 : PartitionData E W := ⟨6,![cycle3213_0,cycle3213_1,cycle3213_2,cycle3213_3,cycle3213_4,cycle3213_5]⟩
lemma valid_data3213 : data3213.Valid src3213 dst3213 Finset.univ := by decide +kernel

def src3214 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3214 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3214_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3214_1 : CycleData E W := ⟨3,![2,1,19,21,7],![3,4,6,38,18]⟩
def cycle3214_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3214_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle3214_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3214_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3214 : PartitionData E W := ⟨6,![cycle3214_0,cycle3214_1,cycle3214_2,cycle3214_3,cycle3214_4,cycle3214_5]⟩
lemma valid_data3214 : data3214.Valid src3214 dst3214 Finset.univ := by decide +kernel

def src3215 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3215 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3215_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3215_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3215_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3215_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3215_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle3215_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data3215 : PartitionData E W := ⟨6,![cycle3215_0,cycle3215_1,cycle3215_2,cycle3215_3,cycle3215_4,cycle3215_5]⟩
lemma valid_data3215 : data3215.Valid src3215 dst3215 Finset.univ := by decide +kernel

def src3216 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3216 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3216_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3216_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3216_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3216_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle3216_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3216_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data3216 : PartitionData E W := ⟨6,![cycle3216_0,cycle3216_1,cycle3216_2,cycle3216_3,cycle3216_4,cycle3216_5]⟩
lemma valid_data3216 : data3216.Valid src3216 dst3216 Finset.univ := by decide +kernel

def src3217 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3217 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3217_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3217_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3217_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle3217_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3217_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3217_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data3217 : PartitionData E W := ⟨6,![cycle3217_0,cycle3217_1,cycle3217_2,cycle3217_3,cycle3217_4,cycle3217_5]⟩
lemma valid_data3217 : data3217.Valid src3217 dst3217 Finset.univ := by decide +kernel

def src3218 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3218 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3218_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3218_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3218_2 : CycleData E W := ⟨3,![2,10,16,22,7],![3,4,26,38,18]⟩
def cycle3218_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3218_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3218_5 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def data3218 : PartitionData E W := ⟨6,![cycle3218_0,cycle3218_1,cycle3218_2,cycle3218_3,cycle3218_4,cycle3218_5]⟩
lemma valid_data3218 : data3218.Valid src3218 dst3218 Finset.univ := by decide +kernel

def src3219 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3219 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3219_0 : CycleData E W := ⟨3,![0,19,18,17,9],![2,6,38,26,16]⟩
def cycle3219_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3219_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3219_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3219_4 : CycleData E W := ⟨3,![4,23,22,12,5],![2,8,38,28,14]⟩
def cycle3219_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3219 : PartitionData E W := ⟨6,![cycle3219_0,cycle3219_1,cycle3219_2,cycle3219_3,cycle3219_4,cycle3219_5]⟩
lemma valid_data3219 : data3219.Valid src3219 dst3219 Finset.univ := by decide +kernel

def src3220 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3220 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3220_0 : CycleData E W := ⟨3,![0,1,14,16,9],![2,6,4,27,16]⟩
def cycle3220_1 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3220_2 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3220_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3220_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle3220_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3220 : PartitionData E W := ⟨6,![cycle3220_0,cycle3220_1,cycle3220_2,cycle3220_3,cycle3220_4,cycle3220_5]⟩
lemma valid_data3220 : data3220.Valid src3220 dst3220 Finset.univ := by decide +kernel

def src3221 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3221 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3221_0 : CycleData E W := ⟨3,![0,19,18,17,9],![2,6,38,26,16]⟩
def cycle3221_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3221_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle3221_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3221_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle3221_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3221 : PartitionData E W := ⟨6,![cycle3221_0,cycle3221_1,cycle3221_2,cycle3221_3,cycle3221_4,cycle3221_5]⟩
lemma valid_data3221 : data3221.Valid src3221 dst3221 Finset.univ := by decide +kernel

def src3222 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3222 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3222_0 : CycleData E W := ⟨3,![0,19,18,17,9],![2,6,38,27,16]⟩
def cycle3222_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3222_2 : CycleData E W := ⟨2,![2,14,13,6],![3,4,27,14]⟩
def cycle3222_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3222_4 : CycleData E W := ⟨3,![4,23,22,12,5],![2,8,38,28,14]⟩
def cycle3222_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data3222 : PartitionData E W := ⟨6,![cycle3222_0,cycle3222_1,cycle3222_2,cycle3222_3,cycle3222_4,cycle3222_5]⟩
lemma valid_data3222 : data3222.Valid src3222 dst3222 Finset.univ := by decide +kernel

def src3223 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3223 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3223_0 : CycleData E W := ⟨3,![0,1,10,16,9],![2,6,4,26,16]⟩
def cycle3223_1 : CycleData E W := ⟨2,![2,14,13,6],![3,4,27,14]⟩
def cycle3223_2 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3223_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3223_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle3223_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3223 : PartitionData E W := ⟨6,![cycle3223_0,cycle3223_1,cycle3223_2,cycle3223_3,cycle3223_4,cycle3223_5]⟩
lemma valid_data3223 : data3223.Valid src3223 dst3223 Finset.univ := by decide +kernel

def src3224 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3224 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3224_0 : CycleData E W := ⟨3,![0,19,18,17,9],![2,6,38,27,16]⟩
def cycle3224_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3224_2 : CycleData E W := ⟨2,![2,14,13,6],![3,4,27,14]⟩
def cycle3224_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3224_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle3224_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data3224 : PartitionData E W := ⟨6,![cycle3224_0,cycle3224_1,cycle3224_2,cycle3224_3,cycle3224_4,cycle3224_5]⟩
lemma valid_data3224 : data3224.Valid src3224 dst3224 Finset.univ := by decide +kernel

def src3225 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3225 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3225_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3225_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3225_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3225_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle3225_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3225_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data3225 : PartitionData E W := ⟨6,![cycle3225_0,cycle3225_1,cycle3225_2,cycle3225_3,cycle3225_4,cycle3225_5]⟩
lemma valid_data3225 : data3225.Valid src3225 dst3225 Finset.univ := by decide +kernel

def src3226 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3226 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3226_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3226_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3226_2 : CycleData E W := ⟨3,![4,23,11,16,9],![2,8,28,26,16]⟩
def cycle3226_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3226_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3226_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data3226 : PartitionData E W := ⟨6,![cycle3226_0,cycle3226_1,cycle3226_2,cycle3226_3,cycle3226_4,cycle3226_5]⟩
lemma valid_data3226 : data3226.Valid src3226 dst3226 Finset.univ := by decide +kernel

def src3227 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3227 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3227_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3227_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3227_2 : CycleData E W := ⟨3,![2,10,11,12,6],![3,4,26,28,14]⟩
def cycle3227_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3227_4 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3227_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data3227 : PartitionData E W := ⟨6,![cycle3227_0,cycle3227_1,cycle3227_2,cycle3227_3,cycle3227_4,cycle3227_5]⟩
lemma valid_data3227 : data3227.Valid src3227 dst3227 Finset.univ := by decide +kernel

def src3228 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3228 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3228_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3228_1 : CycleData E W := ⟨3,![2,1,19,23,3],![3,4,6,38,8]⟩
def cycle3228_2 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle3228_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle3228_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3228_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3228 : PartitionData E W := ⟨6,![cycle3228_0,cycle3228_1,cycle3228_2,cycle3228_3,cycle3228_4,cycle3228_5]⟩
lemma valid_data3228 : data3228.Valid src3228 dst3228 Finset.univ := by decide +kernel

def src3229 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3229 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3229_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3229_1 : CycleData E W := ⟨3,![2,1,19,21,7],![3,4,6,38,18]⟩
def cycle3229_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3229_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle3229_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3229_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3229 : PartitionData E W := ⟨6,![cycle3229_0,cycle3229_1,cycle3229_2,cycle3229_3,cycle3229_4,cycle3229_5]⟩
lemma valid_data3229 : data3229.Valid src3229 dst3229 Finset.univ := by decide +kernel

def src3230 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3230 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3230_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3230_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3230_2 : CycleData E W := ⟨2,![2,14,13,6],![3,4,27,14]⟩
def cycle3230_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3230_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle3230_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data3230 : PartitionData E W := ⟨6,![cycle3230_0,cycle3230_1,cycle3230_2,cycle3230_3,cycle3230_4,cycle3230_5]⟩
lemma valid_data3230 : data3230.Valid src3230 dst3230 Finset.univ := by decide +kernel

def src3231 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3231 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3231_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3231_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3231_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle3231_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3231_4 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,27,16]⟩
def cycle3231_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data3231 : PartitionData E W := ⟨6,![cycle3231_0,cycle3231_1,cycle3231_2,cycle3231_3,cycle3231_4,cycle3231_5]⟩
lemma valid_data3231 : data3231.Valid src3231 dst3231 Finset.univ := by decide +kernel

def src3232 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3232 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3232_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3232_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3232_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle3232_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3232_4 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle3232_5 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def data3232 : PartitionData E W := ⟨6,![cycle3232_0,cycle3232_1,cycle3232_2,cycle3232_3,cycle3232_4,cycle3232_5]⟩
lemma valid_data3232 : data3232.Valid src3232 dst3232 Finset.univ := by decide +kernel

def src3233 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3233 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3233_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3233_1 : CycleData E W := ⟨2,![1,15,13,14],![4,6,26,28]⟩
def cycle3233_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle3233_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3233_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,26,16]⟩
def cycle3233_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data3233 : PartitionData E W := ⟨6,![cycle3233_0,cycle3233_1,cycle3233_2,cycle3233_3,cycle3233_4,cycle3233_5]⟩
lemma valid_data3233 : data3233.Valid src3233 dst3233 Finset.univ := by decide +kernel

def src3234 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3234 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3234_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3234_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3234_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3234_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle3234_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3234_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data3234 : PartitionData E W := ⟨6,![cycle3234_0,cycle3234_1,cycle3234_2,cycle3234_3,cycle3234_4,cycle3234_5]⟩
lemma valid_data3234 : data3234.Valid src3234 dst3234 Finset.univ := by decide +kernel

def src3235 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3235 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3235_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3235_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3235_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle3235_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3235_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3235_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data3235 : PartitionData E W := ⟨6,![cycle3235_0,cycle3235_1,cycle3235_2,cycle3235_3,cycle3235_4,cycle3235_5]⟩
lemma valid_data3235 : data3235.Valid src3235 dst3235 Finset.univ := by decide +kernel

def src3236 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3236 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3236_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3236_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3236_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3236_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3236_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,27,38,18]⟩
def cycle3236_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data3236 : PartitionData E W := ⟨6,![cycle3236_0,cycle3236_1,cycle3236_2,cycle3236_3,cycle3236_4,cycle3236_5]⟩
lemma valid_data3236 : data3236.Valid src3236 dst3236 Finset.univ := by decide +kernel

def src3237 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3237 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3237_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3237_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3237_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3237_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle3237_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3237_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3237 : PartitionData E W := ⟨6,![cycle3237_0,cycle3237_1,cycle3237_2,cycle3237_3,cycle3237_4,cycle3237_5]⟩
lemma valid_data3237 : data3237.Valid src3237 dst3237 Finset.univ := by decide +kernel

def src3238 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3238 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3238_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3238_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3238_2 : CycleData E W := ⟨4,![4,23,14,10,18,9],![2,8,28,4,27,16]⟩
def cycle3238_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3238_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3238_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3238 : PartitionData E W := ⟨6,![cycle3238_0,cycle3238_1,cycle3238_2,cycle3238_3,cycle3238_4,cycle3238_5]⟩
lemma valid_data3238 : data3238.Valid src3238 dst3238 Finset.univ := by decide +kernel

def src3239 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3239 : E → W := ![6,4,3,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3239_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3239_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3239_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3239_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3239_4 : CycleData E W := ⟨3,![6,11,18,8,7],![3,14,27,16,18]⟩
def cycle3239_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3239 : PartitionData E W := ⟨6,![cycle3239_0,cycle3239_1,cycle3239_2,cycle3239_3,cycle3239_4,cycle3239_5]⟩
lemma valid_data3239 : data3239.Valid src3239 dst3239 Finset.univ := by decide +kernel

def src3240 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3240 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3240_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3240_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3240_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3240_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3240_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3240_5 : CycleData E W := ⟨3,![6,21,22,18,12],![14,18,28,38,27]⟩
def data3240 : PartitionData E W := ⟨6,![cycle3240_0,cycle3240_1,cycle3240_2,cycle3240_3,cycle3240_4,cycle3240_5]⟩
lemma valid_data3240 : data3240.Valid src3240 dst3240 Finset.univ := by decide +kernel

def src3241 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3241 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3241_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3241_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3241_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3241_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3241_4 : CycleData E W := ⟨3,![4,23,22,17,9],![2,8,28,38,16]⟩
def cycle3241_5 : CycleData E W := ⟨2,![6,21,18,12],![14,18,38,27]⟩
def data3241 : PartitionData E W := ⟨6,![cycle3241_0,cycle3241_1,cycle3241_2,cycle3241_3,cycle3241_4,cycle3241_5]⟩
lemma valid_data3241 : data3241.Valid src3241 dst3241 Finset.univ := by decide +kernel

def src3242 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3242 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3242_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3242_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3242_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3242_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3242_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3242_5 : CycleData E W := ⟨2,![6,22,18,12],![14,18,38,27]⟩
def data3242 : PartitionData E W := ⟨6,![cycle3242_0,cycle3242_1,cycle3242_2,cycle3242_3,cycle3242_4,cycle3242_5]⟩
lemma valid_data3242 : data3242.Valid src3242 dst3242 Finset.univ := by decide +kernel

def src3243 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3243 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3243_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3243_1 : CycleData E W := ⟨3,![2,1,19,18,8],![3,4,6,27,16]⟩
def cycle3243_2 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3243_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3243_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def cycle3243_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data3243 : PartitionData E W := ⟨6,![cycle3243_0,cycle3243_1,cycle3243_2,cycle3243_3,cycle3243_4,cycle3243_5]⟩
lemma valid_data3243 : data3243.Valid src3243 dst3243 Finset.univ := by decide +kernel

def src3244 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3244 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3244_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle3244_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3244_2 : CycleData E W := ⟨3,![2,14,13,18,8],![3,4,28,27,16]⟩
def cycle3244_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3244_4 : CycleData E W := ⟨3,![4,23,22,17,9],![2,8,28,38,16]⟩
def cycle3244_5 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def data3244 : PartitionData E W := ⟨6,![cycle3244_0,cycle3244_1,cycle3244_2,cycle3244_3,cycle3244_4,cycle3244_5]⟩
lemma valid_data3244 : data3244.Valid src3244 dst3244 Finset.univ := by decide +kernel

def src3245 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3245 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3245_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle3245_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3245_2 : CycleData E W := ⟨3,![2,14,13,18,8],![3,4,28,27,16]⟩
def cycle3245_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3245_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3245_5 : CycleData E W := ⟨2,![6,22,16,11],![14,18,38,26]⟩
def data3245 : PartitionData E W := ⟨6,![cycle3245_0,cycle3245_1,cycle3245_2,cycle3245_3,cycle3245_4,cycle3245_5]⟩
lemma valid_data3245 : data3245.Valid src3245 dst3245 Finset.univ := by decide +kernel

def src3246 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3246 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3246_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3246_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3246_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3246_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3246_4 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3246_5 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def data3246 : PartitionData E W := ⟨6,![cycle3246_0,cycle3246_1,cycle3246_2,cycle3246_3,cycle3246_4,cycle3246_5]⟩
lemma valid_data3246 : data3246.Valid src3246 dst3246 Finset.univ := by decide +kernel

def src3247 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3247 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3247_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle3247_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3247_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3247_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3247_4 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle3247_5 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def data3247 : PartitionData E W := ⟨6,![cycle3247_0,cycle3247_1,cycle3247_2,cycle3247_3,cycle3247_4,cycle3247_5]⟩
lemma valid_data3247 : data3247.Valid src3247 dst3247 Finset.univ := by decide +kernel

def src3248 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3248 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3248_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3248_1 : CycleData E W := ⟨2,![1,15,13,14],![4,6,27,28]⟩
def cycle3248_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3248_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3248_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,27,16]⟩
def cycle3248_5 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def data3248 : PartitionData E W := ⟨6,![cycle3248_0,cycle3248_1,cycle3248_2,cycle3248_3,cycle3248_4,cycle3248_5]⟩
lemma valid_data3248 : data3248.Valid src3248 dst3248 Finset.univ := by decide +kernel

def src3249 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3249 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3249_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3249_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3249_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle3249_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3249_4 : CycleData E W := ⟨2,![5,11,16,9],![2,14,26,16]⟩
def cycle3249_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3249_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3249 : PartitionData E W := ⟨7,![cycle3249_0,cycle3249_1,cycle3249_2,cycle3249_3,cycle3249_4,cycle3249_5,cycle3249_6]⟩
lemma valid_data3249 : data3249.Valid src3249 dst3249 Finset.univ := by decide +kernel

def src3250 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3250 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3250_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3250_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3250_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3250_3 : CycleData E W := ⟨3,![15,11,6,21,19],![6,26,14,18,38]⟩
def cycle3250_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3250_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3250 : PartitionData E W := ⟨6,![cycle3250_0,cycle3250_1,cycle3250_2,cycle3250_3,cycle3250_4,cycle3250_5]⟩
lemma valid_data3250 : data3250.Valid src3250 dst3250 Finset.univ := by decide +kernel

def src3251 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3251 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3251_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3251_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3251_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3251_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3251_4 : CycleData E W := ⟨3,![4,20,13,17,9],![2,8,28,27,16]⟩
def cycle3251_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3251 : PartitionData E W := ⟨6,![cycle3251_0,cycle3251_1,cycle3251_2,cycle3251_3,cycle3251_4,cycle3251_5]⟩
lemma valid_data3251 : data3251.Valid src3251 dst3251 Finset.univ := by decide +kernel

def src3252 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3252 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3252_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3252_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3252_2 : CycleData E W := ⟨3,![4,23,16,11,5],![2,8,38,26,14]⟩
def cycle3252_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3252_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3252_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3252 : PartitionData E W := ⟨6,![cycle3252_0,cycle3252_1,cycle3252_2,cycle3252_3,cycle3252_4,cycle3252_5]⟩
lemma valid_data3252 : data3252.Valid src3252 dst3252 Finset.univ := by decide +kernel

def src3253 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3253 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3253_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3253_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3253_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3253_3 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle3253_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3253_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3253 : PartitionData E W := ⟨6,![cycle3253_0,cycle3253_1,cycle3253_2,cycle3253_3,cycle3253_4,cycle3253_5]⟩
lemma valid_data3253 : data3253.Valid src3253 dst3253 Finset.univ := by decide +kernel

def src3254 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3254 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3254_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3254_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3254_2 : CycleData E W := ⟨3,![2,10,16,17,8],![3,4,26,38,16]⟩
def cycle3254_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3254_4 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle3254_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3254 : PartitionData E W := ⟨6,![cycle3254_0,cycle3254_1,cycle3254_2,cycle3254_3,cycle3254_4,cycle3254_5]⟩
lemma valid_data3254 : data3254.Valid src3254 dst3254 Finset.univ := by decide +kernel

def src3255 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3255 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3255_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3255_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3255_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3255_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3255_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3255_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3255 : PartitionData E W := ⟨6,![cycle3255_0,cycle3255_1,cycle3255_2,cycle3255_3,cycle3255_4,cycle3255_5]⟩
lemma valid_data3255 : data3255.Valid src3255 dst3255 Finset.univ := by decide +kernel

def src3256 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3256 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3256_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3256_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3256_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3256_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle3256_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3256_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3256 : PartitionData E W := ⟨6,![cycle3256_0,cycle3256_1,cycle3256_2,cycle3256_3,cycle3256_4,cycle3256_5]⟩
lemma valid_data3256 : data3256.Valid src3256 dst3256 Finset.univ := by decide +kernel

def src3257 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3257 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3257_0 : CycleData E W := ⟨3,![0,19,18,11,5],![2,6,38,26,14]⟩
def cycle3257_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3257_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3257_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3257_4 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle3257_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3257 : PartitionData E W := ⟨6,![cycle3257_0,cycle3257_1,cycle3257_2,cycle3257_3,cycle3257_4,cycle3257_5]⟩
lemma valid_data3257 : data3257.Valid src3257 dst3257 Finset.univ := by decide +kernel

def src3258 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3258 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3258_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3258_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3258_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3258_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3258_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3258_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3258 : PartitionData E W := ⟨6,![cycle3258_0,cycle3258_1,cycle3258_2,cycle3258_3,cycle3258_4,cycle3258_5]⟩
lemma valid_data3258 : data3258.Valid src3258 dst3258 Finset.univ := by decide +kernel

def src3259 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3259 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3259_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3259_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3259_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3259_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3259_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3259_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3259 : PartitionData E W := ⟨6,![cycle3259_0,cycle3259_1,cycle3259_2,cycle3259_3,cycle3259_4,cycle3259_5]⟩
lemma valid_data3259 : data3259.Valid src3259 dst3259 Finset.univ := by decide +kernel

def src3260 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3260 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3260_0 : CycleData E W := ⟨3,![0,19,18,13,5],![2,6,38,27,14]⟩
def cycle3260_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3260_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle3260_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3260_4 : CycleData E W := ⟨3,![4,20,11,16,9],![2,8,28,26,16]⟩
def cycle3260_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3260 : PartitionData E W := ⟨6,![cycle3260_0,cycle3260_1,cycle3260_2,cycle3260_3,cycle3260_4,cycle3260_5]⟩
lemma valid_data3260 : data3260.Valid src3260 dst3260 Finset.univ := by decide +kernel

def src3261 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3261 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3261_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3261_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3261_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3261_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3261_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3261_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3261 : PartitionData E W := ⟨6,![cycle3261_0,cycle3261_1,cycle3261_2,cycle3261_3,cycle3261_4,cycle3261_5]⟩
lemma valid_data3261 : data3261.Valid src3261 dst3261 Finset.univ := by decide +kernel

def src3262 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3262 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3262_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3262_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3262_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3262_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3262_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3262_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3262 : PartitionData E W := ⟨6,![cycle3262_0,cycle3262_1,cycle3262_2,cycle3262_3,cycle3262_4,cycle3262_5]⟩
lemma valid_data3262 : data3262.Valid src3262 dst3262 Finset.univ := by decide +kernel

def src3263 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3263 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3263_0 : CycleData E W := ⟨3,![0,15,11,12,5],![2,6,26,28,14]⟩
def cycle3263_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3263_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3263_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3263_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3263_5 : CycleData E W := ⟨2,![6,22,18,13],![14,18,38,27]⟩
def data3263 : PartitionData E W := ⟨6,![cycle3263_0,cycle3263_1,cycle3263_2,cycle3263_3,cycle3263_4,cycle3263_5]⟩
lemma valid_data3263 : data3263.Valid src3263 dst3263 Finset.univ := by decide +kernel

def src3264 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3264 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3264_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3264_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3264_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3264_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3264_4 : CycleData E W := ⟨2,![5,13,16,9],![2,14,27,16]⟩
def cycle3264_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3264_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3264 : PartitionData E W := ⟨7,![cycle3264_0,cycle3264_1,cycle3264_2,cycle3264_3,cycle3264_4,cycle3264_5,cycle3264_6]⟩
lemma valid_data3264 : data3264.Valid src3264 dst3264 Finset.univ := by decide +kernel

def src3265 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3265 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3265_0 : CycleData E W := ⟨3,![0,1,2,8,9],![2,6,4,3,16]⟩
def cycle3265_1 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3265_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3265_3 : CycleData E W := ⟨3,![15,13,6,21,19],![6,27,14,18,38]⟩
def cycle3265_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3265_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3265 : PartitionData E W := ⟨6,![cycle3265_0,cycle3265_1,cycle3265_2,cycle3265_3,cycle3265_4,cycle3265_5]⟩
lemma valid_data3265 : data3265.Valid src3265 dst3265 Finset.univ := by decide +kernel

def src3266 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3266 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3266_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3266_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3266_2 : CycleData E W := ⟨2,![2,14,16,8],![3,4,27,16]⟩
def cycle3266_3 : CycleData E W := ⟨2,![3,23,22,7],![3,8,38,18]⟩
def cycle3266_4 : CycleData E W := ⟨3,![4,20,11,17,9],![2,8,28,26,16]⟩
def cycle3266_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3266 : PartitionData E W := ⟨6,![cycle3266_0,cycle3266_1,cycle3266_2,cycle3266_3,cycle3266_4,cycle3266_5]⟩
lemma valid_data3266 : data3266.Valid src3266 dst3266 Finset.univ := by decide +kernel

def src3267 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3267 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3267_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3267_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3267_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3267_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3267_4 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle3267_5 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def data3267 : PartitionData E W := ⟨6,![cycle3267_0,cycle3267_1,cycle3267_2,cycle3267_3,cycle3267_4,cycle3267_5]⟩
lemma valid_data3267 : data3267.Valid src3267 dst3267 Finset.univ := by decide +kernel

def src3268 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3268 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3268_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3268_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,38,28]⟩
def cycle3268_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3268_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3268_4 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle3268_5 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def data3268 : PartitionData E W := ⟨6,![cycle3268_0,cycle3268_1,cycle3268_2,cycle3268_3,cycle3268_4,cycle3268_5]⟩
lemma valid_data3268 : data3268.Valid src3268 dst3268 Finset.univ := by decide +kernel

def src3269 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3269 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3269_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3269_1 : CycleData E W := ⟨2,![1,15,13,14],![4,6,26,28]⟩
def cycle3269_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3269_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3269_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,26,16]⟩
def cycle3269_5 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def data3269 : PartitionData E W := ⟨6,![cycle3269_0,cycle3269_1,cycle3269_2,cycle3269_3,cycle3269_4,cycle3269_5]⟩
lemma valid_data3269 : data3269.Valid src3269 dst3269 Finset.univ := by decide +kernel

def src3270 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3270 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3270_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3270_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3270_2 : CycleData E W := ⟨3,![2,14,13,16,8],![3,4,28,26,16]⟩
def cycle3270_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3270_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3270_5 : CycleData E W := ⟨3,![6,21,22,18,11],![14,18,28,38,27]⟩
def data3270 : PartitionData E W := ⟨6,![cycle3270_0,cycle3270_1,cycle3270_2,cycle3270_3,cycle3270_4,cycle3270_5]⟩
lemma valid_data3270 : data3270.Valid src3270 dst3270 Finset.univ := by decide +kernel

def src3271 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3271 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3271_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3271_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3271_2 : CycleData E W := ⟨3,![2,14,13,16,8],![3,4,28,26,16]⟩
def cycle3271_3 : CycleData E W := ⟨1,![3,20,7],![3,8,18]⟩
def cycle3271_4 : CycleData E W := ⟨3,![4,23,22,17,9],![2,8,28,38,16]⟩
def cycle3271_5 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def data3271 : PartitionData E W := ⟨6,![cycle3271_0,cycle3271_1,cycle3271_2,cycle3271_3,cycle3271_4,cycle3271_5]⟩
lemma valid_data3271 : data3271.Valid src3271 dst3271 Finset.univ := by decide +kernel

def src3272 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3272 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3272_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3272_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3272_2 : CycleData E W := ⟨3,![2,14,13,16,8],![3,4,28,26,16]⟩
def cycle3272_3 : CycleData E W := ⟨2,![3,20,21,7],![3,8,28,18]⟩
def cycle3272_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3272_5 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def data3272 : PartitionData E W := ⟨6,![cycle3272_0,cycle3272_1,cycle3272_2,cycle3272_3,cycle3272_4,cycle3272_5]⟩
lemma valid_data3272 : data3272.Valid src3272 dst3272 Finset.univ := by decide +kernel

def src3273 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3273 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3273_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3273_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3273_2 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3273_3 : CycleData E W := ⟨2,![4,3,8,9],![2,8,3,16]⟩
def cycle3273_4 : CycleData E W := ⟨4,![20,6,11,18,17,23],![8,18,14,27,16,38]⟩
def cycle3273_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3273 : PartitionData E W := ⟨6,![cycle3273_0,cycle3273_1,cycle3273_2,cycle3273_3,cycle3273_4,cycle3273_5]⟩
lemma valid_data3273 : data3273.Valid src3273 dst3273 Finset.univ := by decide +kernel

def src3274 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3274 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3274_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3274_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3274_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3274_3 : CycleData E W := ⟨3,![4,20,7,8,9],![2,8,18,3,16]⟩
def cycle3274_4 : CycleData E W := ⟨3,![6,21,17,18,11],![14,18,38,16,27]⟩
def cycle3274_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3274 : PartitionData E W := ⟨6,![cycle3274_0,cycle3274_1,cycle3274_2,cycle3274_3,cycle3274_4,cycle3274_5]⟩
lemma valid_data3274 : data3274.Valid src3274 dst3274 Finset.univ := by decide +kernel

def src3275 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3275 : E → W := ![6,4,3,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3275_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3275_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3275_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3275_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3275_4 : CycleData E W := ⟨3,![7,6,11,18,8],![3,18,14,27,16]⟩
def cycle3275_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3275 : PartitionData E W := ⟨6,![cycle3275_0,cycle3275_1,cycle3275_2,cycle3275_3,cycle3275_4,cycle3275_5]⟩
lemma valid_data3275 : data3275.Valid src3275 dst3275 Finset.univ := by decide +kernel

def src3276 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3276 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3276_0 : CycleData E W := ⟨3,![0,1,10,16,5],![2,6,4,26,16]⟩
def cycle3276_1 : CycleData E W := ⟨3,![2,14,21,8,7],![3,4,28,18,14]⟩
def cycle3276_2 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3276_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3276_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3276_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3276 : PartitionData E W := ⟨6,![cycle3276_0,cycle3276_1,cycle3276_2,cycle3276_3,cycle3276_4,cycle3276_5]⟩
lemma valid_data3276 : data3276.Valid src3276 dst3276 Finset.univ := by decide +kernel

def src3277 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3277 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3277_0 : CycleData E W := ⟨3,![0,1,10,16,5],![2,6,4,26,16]⟩
def cycle3277_1 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3277_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3277_3 : CycleData E W := ⟨3,![6,17,21,8,7],![3,16,38,18,14]⟩
def cycle3277_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3277_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3277 : PartitionData E W := ⟨6,![cycle3277_0,cycle3277_1,cycle3277_2,cycle3277_3,cycle3277_4,cycle3277_5]⟩
lemma valid_data3277 : data3277.Valid src3277 dst3277 Finset.univ := by decide +kernel

def src3278 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3278 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3278_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3278_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3278_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3278_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3278_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3278_5 : CycleData E W := ⟨2,![8,22,18,12],![14,18,38,27]⟩
def data3278 : PartitionData E W := ⟨6,![cycle3278_0,cycle3278_1,cycle3278_2,cycle3278_3,cycle3278_4,cycle3278_5]⟩
lemma valid_data3278 : data3278.Valid src3278 dst3278 Finset.univ := by decide +kernel

def src3279 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3279 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3279_0 : CycleData E W := ⟨2,![0,19,18,5],![2,6,27,16]⟩
def cycle3279_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3279_2 : CycleData E W := ⟨3,![2,14,13,12,7],![3,4,28,27,14]⟩
def cycle3279_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3279_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3279_5 : CycleData E W := ⟨3,![8,21,22,16,11],![14,18,28,38,26]⟩
def data3279 : PartitionData E W := ⟨6,![cycle3279_0,cycle3279_1,cycle3279_2,cycle3279_3,cycle3279_4,cycle3279_5]⟩
lemma valid_data3279 : data3279.Valid src3279 dst3279 Finset.univ := by decide +kernel

def src3280 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3280 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3280_0 : CycleData E W := ⟨4,![0,19,12,7,6,5],![2,6,27,14,3,16]⟩
def cycle3280_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3280_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3280_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3280_4 : CycleData E W := ⟨2,![8,21,16,11],![14,18,38,26]⟩
def cycle3280_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3280 : PartitionData E W := ⟨6,![cycle3280_0,cycle3280_1,cycle3280_2,cycle3280_3,cycle3280_4,cycle3280_5]⟩
lemma valid_data3280 : data3280.Valid src3280 dst3280 Finset.univ := by decide +kernel

def src3281 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3281 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3281_0 : CycleData E W := ⟨2,![0,19,18,5],![2,6,27,16]⟩
def cycle3281_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3281_2 : CycleData E W := ⟨3,![2,14,13,12,7],![3,4,28,27,14]⟩
def cycle3281_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3281_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3281_5 : CycleData E W := ⟨2,![8,22,16,11],![14,18,38,26]⟩
def data3281 : PartitionData E W := ⟨6,![cycle3281_0,cycle3281_1,cycle3281_2,cycle3281_3,cycle3281_4,cycle3281_5]⟩
lemma valid_data3281 : data3281.Valid src3281 dst3281 Finset.univ := by decide +kernel

def src3282 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3282 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3282_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3282_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3282_2 : CycleData E W := ⟨3,![2,14,22,23,3],![3,4,28,38,8]⟩
def cycle3282_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3282_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle3282_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data3282 : PartitionData E W := ⟨6,![cycle3282_0,cycle3282_1,cycle3282_2,cycle3282_3,cycle3282_4,cycle3282_5]⟩
lemma valid_data3282 : data3282.Valid src3282 dst3282 Finset.univ := by decide +kernel

def src3283 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3283 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3283_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3283_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3283_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3283_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3283_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle3283_5 : CycleData E W := ⟨3,![8,21,22,13,12],![14,18,38,28,27]⟩
def data3283 : PartitionData E W := ⟨6,![cycle3283_0,cycle3283_1,cycle3283_2,cycle3283_3,cycle3283_4,cycle3283_5]⟩
lemma valid_data3283 : data3283.Valid src3283 dst3283 Finset.univ := by decide +kernel

def src3284 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3284 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3284_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3284_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3284_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3284_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3284_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle3284_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data3284 : PartitionData E W := ⟨6,![cycle3284_0,cycle3284_1,cycle3284_2,cycle3284_3,cycle3284_4,cycle3284_5]⟩
lemma valid_data3284 : data3284.Valid src3284 dst3284 Finset.univ := by decide +kernel

def src3285 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3285 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3285_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3285_1 : CycleData E W := ⟨4,![3,23,19,15,11,7],![3,8,38,6,26,14]⟩
def cycle3285_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3285_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3285_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3285_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3285 : PartitionData E W := ⟨6,![cycle3285_0,cycle3285_1,cycle3285_2,cycle3285_3,cycle3285_4,cycle3285_5]⟩
lemma valid_data3285 : data3285.Valid src3285 dst3285 Finset.univ := by decide +kernel

def src3286 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3286 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3286_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3286_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3286_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3286_3 : CycleData E W := ⟨3,![15,11,8,21,19],![6,26,14,18,38]⟩
def cycle3286_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3286_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3286 : PartitionData E W := ⟨6,![cycle3286_0,cycle3286_1,cycle3286_2,cycle3286_3,cycle3286_4,cycle3286_5]⟩
lemma valid_data3286 : data3286.Valid src3286 dst3286 Finset.univ := by decide +kernel

def src3287 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3287 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3287_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3287_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3287_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3287_3 : CycleData E W := ⟨3,![3,20,13,17,6],![3,8,28,27,16]⟩
def cycle3287_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3287_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data3287 : PartitionData E W := ⟨6,![cycle3287_0,cycle3287_1,cycle3287_2,cycle3287_3,cycle3287_4,cycle3287_5]⟩
lemma valid_data3287 : data3287.Valid src3287 dst3287 Finset.univ := by decide +kernel

def src3288 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3288 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3288_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3288_1 : CycleData E W := ⟨3,![3,23,16,11,7],![3,8,38,26,14]⟩
def cycle3288_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3288_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3288_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3288_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3288 : PartitionData E W := ⟨6,![cycle3288_0,cycle3288_1,cycle3288_2,cycle3288_3,cycle3288_4,cycle3288_5]⟩
lemma valid_data3288 : data3288.Valid src3288 dst3288 Finset.univ := by decide +kernel

def src3289 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3289 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3289_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3289_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3289_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3289_3 : CycleData E W := ⟨2,![8,21,16,11],![14,18,38,26]⟩
def cycle3289_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3289_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3289 : PartitionData E W := ⟨6,![cycle3289_0,cycle3289_1,cycle3289_2,cycle3289_3,cycle3289_4,cycle3289_5]⟩
lemma valid_data3289 : data3289.Valid src3289 dst3289 Finset.univ := by decide +kernel

def src3290 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3290 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3290_0 : CycleData E W := ⟨3,![0,15,16,17,5],![2,6,26,38,16]⟩
def cycle3290_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3290_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3290_3 : CycleData E W := ⟨3,![3,20,13,18,6],![3,8,28,27,16]⟩
def cycle3290_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3290_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data3290 : PartitionData E W := ⟨6,![cycle3290_0,cycle3290_1,cycle3290_2,cycle3290_3,cycle3290_4,cycle3290_5]⟩
lemma valid_data3290 : data3290.Valid src3290 dst3290 Finset.univ := by decide +kernel

def src3291 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3291 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3291_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3291_1 : CycleData E W := ⟨3,![3,23,18,11,7],![3,8,38,26,14]⟩
def cycle3291_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3291_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3291_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3291_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3291 : PartitionData E W := ⟨6,![cycle3291_0,cycle3291_1,cycle3291_2,cycle3291_3,cycle3291_4,cycle3291_5]⟩
lemma valid_data3291 : data3291.Valid src3291 dst3291 Finset.univ := by decide +kernel

def src3292 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3292 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3292_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3292_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3292_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3292_3 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,26]⟩
def cycle3292_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3292_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3292 : PartitionData E W := ⟨6,![cycle3292_0,cycle3292_1,cycle3292_2,cycle3292_3,cycle3292_4,cycle3292_5]⟩
lemma valid_data3292 : data3292.Valid src3292 dst3292 Finset.univ := by decide +kernel

def src3293 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3293 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3293_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3293_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3293_2 : CycleData E W := ⟨3,![2,14,13,20,3],![3,4,27,28,8]⟩
def cycle3293_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3293_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle3293_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data3293 : PartitionData E W := ⟨6,![cycle3293_0,cycle3293_1,cycle3293_2,cycle3293_3,cycle3293_4,cycle3293_5]⟩
lemma valid_data3293 : data3293.Valid src3293 dst3293 Finset.univ := by decide +kernel

def src3294 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3294 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3294_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3294_1 : CycleData E W := ⟨3,![3,23,18,13,7],![3,8,38,27,14]⟩
def cycle3294_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3294_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3294_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3294_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3294 : PartitionData E W := ⟨6,![cycle3294_0,cycle3294_1,cycle3294_2,cycle3294_3,cycle3294_4,cycle3294_5]⟩
lemma valid_data3294 : data3294.Valid src3294 dst3294 Finset.univ := by decide +kernel

def src3295 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3295 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3295_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3295_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3295_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3295_3 : CycleData E W := ⟨2,![8,21,18,13],![14,18,38,27]⟩
def cycle3295_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3295_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3295 : PartitionData E W := ⟨6,![cycle3295_0,cycle3295_1,cycle3295_2,cycle3295_3,cycle3295_4,cycle3295_5]⟩
lemma valid_data3295 : data3295.Valid src3295 dst3295 Finset.univ := by decide +kernel

def src3296 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3296 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3296_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3296_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3296_2 : CycleData E W := ⟨3,![2,10,11,20,3],![3,4,26,28,8]⟩
def cycle3296_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3296_4 : CycleData E W := ⟨2,![6,17,13,7],![3,16,27,14]⟩
def cycle3296_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data3296 : PartitionData E W := ⟨6,![cycle3296_0,cycle3296_1,cycle3296_2,cycle3296_3,cycle3296_4,cycle3296_5]⟩
lemma valid_data3296 : data3296.Valid src3296 dst3296 Finset.univ := by decide +kernel

def src3297 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3297 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3297_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3297_1 : CycleData E W := ⟨3,![3,23,18,13,7],![3,8,38,27,14]⟩
def cycle3297_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3297_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3297_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3297_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3297 : PartitionData E W := ⟨6,![cycle3297_0,cycle3297_1,cycle3297_2,cycle3297_3,cycle3297_4,cycle3297_5]⟩
lemma valid_data3297 : data3297.Valid src3297 dst3297 Finset.univ := by decide +kernel

def src3298 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3298 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3298_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3298_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3298_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3298_3 : CycleData E W := ⟨2,![8,21,18,13],![14,18,38,27]⟩
def cycle3298_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3298_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3298 : PartitionData E W := ⟨6,![cycle3298_0,cycle3298_1,cycle3298_2,cycle3298_3,cycle3298_4,cycle3298_5]⟩
lemma valid_data3298 : data3298.Valid src3298 dst3298 Finset.univ := by decide +kernel

def src3299 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3299 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3299_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3299_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3299_2 : CycleData E W := ⟨3,![2,10,11,12,7],![3,4,26,28,14]⟩
def cycle3299_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3299_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3299_5 : CycleData E W := ⟨2,![8,22,18,13],![14,18,38,27]⟩
def data3299 : PartitionData E W := ⟨6,![cycle3299_0,cycle3299_1,cycle3299_2,cycle3299_3,cycle3299_4,cycle3299_5]⟩
lemma valid_data3299 : data3299.Valid src3299 dst3299 Finset.univ := by decide +kernel

def src3300 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3300 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3300_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3300_1 : CycleData E W := ⟨4,![3,23,19,15,13,7],![3,8,38,6,27,14]⟩
def cycle3300_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3300_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle3300_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3300_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3300 : PartitionData E W := ⟨6,![cycle3300_0,cycle3300_1,cycle3300_2,cycle3300_3,cycle3300_4,cycle3300_5]⟩
lemma valid_data3300 : data3300.Valid src3300 dst3300 Finset.univ := by decide +kernel

def src3301 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3301 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3301_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,16]⟩
def cycle3301_1 : CycleData E W := ⟨2,![3,23,12,7],![3,8,28,14]⟩
def cycle3301_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3301_3 : CycleData E W := ⟨3,![15,13,8,21,19],![6,27,14,18,38]⟩
def cycle3301_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3301_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3301 : PartitionData E W := ⟨6,![cycle3301_0,cycle3301_1,cycle3301_2,cycle3301_3,cycle3301_4,cycle3301_5]⟩
lemma valid_data3301 : data3301.Valid src3301 dst3301 Finset.univ := by decide +kernel

def src3302 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3302 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3302_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3302_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3302_2 : CycleData E W := ⟨2,![2,14,13,7],![3,4,27,14]⟩
def cycle3302_3 : CycleData E W := ⟨3,![3,20,11,17,6],![3,8,28,26,16]⟩
def cycle3302_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3302_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data3302 : PartitionData E W := ⟨6,![cycle3302_0,cycle3302_1,cycle3302_2,cycle3302_3,cycle3302_4,cycle3302_5]⟩
lemma valid_data3302 : data3302.Valid src3302 dst3302 Finset.univ := by decide +kernel

def src3303 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3303 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3303_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3303_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,27]⟩
def cycle3303_2 : CycleData E W := ⟨3,![2,14,22,23,3],![3,4,28,38,8]⟩
def cycle3303_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3303_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle3303_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def data3303 : PartitionData E W := ⟨6,![cycle3303_0,cycle3303_1,cycle3303_2,cycle3303_3,cycle3303_4,cycle3303_5]⟩
lemma valid_data3303 : data3303.Valid src3303 dst3303 Finset.univ := by decide +kernel

def src3304 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3304 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3304_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3304_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,27]⟩
def cycle3304_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3304_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3304_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle3304_5 : CycleData E W := ⟨3,![8,21,22,13,12],![14,18,38,28,26]⟩
def data3304 : PartitionData E W := ⟨6,![cycle3304_0,cycle3304_1,cycle3304_2,cycle3304_3,cycle3304_4,cycle3304_5]⟩
lemma valid_data3304 : data3304.Valid src3304 dst3304 Finset.univ := by decide +kernel

def src3305 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3305 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3305_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3305_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,27]⟩
def cycle3305_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3305_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3305_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle3305_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def data3305 : PartitionData E W := ⟨6,![cycle3305_0,cycle3305_1,cycle3305_2,cycle3305_3,cycle3305_4,cycle3305_5]⟩
lemma valid_data3305 : data3305.Valid src3305 dst3305 Finset.univ := by decide +kernel

def src3306 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3306 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3306_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3306_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3306_2 : CycleData E W := ⟨3,![2,14,13,12,7],![3,4,28,26,14]⟩
def cycle3306_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3306_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3306_5 : CycleData E W := ⟨3,![8,21,22,18,11],![14,18,28,38,27]⟩
def data3306 : PartitionData E W := ⟨6,![cycle3306_0,cycle3306_1,cycle3306_2,cycle3306_3,cycle3306_4,cycle3306_5]⟩
lemma valid_data3306 : data3306.Valid src3306 dst3306 Finset.univ := by decide +kernel

def src3307 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3307 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3307_0 : CycleData E W := ⟨4,![0,15,12,7,6,5],![2,6,26,14,3,16]⟩
def cycle3307_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3307_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3307_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3307_4 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle3307_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data3307 : PartitionData E W := ⟨6,![cycle3307_0,cycle3307_1,cycle3307_2,cycle3307_3,cycle3307_4,cycle3307_5]⟩
lemma valid_data3307 : data3307.Valid src3307 dst3307 Finset.univ := by decide +kernel

def src3308 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3308 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3308_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3308_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3308_2 : CycleData E W := ⟨3,![2,14,13,12,7],![3,4,28,26,14]⟩
def cycle3308_3 : CycleData E W := ⟨2,![3,23,17,6],![3,8,38,16]⟩
def cycle3308_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3308_5 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def data3308 : PartitionData E W := ⟨6,![cycle3308_0,cycle3308_1,cycle3308_2,cycle3308_3,cycle3308_4,cycle3308_5]⟩
lemma valid_data3308 : data3308.Valid src3308 dst3308 Finset.univ := by decide +kernel

def src3309 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3309 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3309_0 : CycleData E W := ⟨3,![0,15,12,8,9],![2,6,26,14,18]⟩
def cycle3309_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3309_2 : CycleData E W := ⟨3,![2,14,21,20,3],![3,4,28,18,8]⟩
def cycle3309_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3309_4 : CycleData E W := ⟨2,![6,18,11,7],![3,16,27,14]⟩
def cycle3309_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3309 : PartitionData E W := ⟨6,![cycle3309_0,cycle3309_1,cycle3309_2,cycle3309_3,cycle3309_4,cycle3309_5]⟩
lemma valid_data3309 : data3309.Valid src3309 dst3309 Finset.univ := by decide +kernel

def src3310 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3310 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3310_0 : CycleData E W := ⟨4,![0,15,12,7,6,5],![2,6,26,14,3,16]⟩
def cycle3310_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3310_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3310_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3310_4 : CycleData E W := ⟨3,![8,21,17,18,11],![14,18,38,16,27]⟩
def cycle3310_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3310 : PartitionData E W := ⟨6,![cycle3310_0,cycle3310_1,cycle3310_2,cycle3310_3,cycle3310_4,cycle3310_5]⟩
lemma valid_data3310 : data3310.Valid src3310 dst3310 Finset.univ := by decide +kernel

def src3311 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3311 : E → W := ![6,4,3,8,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3311_0 : CycleData E W := ⟨3,![0,15,12,8,9],![2,6,26,14,18]⟩
def cycle3311_1 : CycleData E W := ⟨1,![1,19,10],![4,6,27]⟩
def cycle3311_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3311_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3311_4 : CycleData E W := ⟨2,![6,18,11,7],![3,16,27,14]⟩
def cycle3311_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3311 : PartitionData E W := ⟨6,![cycle3311_0,cycle3311_1,cycle3311_2,cycle3311_3,cycle3311_4,cycle3311_5]⟩
lemma valid_data3311 : data3311.Valid src3311 dst3311 Finset.univ := by decide +kernel

def lookupB16 (j : ℕ) : PartitionData E W := (if j < 56 then (if j < 28 then (if j < 14 then (if j < 7 then (if j < 3 then (if j < 1 then data3200 else (if j < 2 then data3201 else data3202)) else (if j < 5 then (if j < 4 then data3203 else data3204) else (if j < 6 then data3205 else data3206))) else (if j < 10 then (if j < 8 then data3207 else (if j < 9 then data3208 else data3209)) else (if j < 12 then (if j < 11 then data3210 else data3211) else (if j < 13 then data3212 else data3213)))) else (if j < 21 then (if j < 17 then (if j < 15 then data3214 else (if j < 16 then data3215 else data3216)) else (if j < 19 then (if j < 18 then data3217 else data3218) else (if j < 20 then data3219 else data3220))) else (if j < 24 then (if j < 22 then data3221 else (if j < 23 then data3222 else data3223)) else (if j < 26 then (if j < 25 then data3224 else data3225) else (if j < 27 then data3226 else data3227))))) else (if j < 42 then (if j < 35 then (if j < 31 then (if j < 29 then data3228 else (if j < 30 then data3229 else data3230)) else (if j < 33 then (if j < 32 then data3231 else data3232) else (if j < 34 then data3233 else data3234))) else (if j < 38 then (if j < 36 then data3235 else (if j < 37 then data3236 else data3237)) else (if j < 40 then (if j < 39 then data3238 else data3239) else (if j < 41 then data3240 else data3241)))) else (if j < 49 then (if j < 45 then (if j < 43 then data3242 else (if j < 44 then data3243 else data3244)) else (if j < 47 then (if j < 46 then data3245 else data3246) else (if j < 48 then data3247 else data3248))) else (if j < 52 then (if j < 50 then data3249 else (if j < 51 then data3250 else data3251)) else (if j < 54 then (if j < 53 then data3252 else data3253) else (if j < 55 then data3254 else data3255)))))) else (if j < 84 then (if j < 70 then (if j < 63 then (if j < 59 then (if j < 57 then data3256 else (if j < 58 then data3257 else data3258)) else (if j < 61 then (if j < 60 then data3259 else data3260) else (if j < 62 then data3261 else data3262))) else (if j < 66 then (if j < 64 then data3263 else (if j < 65 then data3264 else data3265)) else (if j < 68 then (if j < 67 then data3266 else data3267) else (if j < 69 then data3268 else data3269)))) else (if j < 77 then (if j < 73 then (if j < 71 then data3270 else (if j < 72 then data3271 else data3272)) else (if j < 75 then (if j < 74 then data3273 else data3274) else (if j < 76 then data3275 else data3276))) else (if j < 80 then (if j < 78 then data3277 else (if j < 79 then data3278 else data3279)) else (if j < 82 then (if j < 81 then data3280 else data3281) else (if j < 83 then data3282 else data3283))))) else (if j < 98 then (if j < 91 then (if j < 87 then (if j < 85 then data3284 else (if j < 86 then data3285 else data3286)) else (if j < 89 then (if j < 88 then data3287 else data3288) else (if j < 90 then data3289 else data3290))) else (if j < 94 then (if j < 92 then data3291 else (if j < 93 then data3292 else data3293)) else (if j < 96 then (if j < 95 then data3294 else data3295) else (if j < 97 then data3296 else data3297)))) else (if j < 105 then (if j < 101 then (if j < 99 then data3298 else (if j < 100 then data3299 else data3300)) else (if j < 103 then (if j < 102 then data3301 else data3302) else (if j < 104 then data3303 else data3304))) else (if j < 108 then (if j < 106 then data3305 else (if j < 107 then data3306 else data3307)) else (if j < 110 then (if j < 109 then data3308 else data3309) else (if j < 111 then data3310 else data3311)))))))

def srcTableB16 (j : ℕ) : E → W := (if j < 56 then (if j < 28 then (if j < 14 then (if j < 7 then (if j < 3 then (if j < 1 then src3200 else (if j < 2 then src3201 else src3202)) else (if j < 5 then (if j < 4 then src3203 else src3204) else (if j < 6 then src3205 else src3206))) else (if j < 10 then (if j < 8 then src3207 else (if j < 9 then src3208 else src3209)) else (if j < 12 then (if j < 11 then src3210 else src3211) else (if j < 13 then src3212 else src3213)))) else (if j < 21 then (if j < 17 then (if j < 15 then src3214 else (if j < 16 then src3215 else src3216)) else (if j < 19 then (if j < 18 then src3217 else src3218) else (if j < 20 then src3219 else src3220))) else (if j < 24 then (if j < 22 then src3221 else (if j < 23 then src3222 else src3223)) else (if j < 26 then (if j < 25 then src3224 else src3225) else (if j < 27 then src3226 else src3227))))) else (if j < 42 then (if j < 35 then (if j < 31 then (if j < 29 then src3228 else (if j < 30 then src3229 else src3230)) else (if j < 33 then (if j < 32 then src3231 else src3232) else (if j < 34 then src3233 else src3234))) else (if j < 38 then (if j < 36 then src3235 else (if j < 37 then src3236 else src3237)) else (if j < 40 then (if j < 39 then src3238 else src3239) else (if j < 41 then src3240 else src3241)))) else (if j < 49 then (if j < 45 then (if j < 43 then src3242 else (if j < 44 then src3243 else src3244)) else (if j < 47 then (if j < 46 then src3245 else src3246) else (if j < 48 then src3247 else src3248))) else (if j < 52 then (if j < 50 then src3249 else (if j < 51 then src3250 else src3251)) else (if j < 54 then (if j < 53 then src3252 else src3253) else (if j < 55 then src3254 else src3255)))))) else (if j < 84 then (if j < 70 then (if j < 63 then (if j < 59 then (if j < 57 then src3256 else (if j < 58 then src3257 else src3258)) else (if j < 61 then (if j < 60 then src3259 else src3260) else (if j < 62 then src3261 else src3262))) else (if j < 66 then (if j < 64 then src3263 else (if j < 65 then src3264 else src3265)) else (if j < 68 then (if j < 67 then src3266 else src3267) else (if j < 69 then src3268 else src3269)))) else (if j < 77 then (if j < 73 then (if j < 71 then src3270 else (if j < 72 then src3271 else src3272)) else (if j < 75 then (if j < 74 then src3273 else src3274) else (if j < 76 then src3275 else src3276))) else (if j < 80 then (if j < 78 then src3277 else (if j < 79 then src3278 else src3279)) else (if j < 82 then (if j < 81 then src3280 else src3281) else (if j < 83 then src3282 else src3283))))) else (if j < 98 then (if j < 91 then (if j < 87 then (if j < 85 then src3284 else (if j < 86 then src3285 else src3286)) else (if j < 89 then (if j < 88 then src3287 else src3288) else (if j < 90 then src3289 else src3290))) else (if j < 94 then (if j < 92 then src3291 else (if j < 93 then src3292 else src3293)) else (if j < 96 then (if j < 95 then src3294 else src3295) else (if j < 97 then src3296 else src3297)))) else (if j < 105 then (if j < 101 then (if j < 99 then src3298 else (if j < 100 then src3299 else src3300)) else (if j < 103 then (if j < 102 then src3301 else src3302) else (if j < 104 then src3303 else src3304))) else (if j < 108 then (if j < 106 then src3305 else (if j < 107 then src3306 else src3307)) else (if j < 110 then (if j < 109 then src3308 else src3309) else (if j < 111 then src3310 else src3311)))))))

def dstTableB16 (j : ℕ) : E → W := (if j < 56 then (if j < 28 then (if j < 14 then (if j < 7 then (if j < 3 then (if j < 1 then dst3200 else (if j < 2 then dst3201 else dst3202)) else (if j < 5 then (if j < 4 then dst3203 else dst3204) else (if j < 6 then dst3205 else dst3206))) else (if j < 10 then (if j < 8 then dst3207 else (if j < 9 then dst3208 else dst3209)) else (if j < 12 then (if j < 11 then dst3210 else dst3211) else (if j < 13 then dst3212 else dst3213)))) else (if j < 21 then (if j < 17 then (if j < 15 then dst3214 else (if j < 16 then dst3215 else dst3216)) else (if j < 19 then (if j < 18 then dst3217 else dst3218) else (if j < 20 then dst3219 else dst3220))) else (if j < 24 then (if j < 22 then dst3221 else (if j < 23 then dst3222 else dst3223)) else (if j < 26 then (if j < 25 then dst3224 else dst3225) else (if j < 27 then dst3226 else dst3227))))) else (if j < 42 then (if j < 35 then (if j < 31 then (if j < 29 then dst3228 else (if j < 30 then dst3229 else dst3230)) else (if j < 33 then (if j < 32 then dst3231 else dst3232) else (if j < 34 then dst3233 else dst3234))) else (if j < 38 then (if j < 36 then dst3235 else (if j < 37 then dst3236 else dst3237)) else (if j < 40 then (if j < 39 then dst3238 else dst3239) else (if j < 41 then dst3240 else dst3241)))) else (if j < 49 then (if j < 45 then (if j < 43 then dst3242 else (if j < 44 then dst3243 else dst3244)) else (if j < 47 then (if j < 46 then dst3245 else dst3246) else (if j < 48 then dst3247 else dst3248))) else (if j < 52 then (if j < 50 then dst3249 else (if j < 51 then dst3250 else dst3251)) else (if j < 54 then (if j < 53 then dst3252 else dst3253) else (if j < 55 then dst3254 else dst3255)))))) else (if j < 84 then (if j < 70 then (if j < 63 then (if j < 59 then (if j < 57 then dst3256 else (if j < 58 then dst3257 else dst3258)) else (if j < 61 then (if j < 60 then dst3259 else dst3260) else (if j < 62 then dst3261 else dst3262))) else (if j < 66 then (if j < 64 then dst3263 else (if j < 65 then dst3264 else dst3265)) else (if j < 68 then (if j < 67 then dst3266 else dst3267) else (if j < 69 then dst3268 else dst3269)))) else (if j < 77 then (if j < 73 then (if j < 71 then dst3270 else (if j < 72 then dst3271 else dst3272)) else (if j < 75 then (if j < 74 then dst3273 else dst3274) else (if j < 76 then dst3275 else dst3276))) else (if j < 80 then (if j < 78 then dst3277 else (if j < 79 then dst3278 else dst3279)) else (if j < 82 then (if j < 81 then dst3280 else dst3281) else (if j < 83 then dst3282 else dst3283))))) else (if j < 98 then (if j < 91 then (if j < 87 then (if j < 85 then dst3284 else (if j < 86 then dst3285 else dst3286)) else (if j < 89 then (if j < 88 then dst3287 else dst3288) else (if j < 90 then dst3289 else dst3290))) else (if j < 94 then (if j < 92 then dst3291 else (if j < 93 then dst3292 else dst3293)) else (if j < 96 then (if j < 95 then dst3294 else dst3295) else (if j < 97 then dst3296 else dst3297)))) else (if j < 105 then (if j < 101 then (if j < 99 then dst3298 else (if j < 100 then dst3299 else dst3300)) else (if j < 103 then (if j < 102 then dst3301 else dst3302) else (if j < 104 then dst3303 else dst3304))) else (if j < 108 then (if j < 106 then dst3305 else (if j < 107 then dst3306 else dst3307)) else (if j < 110 then (if j < 109 then dst3308 else dst3309) else (if j < 111 then dst3310 else dst3311)))))))

def caseB16 (i : Fin 112) : Cases := ⟨3200 + i.val,by have := i.isLt; omega⟩
lemma tableB16_valid (i : Fin 112) :
    (lookupB16 i.val).Valid (srcTableB16 i.val) (dstTableB16 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data3200
  · exact valid_data3201
  · exact valid_data3202
  · exact valid_data3203
  · exact valid_data3204
  · exact valid_data3205
  · exact valid_data3206
  · exact valid_data3207
  · exact valid_data3208
  · exact valid_data3209
  · exact valid_data3210
  · exact valid_data3211
  · exact valid_data3212
  · exact valid_data3213
  · exact valid_data3214
  · exact valid_data3215
  · exact valid_data3216
  · exact valid_data3217
  · exact valid_data3218
  · exact valid_data3219
  · exact valid_data3220
  · exact valid_data3221
  · exact valid_data3222
  · exact valid_data3223
  · exact valid_data3224
  · exact valid_data3225
  · exact valid_data3226
  · exact valid_data3227
  · exact valid_data3228
  · exact valid_data3229
  · exact valid_data3230
  · exact valid_data3231
  · exact valid_data3232
  · exact valid_data3233
  · exact valid_data3234
  · exact valid_data3235
  · exact valid_data3236
  · exact valid_data3237
  · exact valid_data3238
  · exact valid_data3239
  · exact valid_data3240
  · exact valid_data3241
  · exact valid_data3242
  · exact valid_data3243
  · exact valid_data3244
  · exact valid_data3245
  · exact valid_data3246
  · exact valid_data3247
  · exact valid_data3248
  · exact valid_data3249
  · exact valid_data3250
  · exact valid_data3251
  · exact valid_data3252
  · exact valid_data3253
  · exact valid_data3254
  · exact valid_data3255
  · exact valid_data3256
  · exact valid_data3257
  · exact valid_data3258
  · exact valid_data3259
  · exact valid_data3260
  · exact valid_data3261
  · exact valid_data3262
  · exact valid_data3263
  · exact valid_data3264
  · exact valid_data3265
  · exact valid_data3266
  · exact valid_data3267
  · exact valid_data3268
  · exact valid_data3269
  · exact valid_data3270
  · exact valid_data3271
  · exact valid_data3272
  · exact valid_data3273
  · exact valid_data3274
  · exact valid_data3275
  · exact valid_data3276
  · exact valid_data3277
  · exact valid_data3278
  · exact valid_data3279
  · exact valid_data3280
  · exact valid_data3281
  · exact valid_data3282
  · exact valid_data3283
  · exact valid_data3284
  · exact valid_data3285
  · exact valid_data3286
  · exact valid_data3287
  · exact valid_data3288
  · exact valid_data3289
  · exact valid_data3290
  · exact valid_data3291
  · exact valid_data3292
  · exact valid_data3293
  · exact valid_data3294
  · exact valid_data3295
  · exact valid_data3296
  · exact valid_data3297
  · exact valid_data3298
  · exact valid_data3299
  · exact valid_data3300
  · exact valid_data3301
  · exact valid_data3302
  · exact valid_data3303
  · exact valid_data3304
  · exact valid_data3305
  · exact valid_data3306
  · exact valid_data3307
  · exact valid_data3308
  · exact valid_data3309
  · exact valid_data3310
  · exact valid_data3311

lemma srcB16_row : ∀ (i : Fin 112) (e : E),
    srcTableB16 i.val e = caseSource (caseB16 i) e := by decide +kernel

lemma dstB16_row : ∀ (i : Fin 112) (e : E),
    dstTableB16 i.val e = caseTarget (caseB16 i) e := by decide +kernel

lemma sizeB16 : ∀ i : Fin 112, (lookupB16 i.val).size ≤ 5 →
    (lookupB16 i.val).size = 2 ∧
      (⟨caseKey (caseB16 i),caseKey_lt (caseB16 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB16 (i : Fin 112) : Certificate (caseB16 i) := by
  refine ⟨lookupB16 i.val,?_,sizeB16 i⟩
  have hv := tableB16_valid i
  rw [funext (srcB16_row i),funext (dstB16_row i)] at hv
  exact hv
lemma certificateInterval16 : FiniteIntervals.Covers CertificateAt 3200 3312 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 3200 112 (fun i _ => certificateB16 i)
#print axioms certificateInterval16
end Erdos184Work.FiveRows3

import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1200 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst1200 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1200_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1200_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1200_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1200_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle1200_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle1200_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data1200 : PartitionData E W := ⟨6,![cycle1200_0,cycle1200_1,cycle1200_2,cycle1200_3,cycle1200_4,cycle1200_5]⟩
lemma valid_data1200 : data1200.Valid src1200 dst1200 Finset.univ := by decide +kernel

def src1201 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst1201 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1201_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1201_1 : CycleData E W := ⟨3,![2,23,13,18,7],![3,8,28,27,16]⟩
def cycle1201_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1201_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1201_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle1201_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data1201 : PartitionData E W := ⟨6,![cycle1201_0,cycle1201_1,cycle1201_2,cycle1201_3,cycle1201_4,cycle1201_5]⟩
lemma valid_data1201 : data1201.Valid src1201 dst1201 Finset.univ := by decide +kernel

def src1202 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst1202 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1202_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1202_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle1202_2 : CycleData E W := ⟨3,![2,3,15,11,6],![3,8,6,26,14]⟩
def cycle1202_3 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1202_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1202_5 : CycleData E W := ⟨2,![20,12,16,23],![8,28,26,38]⟩
def data1202 : PartitionData E W := ⟨6,![cycle1202_0,cycle1202_1,cycle1202_2,cycle1202_3,cycle1202_4,cycle1202_5]⟩
lemma valid_data1202 : data1202.Valid src1202 dst1202 Finset.univ := by decide +kernel

def src1203 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst1203 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1203_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1203_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1203_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1203_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1203_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle1203_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data1203 : PartitionData E W := ⟨6,![cycle1203_0,cycle1203_1,cycle1203_2,cycle1203_3,cycle1203_4,cycle1203_5]⟩
lemma valid_data1203 : data1203.Valid src1203 dst1203 Finset.univ := by decide +kernel

def src1204 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst1204 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1204_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1204_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1204_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1204_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1204_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle1204_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data1204 : PartitionData E W := ⟨6,![cycle1204_0,cycle1204_1,cycle1204_2,cycle1204_3,cycle1204_4,cycle1204_5]⟩
lemma valid_data1204 : data1204.Valid src1204 dst1204 Finset.univ := by decide +kernel

def src1205 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst1205 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1205_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1205_1 : CycleData E W := ⟨3,![1,14,15,3,2],![3,4,27,6,8]⟩
def cycle1205_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1205_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,26,16]⟩
def cycle1205_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle1205_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,26,38]⟩
def data1205 : PartitionData E W := ⟨6,![cycle1205_0,cycle1205_1,cycle1205_2,cycle1205_3,cycle1205_4,cycle1205_5]⟩
lemma valid_data1205 : data1205.Valid src1205 dst1205 Finset.univ := by decide +kernel

def src1206 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst1206 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1206_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1206_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1206_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1206_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1206_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1206_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1206 : PartitionData E W := ⟨6,![cycle1206_0,cycle1206_1,cycle1206_2,cycle1206_3,cycle1206_4,cycle1206_5]⟩
lemma valid_data1206 : data1206.Valid src1206 dst1206 Finset.univ := by decide +kernel

def src1207 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst1207 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1207_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1207_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1207_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1207_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1207_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1207_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1207 : PartitionData E W := ⟨6,![cycle1207_0,cycle1207_1,cycle1207_2,cycle1207_3,cycle1207_4,cycle1207_5]⟩
lemma valid_data1207 : data1207.Valid src1207 dst1207 Finset.univ := by decide +kernel

def src1208 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst1208 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1208_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1208_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1208_2 : CycleData E W := ⟨3,![3,23,18,12,15],![6,8,38,27,26]⟩
def cycle1208_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1208_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle1208_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data1208 : PartitionData E W := ⟨6,![cycle1208_0,cycle1208_1,cycle1208_2,cycle1208_3,cycle1208_4,cycle1208_5]⟩
lemma valid_data1208 : data1208.Valid src1208 dst1208 Finset.univ := by decide +kernel

def src1209 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst1209 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1209_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1209_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1209_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1209_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1209_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1209_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data1209 : PartitionData E W := ⟨6,![cycle1209_0,cycle1209_1,cycle1209_2,cycle1209_3,cycle1209_4,cycle1209_5]⟩
lemma valid_data1209 : data1209.Valid src1209 dst1209 Finset.univ := by decide +kernel

def src1210 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst1210 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1210_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1210_1 : CycleData E W := ⟨3,![2,23,13,16,7],![3,8,28,26,16]⟩
def cycle1210_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1210_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1210_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1210_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data1210 : PartitionData E W := ⟨6,![cycle1210_0,cycle1210_1,cycle1210_2,cycle1210_3,cycle1210_4,cycle1210_5]⟩
lemma valid_data1210 : data1210.Valid src1210 dst1210 Finset.univ := by decide +kernel

def src1211 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst1211 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1211_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1211_1 : CycleData E W := ⟨3,![1,14,13,16,7],![3,4,28,26,16]⟩
def cycle1211_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,27,14]⟩
def cycle1211_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,6,8,28,18]⟩
def cycle1211_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1211_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data1211 : PartitionData E W := ⟨6,![cycle1211_0,cycle1211_1,cycle1211_2,cycle1211_3,cycle1211_4,cycle1211_5]⟩
lemma valid_data1211 : data1211.Valid src1211 dst1211 Finset.univ := by decide +kernel

def src1212 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst1212 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle1212_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1212_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1212_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1212_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1212_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle1212_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1212 : PartitionData E W := ⟨6,![cycle1212_0,cycle1212_1,cycle1212_2,cycle1212_3,cycle1212_4,cycle1212_5]⟩
lemma valid_data1212 : data1212.Valid src1212 dst1212 Finset.univ := by decide +kernel

def src1213 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst1213 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle1213_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1213_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1213_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1213_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1213_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle1213_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1213 : PartitionData E W := ⟨6,![cycle1213_0,cycle1213_1,cycle1213_2,cycle1213_3,cycle1213_4,cycle1213_5]⟩
lemma valid_data1213 : data1213.Valid src1213 dst1213 Finset.univ := by decide +kernel

def src1214 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst1214 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle1214_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1214_1 : CycleData E W := ⟨3,![1,14,15,3,2],![3,4,26,6,8]⟩
def cycle1214_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1214_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle1214_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1214_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data1214 : PartitionData E W := ⟨6,![cycle1214_0,cycle1214_1,cycle1214_2,cycle1214_3,cycle1214_4,cycle1214_5]⟩
lemma valid_data1214 : data1214.Valid src1214 dst1214 Finset.univ := by decide +kernel

def src1215 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst1215 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle1215_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1215_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1215_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1215_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1215_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle1215_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1215 : PartitionData E W := ⟨6,![cycle1215_0,cycle1215_1,cycle1215_2,cycle1215_3,cycle1215_4,cycle1215_5]⟩
lemma valid_data1215 : data1215.Valid src1215 dst1215 Finset.univ := by decide +kernel

def src1216 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst1216 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle1216_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1216_1 : CycleData E W := ⟨3,![2,23,13,16,7],![3,8,28,26,16]⟩
def cycle1216_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1216_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1216_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle1216_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1216 : PartitionData E W := ⟨6,![cycle1216_0,cycle1216_1,cycle1216_2,cycle1216_3,cycle1216_4,cycle1216_5]⟩
lemma valid_data1216 : data1216.Valid src1216 dst1216 Finset.univ := by decide +kernel

def src1217 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst1217 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle1217_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1217_1 : CycleData E W := ⟨2,![1,14,16,7],![3,4,26,16]⟩
def cycle1217_2 : CycleData E W := ⟨3,![2,3,19,11,6],![3,8,6,27,14]⟩
def cycle1217_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1217_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1217_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data1217 : PartitionData E W := ⟨6,![cycle1217_0,cycle1217_1,cycle1217_2,cycle1217_3,cycle1217_4,cycle1217_5]⟩
lemma valid_data1217 : data1217.Valid src1217 dst1217 Finset.univ := by decide +kernel

def src1218 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst1218 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle1218_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1218_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1218_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1218_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle1218_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle1218_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1218 : PartitionData E W := ⟨6,![cycle1218_0,cycle1218_1,cycle1218_2,cycle1218_3,cycle1218_4,cycle1218_5]⟩
lemma valid_data1218 : data1218.Valid src1218 dst1218 Finset.univ := by decide +kernel

def src1219 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst1219 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle1219_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1219_1 : CycleData E W := ⟨3,![2,23,12,18,7],![3,8,28,27,16]⟩
def cycle1219_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1219_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1219_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle1219_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1219 : PartitionData E W := ⟨6,![cycle1219_0,cycle1219_1,cycle1219_2,cycle1219_3,cycle1219_4,cycle1219_5]⟩
lemma valid_data1219 : data1219.Valid src1219 dst1219 Finset.univ := by decide +kernel

def src1220 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst1220 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle1220_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1220_1 : CycleData E W := ⟨3,![1,14,15,3,2],![3,4,26,6,8]⟩
def cycle1220_2 : CycleData E W := ⟨3,![4,19,12,21,9],![2,6,27,28,18]⟩
def cycle1220_3 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle1220_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1220_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data1220 : PartitionData E W := ⟨6,![cycle1220_0,cycle1220_1,cycle1220_2,cycle1220_3,cycle1220_4,cycle1220_5]⟩
lemma valid_data1220 : data1220.Valid src1220 dst1220 Finset.univ := by decide +kernel

def src1221 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst1221 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle1221_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1221_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1221_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1221_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1221_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle1221_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1221 : PartitionData E W := ⟨6,![cycle1221_0,cycle1221_1,cycle1221_2,cycle1221_3,cycle1221_4,cycle1221_5]⟩
lemma valid_data1221 : data1221.Valid src1221 dst1221 Finset.univ := by decide +kernel

def src1222 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst1222 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle1222_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1222_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1222_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle1222_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1222_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle1222_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1222 : PartitionData E W := ⟨6,![cycle1222_0,cycle1222_1,cycle1222_2,cycle1222_3,cycle1222_4,cycle1222_5]⟩
lemma valid_data1222 : data1222.Valid src1222 dst1222 Finset.univ := by decide +kernel

def src1223 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst1223 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle1223_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1223_1 : CycleData E W := ⟨2,![1,14,17,7],![3,4,26,16]⟩
def cycle1223_2 : CycleData E W := ⟨3,![2,3,15,11,6],![3,8,6,27,14]⟩
def cycle1223_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1223_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle1223_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data1223 : PartitionData E W := ⟨6,![cycle1223_0,cycle1223_1,cycle1223_2,cycle1223_3,cycle1223_4,cycle1223_5]⟩
lemma valid_data1223 : data1223.Valid src1223 dst1223 Finset.univ := by decide +kernel

def src1224 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst1224 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle1224_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1224_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1224_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1224_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1224_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1224_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1224 : PartitionData E W := ⟨6,![cycle1224_0,cycle1224_1,cycle1224_2,cycle1224_3,cycle1224_4,cycle1224_5]⟩
lemma valid_data1224 : data1224.Valid src1224 dst1224 Finset.univ := by decide +kernel

def src1225 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst1225 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle1225_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1225_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1225_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1225_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1225_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1225_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1225 : PartitionData E W := ⟨6,![cycle1225_0,cycle1225_1,cycle1225_2,cycle1225_3,cycle1225_4,cycle1225_5]⟩
lemma valid_data1225 : data1225.Valid src1225 dst1225 Finset.univ := by decide +kernel

def src1226 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst1226 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle1226_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1226_1 : CycleData E W := ⟨3,![1,14,13,16,7],![3,4,27,26,16]⟩
def cycle1226_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle1226_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1226_4 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1226_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data1226 : PartitionData E W := ⟨6,![cycle1226_0,cycle1226_1,cycle1226_2,cycle1226_3,cycle1226_4,cycle1226_5]⟩
lemma valid_data1226 : data1226.Valid src1226 dst1226 Finset.univ := by decide +kernel

def src1227 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst1227 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle1227_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1227_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1227_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1227_3 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle1227_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1227_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1227 : PartitionData E W := ⟨6,![cycle1227_0,cycle1227_1,cycle1227_2,cycle1227_3,cycle1227_4,cycle1227_5]⟩
lemma valid_data1227 : data1227.Valid src1227 dst1227 Finset.univ := by decide +kernel

def src1228 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst1228 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle1228_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1228_1 : CycleData E W := ⟨3,![2,23,12,16,7],![3,8,28,26,16]⟩
def cycle1228_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1228_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1228_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1228_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1228 : PartitionData E W := ⟨6,![cycle1228_0,cycle1228_1,cycle1228_2,cycle1228_3,cycle1228_4,cycle1228_5]⟩
lemma valid_data1228 : data1228.Valid src1228 dst1228 Finset.univ := by decide +kernel

def src1229 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst1229 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle1229_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1229_1 : CycleData E W := ⟨3,![1,14,13,16,7],![3,4,27,26,16]⟩
def cycle1229_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle1229_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1229_4 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1229_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1229 : PartitionData E W := ⟨6,![cycle1229_0,cycle1229_1,cycle1229_2,cycle1229_3,cycle1229_4,cycle1229_5]⟩
lemma valid_data1229 : data1229.Valid src1229 dst1229 Finset.univ := by decide +kernel

def src1230 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst1230 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle1230_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1230_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1230_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1230_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle1230_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle1230_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1230 : PartitionData E W := ⟨6,![cycle1230_0,cycle1230_1,cycle1230_2,cycle1230_3,cycle1230_4,cycle1230_5]⟩
lemma valid_data1230 : data1230.Valid src1230 dst1230 Finset.univ := by decide +kernel

def src1231 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst1231 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle1231_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1231_1 : CycleData E W := ⟨3,![2,23,12,18,7],![3,8,28,27,16]⟩
def cycle1231_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1231_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1231_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle1231_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1231 : PartitionData E W := ⟨6,![cycle1231_0,cycle1231_1,cycle1231_2,cycle1231_3,cycle1231_4,cycle1231_5]⟩
lemma valid_data1231 : data1231.Valid src1231 dst1231 Finset.univ := by decide +kernel

def src1232 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst1232 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle1232_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1232_1 : CycleData E W := ⟨3,![1,14,16,17,7],![3,4,26,38,16]⟩
def cycle1232_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle1232_3 : CycleData E W := ⟨3,![4,3,23,22,9],![2,6,8,38,18]⟩
def cycle1232_4 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle1232_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1232 : PartitionData E W := ⟨6,![cycle1232_0,cycle1232_1,cycle1232_2,cycle1232_3,cycle1232_4,cycle1232_5]⟩
lemma valid_data1232 : data1232.Valid src1232 dst1232 Finset.univ := by decide +kernel

def src1233 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst1233 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle1233_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1233_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1233_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1233_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1233_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle1233_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1233 : PartitionData E W := ⟨6,![cycle1233_0,cycle1233_1,cycle1233_2,cycle1233_3,cycle1233_4,cycle1233_5]⟩
lemma valid_data1233 : data1233.Valid src1233 dst1233 Finset.univ := by decide +kernel

def src1234 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst1234 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle1234_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1234_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1234_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle1234_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1234_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle1234_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1234 : PartitionData E W := ⟨6,![cycle1234_0,cycle1234_1,cycle1234_2,cycle1234_3,cycle1234_4,cycle1234_5]⟩
lemma valid_data1234 : data1234.Valid src1234 dst1234 Finset.univ := by decide +kernel

def src1235 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst1235 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle1235_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1235_1 : CycleData E W := ⟨3,![1,14,13,16,7],![3,4,26,27,16]⟩
def cycle1235_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle1235_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1235_4 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1235_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data1235 : PartitionData E W := ⟨6,![cycle1235_0,cycle1235_1,cycle1235_2,cycle1235_3,cycle1235_4,cycle1235_5]⟩
lemma valid_data1235 : data1235.Valid src1235 dst1235 Finset.univ := by decide +kernel

def src1236 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst1236 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle1236_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,28,18]⟩
def cycle1236_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle1236_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1236_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1236_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle1236_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1236 : PartitionData E W := ⟨6,![cycle1236_0,cycle1236_1,cycle1236_2,cycle1236_3,cycle1236_4,cycle1236_5]⟩
lemma valid_data1236 : data1236.Valid src1236 dst1236 Finset.univ := by decide +kernel

def src1237 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst1237 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle1237_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1237_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1237_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1237_3 : CycleData E W := ⟨3,![6,12,19,15,7],![3,14,27,6,16]⟩
def cycle1237_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle1237_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1237 : PartitionData E W := ⟨6,![cycle1237_0,cycle1237_1,cycle1237_2,cycle1237_3,cycle1237_4,cycle1237_5]⟩
lemma valid_data1237 : data1237.Valid src1237 dst1237 Finset.univ := by decide +kernel

def src1238 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst1238 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle1238_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,28,18]⟩
def cycle1238_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle1238_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1238_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1238_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle1238_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data1238 : PartitionData E W := ⟨6,![cycle1238_0,cycle1238_1,cycle1238_2,cycle1238_3,cycle1238_4,cycle1238_5]⟩
lemma valid_data1238 : data1238.Valid src1238 dst1238 Finset.univ := by decide +kernel

def src1239 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst1239 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle1239_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1239_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1239_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle1239_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle1239_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1239_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1239 : PartitionData E W := ⟨6,![cycle1239_0,cycle1239_1,cycle1239_2,cycle1239_3,cycle1239_4,cycle1239_5]⟩
lemma valid_data1239 : data1239.Valid src1239 dst1239 Finset.univ := by decide +kernel

def src1240 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst1240 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle1240_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1240_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1240_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1240_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle1240_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1240_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1240 : PartitionData E W := ⟨6,![cycle1240_0,cycle1240_1,cycle1240_2,cycle1240_3,cycle1240_4,cycle1240_5]⟩
lemma valid_data1240 : data1240.Valid src1240 dst1240 Finset.univ := by decide +kernel

def src1241 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst1241 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle1241_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1241_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1241_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1241_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle1241_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,26,38,8,28]⟩
def cycle1241_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1241 : PartitionData E W := ⟨6,![cycle1241_0,cycle1241_1,cycle1241_2,cycle1241_3,cycle1241_4,cycle1241_5]⟩
lemma valid_data1241 : data1241.Valid src1241 dst1241 Finset.univ := by decide +kernel

def src1242 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst1242 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle1242_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1242_1 : CycleData E W := ⟨3,![1,14,21,20,2],![3,4,28,18,8]⟩
def cycle1242_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1242_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1242_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle1242_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1242 : PartitionData E W := ⟨6,![cycle1242_0,cycle1242_1,cycle1242_2,cycle1242_3,cycle1242_4,cycle1242_5]⟩
lemma valid_data1242 : data1242.Valid src1242 dst1242 Finset.univ := by decide +kernel

def src1243 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst1243 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle1243_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1243_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1243_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1243_3 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle1243_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle1243_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1243 : PartitionData E W := ⟨6,![cycle1243_0,cycle1243_1,cycle1243_2,cycle1243_3,cycle1243_4,cycle1243_5]⟩
lemma valid_data1243 : data1243.Valid src1243 dst1243 Finset.univ := by decide +kernel

def src1244 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst1244 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle1244_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1244_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1244_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1244_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1244_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle1244_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data1244 : PartitionData E W := ⟨6,![cycle1244_0,cycle1244_1,cycle1244_2,cycle1244_3,cycle1244_4,cycle1244_5]⟩
lemma valid_data1244 : data1244.Valid src1244 dst1244 Finset.univ := by decide +kernel

def src1245 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst1245 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle1245_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1245_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1245_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1245_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle1245_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1245_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1245 : PartitionData E W := ⟨6,![cycle1245_0,cycle1245_1,cycle1245_2,cycle1245_3,cycle1245_4,cycle1245_5]⟩
lemma valid_data1245 : data1245.Valid src1245 dst1245 Finset.univ := by decide +kernel

def src1246 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst1246 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle1246_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1246_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1246_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,27,28,8,18]⟩
def cycle1246_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle1246_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1246_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1246 : PartitionData E W := ⟨6,![cycle1246_0,cycle1246_1,cycle1246_2,cycle1246_3,cycle1246_4,cycle1246_5]⟩
lemma valid_data1246 : data1246.Valid src1246 dst1246 Finset.univ := by decide +kernel

def src1247 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst1247 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle1247_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1247_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1247_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1247_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle1247_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,26,38,8,28]⟩
def cycle1247_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1247 : PartitionData E W := ⟨6,![cycle1247_0,cycle1247_1,cycle1247_2,cycle1247_3,cycle1247_4,cycle1247_5]⟩
lemma valid_data1247 : data1247.Valid src1247 dst1247 Finset.univ := by decide +kernel

def src1248 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst1248 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle1248_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1248_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1248_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1248_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle1248_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle1248_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1248 : PartitionData E W := ⟨6,![cycle1248_0,cycle1248_1,cycle1248_2,cycle1248_3,cycle1248_4,cycle1248_5]⟩
lemma valid_data1248 : data1248.Valid src1248 dst1248 Finset.univ := by decide +kernel

def src1249 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst1249 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle1249_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1249_1 : CycleData E W := ⟨4,![2,23,14,10,16,7],![3,8,28,4,26,16]⟩
def cycle1249_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1249_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1249_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle1249_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1249 : PartitionData E W := ⟨6,![cycle1249_0,cycle1249_1,cycle1249_2,cycle1249_3,cycle1249_4,cycle1249_5]⟩
lemma valid_data1249 : data1249.Valid src1249 dst1249 Finset.univ := by decide +kernel

def src1250 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst1250 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle1250_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1250_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1250_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1250_3 : CycleData E W := ⟨3,![5,12,13,21,9],![2,14,27,28,18]⟩
def cycle1250_4 : CycleData E W := ⟨2,![6,11,16,7],![3,14,26,16]⟩
def cycle1250_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1250 : PartitionData E W := ⟨6,![cycle1250_0,cycle1250_1,cycle1250_2,cycle1250_3,cycle1250_4,cycle1250_5]⟩
lemma valid_data1250 : data1250.Valid src1250 dst1250 Finset.univ := by decide +kernel

def src1251 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst1251 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1251_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1251_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1251_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1251_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle1251_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle1251_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data1251 : PartitionData E W := ⟨6,![cycle1251_0,cycle1251_1,cycle1251_2,cycle1251_3,cycle1251_4,cycle1251_5]⟩
lemma valid_data1251 : data1251.Valid src1251 dst1251 Finset.univ := by decide +kernel

def src1252 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst1252 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle1252_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1252_1 : CycleData E W := ⟨3,![2,23,13,18,7],![3,8,28,27,16]⟩
def cycle1252_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1252_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1252_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle1252_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data1252 : PartitionData E W := ⟨6,![cycle1252_0,cycle1252_1,cycle1252_2,cycle1252_3,cycle1252_4,cycle1252_5]⟩
lemma valid_data1252 : data1252.Valid src1252 dst1252 Finset.univ := by decide +kernel

def src1253 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst1253 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle1253_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1253_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1253_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1253_3 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1253_4 : CycleData E W := ⟨2,![6,12,18,7],![3,14,27,16]⟩
def cycle1253_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1253 : PartitionData E W := ⟨6,![cycle1253_0,cycle1253_1,cycle1253_2,cycle1253_3,cycle1253_4,cycle1253_5]⟩
lemma valid_data1253 : data1253.Valid src1253 dst1253 Finset.univ := by decide +kernel

def src1254 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst1254 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle1254_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1254_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1254_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1254_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1254_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1254_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data1254 : PartitionData E W := ⟨6,![cycle1254_0,cycle1254_1,cycle1254_2,cycle1254_3,cycle1254_4,cycle1254_5]⟩
lemma valid_data1254 : data1254.Valid src1254 dst1254 Finset.univ := by decide +kernel

def src1255 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst1255 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle1255_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1255_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1255_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1255_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1255_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1255_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data1255 : PartitionData E W := ⟨6,![cycle1255_0,cycle1255_1,cycle1255_2,cycle1255_3,cycle1255_4,cycle1255_5]⟩
lemma valid_data1255 : data1255.Valid src1255 dst1255 Finset.univ := by decide +kernel

def src1256 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst1256 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle1256_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1256_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1256_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1256_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1256_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle1256_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data1256 : PartitionData E W := ⟨6,![cycle1256_0,cycle1256_1,cycle1256_2,cycle1256_3,cycle1256_4,cycle1256_5]⟩
lemma valid_data1256 : data1256.Valid src1256 dst1256 Finset.univ := by decide +kernel

def src1257 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst1257 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle1257_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1257_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1257_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1257_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1257_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,26,16,38,28]⟩
def cycle1257_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data1257 : PartitionData E W := ⟨6,![cycle1257_0,cycle1257_1,cycle1257_2,cycle1257_3,cycle1257_4,cycle1257_5]⟩
lemma valid_data1257 : data1257.Valid src1257 dst1257 Finset.univ := by decide +kernel

def src1258 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst1258 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle1258_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1258_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1258_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1258_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1258_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,26,16,38,28]⟩
def cycle1258_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data1258 : PartitionData E W := ⟨6,![cycle1258_0,cycle1258_1,cycle1258_2,cycle1258_3,cycle1258_4,cycle1258_5]⟩
lemma valid_data1258 : data1258.Valid src1258 dst1258 Finset.univ := by decide +kernel

def src1259 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst1259 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle1259_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1259_1 : CycleData E W := ⟨4,![2,20,14,10,17,7],![3,8,28,4,26,16]⟩
def cycle1259_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1259_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1259_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1259_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data1259 : PartitionData E W := ⟨6,![cycle1259_0,cycle1259_1,cycle1259_2,cycle1259_3,cycle1259_4,cycle1259_5]⟩
lemma valid_data1259 : data1259.Valid src1259 dst1259 Finset.univ := by decide +kernel

def src1260 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst1260 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle1260_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1260_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle1260_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1260_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1260_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle1260_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1260 : PartitionData E W := ⟨6,![cycle1260_0,cycle1260_1,cycle1260_2,cycle1260_3,cycle1260_4,cycle1260_5]⟩
lemma valid_data1260 : data1260.Valid src1260 dst1260 Finset.univ := by decide +kernel

def src1261 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst1261 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle1261_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1261_1 : CycleData E W := ⟨3,![1,14,19,15,7],![3,4,27,6,16]⟩
def cycle1261_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle1261_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1261_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle1261_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1261 : PartitionData E W := ⟨6,![cycle1261_0,cycle1261_1,cycle1261_2,cycle1261_3,cycle1261_4,cycle1261_5]⟩
lemma valid_data1261 : data1261.Valid src1261 dst1261 Finset.univ := by decide +kernel

def src1262 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst1262 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle1262_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1262_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle1262_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1262_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1262_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle1262_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data1262 : PartitionData E W := ⟨6,![cycle1262_0,cycle1262_1,cycle1262_2,cycle1262_3,cycle1262_4,cycle1262_5]⟩
lemma valid_data1262 : data1262.Valid src1262 dst1262 Finset.univ := by decide +kernel

def src1263 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst1263 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle1263_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1263_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1263_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle1263_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle1263_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1263_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1263 : PartitionData E W := ⟨6,![cycle1263_0,cycle1263_1,cycle1263_2,cycle1263_3,cycle1263_4,cycle1263_5]⟩
lemma valid_data1263 : data1263.Valid src1263 dst1263 Finset.univ := by decide +kernel

def src1264 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst1264 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle1264_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1264_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1264_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1264_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle1264_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1264_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1264 : PartitionData E W := ⟨6,![cycle1264_0,cycle1264_1,cycle1264_2,cycle1264_3,cycle1264_4,cycle1264_5]⟩
lemma valid_data1264 : data1264.Valid src1264 dst1264 Finset.univ := by decide +kernel

def src1265 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst1265 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle1265_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1265_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1265_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1265_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle1265_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1265_5 : CycleData E W := ⟨3,![20,12,11,18,23],![8,28,14,26,38]⟩
def data1265 : PartitionData E W := ⟨6,![cycle1265_0,cycle1265_1,cycle1265_2,cycle1265_3,cycle1265_4,cycle1265_5]⟩
lemma valid_data1265 : data1265.Valid src1265 dst1265 Finset.univ := by decide +kernel

def src1266 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst1266 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle1266_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1266_1 : CycleData E W := ⟨2,![1,14,16,7],![3,4,27,16]⟩
def cycle1266_2 : CycleData E W := ⟨3,![2,20,21,12,6],![3,8,18,28,14]⟩
def cycle1266_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1266_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1266_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1266 : PartitionData E W := ⟨6,![cycle1266_0,cycle1266_1,cycle1266_2,cycle1266_3,cycle1266_4,cycle1266_5]⟩
lemma valid_data1266 : data1266.Valid src1266 dst1266 Finset.univ := by decide +kernel

def src1267 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst1267 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle1267_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1267_1 : CycleData E W := ⟨2,![1,14,16,7],![3,4,27,16]⟩
def cycle1267_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle1267_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1267_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle1267_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1267 : PartitionData E W := ⟨6,![cycle1267_0,cycle1267_1,cycle1267_2,cycle1267_3,cycle1267_4,cycle1267_5]⟩
lemma valid_data1267 : data1267.Valid src1267 dst1267 Finset.univ := by decide +kernel

def src1268 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst1268 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle1268_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1268_1 : CycleData E W := ⟨2,![1,14,16,7],![3,4,27,16]⟩
def cycle1268_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1268_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1268_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1268_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data1268 : PartitionData E W := ⟨6,![cycle1268_0,cycle1268_1,cycle1268_2,cycle1268_3,cycle1268_4,cycle1268_5]⟩
lemma valid_data1268 : data1268.Valid src1268 dst1268 Finset.univ := by decide +kernel

def src1269 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst1269 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle1269_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1269_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1269_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1269_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle1269_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1269_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data1269 : PartitionData E W := ⟨6,![cycle1269_0,cycle1269_1,cycle1269_2,cycle1269_3,cycle1269_4,cycle1269_5]⟩
lemma valid_data1269 : data1269.Valid src1269 dst1269 Finset.univ := by decide +kernel

def src1270 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst1270 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle1270_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1270_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1270_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,27,28,8,18]⟩
def cycle1270_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle1270_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1270_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data1270 : PartitionData E W := ⟨6,![cycle1270_0,cycle1270_1,cycle1270_2,cycle1270_3,cycle1270_4,cycle1270_5]⟩
lemma valid_data1270 : data1270.Valid src1270 dst1270 Finset.univ := by decide +kernel

def src1271 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst1271 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle1271_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1271_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1271_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1271_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle1271_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1271_5 : CycleData E W := ⟨3,![20,12,11,17,23],![8,28,14,26,38]⟩
def data1271 : PartitionData E W := ⟨6,![cycle1271_0,cycle1271_1,cycle1271_2,cycle1271_3,cycle1271_4,cycle1271_5]⟩
lemma valid_data1271 : data1271.Valid src1271 dst1271 Finset.univ := by decide +kernel

def src1272 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst1272 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle1272_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1272_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1272_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1272_3 : CycleData E W := ⟨4,![4,15,11,12,21,9],![2,6,26,14,28,18]⟩
def cycle1272_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1272_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1272 : PartitionData E W := ⟨6,![cycle1272_0,cycle1272_1,cycle1272_2,cycle1272_3,cycle1272_4,cycle1272_5]⟩
lemma valid_data1272 : data1272.Valid src1272 dst1272 Finset.univ := by decide +kernel

def src1273 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst1273 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle1273_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1273_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1273_2 : CycleData E W := ⟨3,![3,23,12,11,15],![6,8,28,14,26]⟩
def cycle1273_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1273_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1273_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1273 : PartitionData E W := ⟨6,![cycle1273_0,cycle1273_1,cycle1273_2,cycle1273_3,cycle1273_4,cycle1273_5]⟩
lemma valid_data1273 : data1273.Valid src1273 dst1273 Finset.univ := by decide +kernel

def src1274 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst1274 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle1274_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,16,18]⟩
def cycle1274_1 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1274_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1274_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1274_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1274_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data1274 : PartitionData E W := ⟨6,![cycle1274_0,cycle1274_1,cycle1274_2,cycle1274_3,cycle1274_4,cycle1274_5]⟩
lemma valid_data1274 : data1274.Valid src1274 dst1274 Finset.univ := by decide +kernel

def src1275 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst1275 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle1275_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1275_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1275_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1275_3 : CycleData E W := ⟨4,![4,15,11,12,21,9],![2,6,26,14,28,18]⟩
def cycle1275_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1275_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data1275 : PartitionData E W := ⟨6,![cycle1275_0,cycle1275_1,cycle1275_2,cycle1275_3,cycle1275_4,cycle1275_5]⟩
lemma valid_data1275 : data1275.Valid src1275 dst1275 Finset.univ := by decide +kernel

def src1276 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst1276 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle1276_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1276_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1276_2 : CycleData E W := ⟨3,![3,23,12,11,15],![6,8,28,14,26]⟩
def cycle1276_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1276_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1276_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data1276 : PartitionData E W := ⟨6,![cycle1276_0,cycle1276_1,cycle1276_2,cycle1276_3,cycle1276_4,cycle1276_5]⟩
lemma valid_data1276 : data1276.Valid src1276 dst1276 Finset.univ := by decide +kernel

def src1277 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst1277 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle1277_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1277_1 : CycleData E W := ⟨3,![2,20,13,17,7],![3,8,28,27,16]⟩
def cycle1277_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1277_3 : CycleData E W := ⟨4,![4,15,11,12,21,9],![2,6,26,14,28,18]⟩
def cycle1277_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1277_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data1277 : PartitionData E W := ⟨6,![cycle1277_0,cycle1277_1,cycle1277_2,cycle1277_3,cycle1277_4,cycle1277_5]⟩
lemma valid_data1277 : data1277.Valid src1277 dst1277 Finset.univ := by decide +kernel

def src1278 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst1278 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1278_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1278_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1278_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1278_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle1278_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1278_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data1278 : PartitionData E W := ⟨6,![cycle1278_0,cycle1278_1,cycle1278_2,cycle1278_3,cycle1278_4,cycle1278_5]⟩
lemma valid_data1278 : data1278.Valid src1278 dst1278 Finset.univ := by decide +kernel

def src1279 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst1279 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1279_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1279_1 : CycleData E W := ⟨3,![2,23,13,18,7],![3,8,28,27,16]⟩
def cycle1279_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1279_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1279_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1279_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data1279 : PartitionData E W := ⟨6,![cycle1279_0,cycle1279_1,cycle1279_2,cycle1279_3,cycle1279_4,cycle1279_5]⟩
lemma valid_data1279 : data1279.Valid src1279 dst1279 Finset.univ := by decide +kernel

def src1280 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst1280 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1280_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1280_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle1280_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1280_3 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1280_4 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1280_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1280 : PartitionData E W := ⟨6,![cycle1280_0,cycle1280_1,cycle1280_2,cycle1280_3,cycle1280_4,cycle1280_5]⟩
lemma valid_data1280 : data1280.Valid src1280 dst1280 Finset.univ := by decide +kernel

def src1281 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst1281 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1281_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1281_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1281_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1281_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1281_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1281_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1281 : PartitionData E W := ⟨6,![cycle1281_0,cycle1281_1,cycle1281_2,cycle1281_3,cycle1281_4,cycle1281_5]⟩
lemma valid_data1281 : data1281.Valid src1281 dst1281 Finset.univ := by decide +kernel

def src1282 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst1282 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1282_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1282_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1282_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1282_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1282_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1282_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1282 : PartitionData E W := ⟨6,![cycle1282_0,cycle1282_1,cycle1282_2,cycle1282_3,cycle1282_4,cycle1282_5]⟩
lemma valid_data1282 : data1282.Valid src1282 dst1282 Finset.univ := by decide +kernel

def src1283 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst1283 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1283_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1283_1 : CycleData E W := ⟨2,![1,14,16,7],![3,4,27,16]⟩
def cycle1283_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1283_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1283_4 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1283_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data1283 : PartitionData E W := ⟨6,![cycle1283_0,cycle1283_1,cycle1283_2,cycle1283_3,cycle1283_4,cycle1283_5]⟩
lemma valid_data1283 : data1283.Valid src1283 dst1283 Finset.univ := by decide +kernel

def src1284 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst1284 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle1284_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1284_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1284_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1284_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle1284_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle1284_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data1284 : PartitionData E W := ⟨6,![cycle1284_0,cycle1284_1,cycle1284_2,cycle1284_3,cycle1284_4,cycle1284_5]⟩
lemma valid_data1284 : data1284.Valid src1284 dst1284 Finset.univ := by decide +kernel

def src1285 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst1285 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle1285_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1285_1 : CycleData E W := ⟨4,![2,23,14,10,16,7],![3,8,28,4,26,16]⟩
def cycle1285_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1285_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1285_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle1285_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data1285 : PartitionData E W := ⟨6,![cycle1285_0,cycle1285_1,cycle1285_2,cycle1285_3,cycle1285_4,cycle1285_5]⟩
lemma valid_data1285 : data1285.Valid src1285 dst1285 Finset.univ := by decide +kernel

def src1286 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst1286 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle1286_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle1286_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1286_2 : CycleData E W := ⟨3,![2,23,18,12,6],![3,8,38,27,14]⟩
def cycle1286_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,6,8,28,18]⟩
def cycle1286_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1286_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data1286 : PartitionData E W := ⟨6,![cycle1286_0,cycle1286_1,cycle1286_2,cycle1286_3,cycle1286_4,cycle1286_5]⟩
lemma valid_data1286 : data1286.Valid src1286 dst1286 Finset.univ := by decide +kernel

def src1287 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst1287 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle1287_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1287_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1287_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1287_3 : CycleData E W := ⟨4,![4,15,12,13,21,9],![2,6,27,14,28,18]⟩
def cycle1287_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1287_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1287 : PartitionData E W := ⟨6,![cycle1287_0,cycle1287_1,cycle1287_2,cycle1287_3,cycle1287_4,cycle1287_5]⟩
lemma valid_data1287 : data1287.Valid src1287 dst1287 Finset.univ := by decide +kernel

def src1288 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst1288 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle1288_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1288_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1288_2 : CycleData E W := ⟨3,![3,23,13,12,15],![6,8,28,14,27]⟩
def cycle1288_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1288_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1288_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1288 : PartitionData E W := ⟨6,![cycle1288_0,cycle1288_1,cycle1288_2,cycle1288_3,cycle1288_4,cycle1288_5]⟩
lemma valid_data1288 : data1288.Valid src1288 dst1288 Finset.univ := by decide +kernel

def src1289 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst1289 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle1289_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,16,18]⟩
def cycle1289_1 : CycleData E W := ⟨2,![2,20,13,6],![3,8,28,14]⟩
def cycle1289_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1289_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1289_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle1289_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1289 : PartitionData E W := ⟨6,![cycle1289_0,cycle1289_1,cycle1289_2,cycle1289_3,cycle1289_4,cycle1289_5]⟩
lemma valid_data1289 : data1289.Valid src1289 dst1289 Finset.univ := by decide +kernel

def src1290 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst1290 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle1290_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1290_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1290_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle1290_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle1290_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1290_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1290 : PartitionData E W := ⟨6,![cycle1290_0,cycle1290_1,cycle1290_2,cycle1290_3,cycle1290_4,cycle1290_5]⟩
lemma valid_data1290 : data1290.Valid src1290 dst1290 Finset.univ := by decide +kernel

def src1291 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst1291 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle1291_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1291_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1291_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1291_3 : CycleData E W := ⟨3,![20,8,16,11,23],![8,18,16,26,28]⟩
def cycle1291_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1291_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1291 : PartitionData E W := ⟨6,![cycle1291_0,cycle1291_1,cycle1291_2,cycle1291_3,cycle1291_4,cycle1291_5]⟩
lemma valid_data1291 : data1291.Valid src1291 dst1291 Finset.univ := by decide +kernel

def src1292 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst1292 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle1292_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1292_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1292_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1292_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle1292_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1292_5 : CycleData E W := ⟨3,![20,12,13,18,23],![8,28,14,27,38]⟩
def data1292 : PartitionData E W := ⟨6,![cycle1292_0,cycle1292_1,cycle1292_2,cycle1292_3,cycle1292_4,cycle1292_5]⟩
lemma valid_data1292 : data1292.Valid src1292 dst1292 Finset.univ := by decide +kernel

def src1293 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst1293 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle1293_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1293_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1293_2 : CycleData E W := ⟨3,![2,20,21,12,6],![3,8,18,28,14]⟩
def cycle1293_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1293_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1293_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data1293 : PartitionData E W := ⟨6,![cycle1293_0,cycle1293_1,cycle1293_2,cycle1293_3,cycle1293_4,cycle1293_5]⟩
lemma valid_data1293 : data1293.Valid src1293 dst1293 Finset.univ := by decide +kernel

def src1294 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst1294 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle1294_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1294_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1294_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle1294_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1294_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle1294_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data1294 : PartitionData E W := ⟨6,![cycle1294_0,cycle1294_1,cycle1294_2,cycle1294_3,cycle1294_4,cycle1294_5]⟩
lemma valid_data1294 : data1294.Valid src1294 dst1294 Finset.univ := by decide +kernel

def src1295 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst1295 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle1295_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1295_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1295_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1295_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1295_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1295_5 : CycleData E W := ⟨2,![21,11,17,22],![18,28,26,38]⟩
def data1295 : PartitionData E W := ⟨6,![cycle1295_0,cycle1295_1,cycle1295_2,cycle1295_3,cycle1295_4,cycle1295_5]⟩
lemma valid_data1295 : data1295.Valid src1295 dst1295 Finset.univ := by decide +kernel

def src1296 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst1296 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle1296_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle1296_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,27,14]⟩
def cycle1296_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1296_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1296_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle1296_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1296 : PartitionData E W := ⟨6,![cycle1296_0,cycle1296_1,cycle1296_2,cycle1296_3,cycle1296_4,cycle1296_5]⟩
lemma valid_data1296 : data1296.Valid src1296 dst1296 Finset.univ := by decide +kernel

def src1297 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst1297 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle1297_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1297_1 : CycleData E W := ⟨3,![1,10,19,15,7],![3,4,26,6,16]⟩
def cycle1297_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle1297_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1297_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle1297_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1297 : PartitionData E W := ⟨6,![cycle1297_0,cycle1297_1,cycle1297_2,cycle1297_3,cycle1297_4,cycle1297_5]⟩
lemma valid_data1297 : data1297.Valid src1297 dst1297 Finset.univ := by decide +kernel

def src1298 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst1298 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle1298_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle1298_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,27,14]⟩
def cycle1298_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1298_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1298_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle1298_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data1298 : PartitionData E W := ⟨6,![cycle1298_0,cycle1298_1,cycle1298_2,cycle1298_3,cycle1298_4,cycle1298_5]⟩
lemma valid_data1298 : data1298.Valid src1298 dst1298 Finset.univ := by decide +kernel

def src1299 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst1299 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle1299_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1299_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1299_2 : CycleData E W := ⟨3,![4,19,11,21,9],![2,6,26,28,18]⟩
def cycle1299_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle1299_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1299_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data1299 : PartitionData E W := ⟨6,![cycle1299_0,cycle1299_1,cycle1299_2,cycle1299_3,cycle1299_4,cycle1299_5]⟩
lemma valid_data1299 : data1299.Valid src1299 dst1299 Finset.univ := by decide +kernel

def src1300 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst1300 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle1300_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1300_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1300_2 : CycleData E W := ⟨4,![4,19,11,23,20,9],![2,6,26,28,8,18]⟩
def cycle1300_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle1300_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1300_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data1300 : PartitionData E W := ⟨6,![cycle1300_0,cycle1300_1,cycle1300_2,cycle1300_3,cycle1300_4,cycle1300_5]⟩
lemma valid_data1300 : data1300.Valid src1300 dst1300 Finset.univ := by decide +kernel

def src1301 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst1301 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle1301_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1301_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1301_2 : CycleData E W := ⟨3,![4,19,11,21,9],![2,6,26,28,18]⟩
def cycle1301_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle1301_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1301_5 : CycleData E W := ⟨3,![20,12,13,17,23],![8,28,14,27,38]⟩
def data1301 : PartitionData E W := ⟨6,![cycle1301_0,cycle1301_1,cycle1301_2,cycle1301_3,cycle1301_4,cycle1301_5]⟩
lemma valid_data1301 : data1301.Valid src1301 dst1301 Finset.univ := by decide +kernel

def src1302 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst1302 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle1302_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1302_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1302_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1302_3 : CycleData E W := ⟨3,![4,15,11,21,9],![2,6,26,28,18]⟩
def cycle1302_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1302_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1302 : PartitionData E W := ⟨6,![cycle1302_0,cycle1302_1,cycle1302_2,cycle1302_3,cycle1302_4,cycle1302_5]⟩
lemma valid_data1302 : data1302.Valid src1302 dst1302 Finset.univ := by decide +kernel

def src1303 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst1303 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle1303_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1303_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1303_2 : CycleData E W := ⟨2,![3,23,11,15],![6,8,28,26]⟩
def cycle1303_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1303_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1303_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1303 : PartitionData E W := ⟨6,![cycle1303_0,cycle1303_1,cycle1303_2,cycle1303_3,cycle1303_4,cycle1303_5]⟩
lemma valid_data1303 : data1303.Valid src1303 dst1303 Finset.univ := by decide +kernel

def src1304 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst1304 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle1304_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1304_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1304_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1304_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1304_4 : CycleData E W := ⟨3,![4,15,11,21,9],![2,6,26,28,18]⟩
def cycle1304_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data1304 : PartitionData E W := ⟨6,![cycle1304_0,cycle1304_1,cycle1304_2,cycle1304_3,cycle1304_4,cycle1304_5]⟩
lemma valid_data1304 : data1304.Valid src1304 dst1304 Finset.univ := by decide +kernel

def src1305 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst1305 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle1305_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1305_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1305_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1305_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle1305_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1305_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1305 : PartitionData E W := ⟨6,![cycle1305_0,cycle1305_1,cycle1305_2,cycle1305_3,cycle1305_4,cycle1305_5]⟩
lemma valid_data1305 : data1305.Valid src1305 dst1305 Finset.univ := by decide +kernel

def src1306 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst1306 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle1306_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1306_1 : CycleData E W := ⟨3,![2,23,11,16,7],![3,8,28,26,16]⟩
def cycle1306_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1306_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1306_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1306_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1306 : PartitionData E W := ⟨6,![cycle1306_0,cycle1306_1,cycle1306_2,cycle1306_3,cycle1306_4,cycle1306_5]⟩
lemma valid_data1306 : data1306.Valid src1306 dst1306 Finset.univ := by decide +kernel

def src1307 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst1307 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle1307_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1307_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1307_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1307_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1307_4 : CycleData E W := ⟨3,![4,15,11,21,9],![2,6,26,28,18]⟩
def cycle1307_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1307 : PartitionData E W := ⟨6,![cycle1307_0,cycle1307_1,cycle1307_2,cycle1307_3,cycle1307_4,cycle1307_5]⟩
lemma valid_data1307 : data1307.Valid src1307 dst1307 Finset.univ := by decide +kernel

def src1308 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst1308 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle1308_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1308_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1308_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1308_3 : CycleData E W := ⟨4,![4,15,13,12,21,9],![2,6,27,14,28,18]⟩
def cycle1308_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1308_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1308 : PartitionData E W := ⟨6,![cycle1308_0,cycle1308_1,cycle1308_2,cycle1308_3,cycle1308_4,cycle1308_5]⟩
lemma valid_data1308 : data1308.Valid src1308 dst1308 Finset.univ := by decide +kernel

def src1309 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst1309 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle1309_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1309_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1309_2 : CycleData E W := ⟨3,![3,23,12,13,15],![6,8,28,14,27]⟩
def cycle1309_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1309_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1309_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1309 : PartitionData E W := ⟨6,![cycle1309_0,cycle1309_1,cycle1309_2,cycle1309_3,cycle1309_4,cycle1309_5]⟩
lemma valid_data1309 : data1309.Valid src1309 dst1309 Finset.univ := by decide +kernel

def src1310 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst1310 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle1310_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,16,18]⟩
def cycle1310_1 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle1310_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1310_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1310_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1310_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data1310 : PartitionData E W := ⟨6,![cycle1310_0,cycle1310_1,cycle1310_2,cycle1310_3,cycle1310_4,cycle1310_5]⟩
lemma valid_data1310 : data1310.Valid src1310 dst1310 Finset.univ := by decide +kernel

def src1311 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst1311 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle1311_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1311_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1311_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1311_3 : CycleData E W := ⟨4,![4,15,13,12,21,9],![2,6,27,14,28,18]⟩
def cycle1311_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1311_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data1311 : PartitionData E W := ⟨6,![cycle1311_0,cycle1311_1,cycle1311_2,cycle1311_3,cycle1311_4,cycle1311_5]⟩
lemma valid_data1311 : data1311.Valid src1311 dst1311 Finset.univ := by decide +kernel

def src1312 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst1312 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle1312_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1312_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1312_2 : CycleData E W := ⟨3,![3,23,12,13,15],![6,8,28,14,27]⟩
def cycle1312_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1312_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1312_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data1312 : PartitionData E W := ⟨6,![cycle1312_0,cycle1312_1,cycle1312_2,cycle1312_3,cycle1312_4,cycle1312_5]⟩
lemma valid_data1312 : data1312.Valid src1312 dst1312 Finset.univ := by decide +kernel

def src1313 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst1313 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle1313_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1313_1 : CycleData E W := ⟨3,![2,20,11,17,7],![3,8,28,26,16]⟩
def cycle1313_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1313_3 : CycleData E W := ⟨4,![4,15,13,12,21,9],![2,6,27,14,28,18]⟩
def cycle1313_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1313_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data1313 : PartitionData E W := ⟨6,![cycle1313_0,cycle1313_1,cycle1313_2,cycle1313_3,cycle1313_4,cycle1313_5]⟩
lemma valid_data1313 : data1313.Valid src1313 dst1313 Finset.univ := by decide +kernel

def src1314 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst1314 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle1314_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1314_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1314_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle1314_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1314_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1314_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1314 : PartitionData E W := ⟨6,![cycle1314_0,cycle1314_1,cycle1314_2,cycle1314_3,cycle1314_4,cycle1314_5]⟩
lemma valid_data1314 : data1314.Valid src1314 dst1314 Finset.univ := by decide +kernel

def src1315 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst1315 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle1315_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1315_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1315_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1315_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,26,28]⟩
def cycle1315_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1315_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1315 : PartitionData E W := ⟨6,![cycle1315_0,cycle1315_1,cycle1315_2,cycle1315_3,cycle1315_4,cycle1315_5]⟩
lemma valid_data1315 : data1315.Valid src1315 dst1315 Finset.univ := by decide +kernel

def src1316 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst1316 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle1316_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1316_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1316_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle1316_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1316_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,27,38,8,28]⟩
def cycle1316_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1316 : PartitionData E W := ⟨6,![cycle1316_0,cycle1316_1,cycle1316_2,cycle1316_3,cycle1316_4,cycle1316_5]⟩
lemma valid_data1316 : data1316.Valid src1316 dst1316 Finset.univ := by decide +kernel

def src1317 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst1317 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle1317_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1317_1 : CycleData E W := ⟨3,![1,14,21,20,2],![3,4,28,18,8]⟩
def cycle1317_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1317_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1317_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle1317_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data1317 : PartitionData E W := ⟨6,![cycle1317_0,cycle1317_1,cycle1317_2,cycle1317_3,cycle1317_4,cycle1317_5]⟩
lemma valid_data1317 : data1317.Valid src1317 dst1317 Finset.univ := by decide +kernel

def src1318 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst1318 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle1318_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1318_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1318_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1318_3 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle1318_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle1318_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data1318 : PartitionData E W := ⟨6,![cycle1318_0,cycle1318_1,cycle1318_2,cycle1318_3,cycle1318_4,cycle1318_5]⟩
lemma valid_data1318 : data1318.Valid src1318 dst1318 Finset.univ := by decide +kernel

def src1319 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst1319 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle1319_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1319_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1319_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1319_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle1319_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle1319_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,26,38]⟩
def data1319 : PartitionData E W := ⟨6,![cycle1319_0,cycle1319_1,cycle1319_2,cycle1319_3,cycle1319_4,cycle1319_5]⟩
lemma valid_data1319 : data1319.Valid src1319 dst1319 Finset.univ := by decide +kernel

def src1320 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst1320 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle1320_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,28,18]⟩
def cycle1320_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,27,14]⟩
def cycle1320_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1320_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,26,14]⟩
def cycle1320_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle1320_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1320 : PartitionData E W := ⟨6,![cycle1320_0,cycle1320_1,cycle1320_2,cycle1320_3,cycle1320_4,cycle1320_5]⟩
lemma valid_data1320 : data1320.Valid src1320 dst1320 Finset.univ := by decide +kernel

def src1321 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst1321 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle1321_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1321_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1321_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1321_3 : CycleData E W := ⟨3,![6,12,19,15,7],![3,14,26,6,16]⟩
def cycle1321_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle1321_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1321 : PartitionData E W := ⟨6,![cycle1321_0,cycle1321_1,cycle1321_2,cycle1321_3,cycle1321_4,cycle1321_5]⟩
lemma valid_data1321 : data1321.Valid src1321 dst1321 Finset.univ := by decide +kernel

def src1322 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst1322 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle1322_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,28,18]⟩
def cycle1322_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,27,14]⟩
def cycle1322_2 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1322_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,26,14]⟩
def cycle1322_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle1322_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data1322 : PartitionData E W := ⟨6,![cycle1322_0,cycle1322_1,cycle1322_2,cycle1322_3,cycle1322_4,cycle1322_5]⟩
lemma valid_data1322 : data1322.Valid src1322 dst1322 Finset.univ := by decide +kernel

def src1323 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst1323 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle1323_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1323_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1323_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,26,28,18]⟩
def cycle1323_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle1323_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle1323_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1323 : PartitionData E W := ⟨6,![cycle1323_0,cycle1323_1,cycle1323_2,cycle1323_3,cycle1323_4,cycle1323_5]⟩
lemma valid_data1323 : data1323.Valid src1323 dst1323 Finset.univ := by decide +kernel

def src1324 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst1324 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle1324_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1324_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1324_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,26,28,8,18]⟩
def cycle1324_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle1324_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle1324_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1324 : PartitionData E W := ⟨6,![cycle1324_0,cycle1324_1,cycle1324_2,cycle1324_3,cycle1324_4,cycle1324_5]⟩
lemma valid_data1324 : data1324.Valid src1324 dst1324 Finset.univ := by decide +kernel

def src1325 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst1325 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle1325_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1325_1 : CycleData E W := ⟨2,![2,3,15,7],![3,8,6,16]⟩
def cycle1325_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,26,28,18]⟩
def cycle1325_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle1325_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,27,38,8,28]⟩
def cycle1325_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1325 : PartitionData E W := ⟨6,![cycle1325_0,cycle1325_1,cycle1325_2,cycle1325_3,cycle1325_4,cycle1325_5]⟩
lemma valid_data1325 : data1325.Valid src1325 dst1325 Finset.univ := by decide +kernel

def src1326 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst1326 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1326_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1326_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1326_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1326_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1326_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1326_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data1326 : PartitionData E W := ⟨6,![cycle1326_0,cycle1326_1,cycle1326_2,cycle1326_3,cycle1326_4,cycle1326_5]⟩
lemma valid_data1326 : data1326.Valid src1326 dst1326 Finset.univ := by decide +kernel

def src1327 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst1327 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1327_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1327_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1327_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1327_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1327_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1327_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data1327 : PartitionData E W := ⟨6,![cycle1327_0,cycle1327_1,cycle1327_2,cycle1327_3,cycle1327_4,cycle1327_5]⟩
lemma valid_data1327 : data1327.Valid src1327 dst1327 Finset.univ := by decide +kernel

def src1328 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst1328 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1328_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1328_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1328_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1328_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1328_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle1328_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data1328 : PartitionData E W := ⟨6,![cycle1328_0,cycle1328_1,cycle1328_2,cycle1328_3,cycle1328_4,cycle1328_5]⟩
lemma valid_data1328 : data1328.Valid src1328 dst1328 Finset.univ := by decide +kernel

def src1329 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst1329 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1329_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1329_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1329_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1329_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle1329_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1329_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data1329 : PartitionData E W := ⟨6,![cycle1329_0,cycle1329_1,cycle1329_2,cycle1329_3,cycle1329_4,cycle1329_5]⟩
lemma valid_data1329 : data1329.Valid src1329 dst1329 Finset.univ := by decide +kernel

def src1330 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst1330 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1330_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1330_1 : CycleData E W := ⟨3,![2,23,13,16,7],![3,8,28,26,16]⟩
def cycle1330_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1330_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1330_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1330_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data1330 : PartitionData E W := ⟨6,![cycle1330_0,cycle1330_1,cycle1330_2,cycle1330_3,cycle1330_4,cycle1330_5]⟩
lemma valid_data1330 : data1330.Valid src1330 dst1330 Finset.univ := by decide +kernel

def src1331 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst1331 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1331_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1331_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1331_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1331_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1331_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle1331_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1331 : PartitionData E W := ⟨6,![cycle1331_0,cycle1331_1,cycle1331_2,cycle1331_3,cycle1331_4,cycle1331_5]⟩
lemma valid_data1331 : data1331.Valid src1331 dst1331 Finset.univ := by decide +kernel

def src1332 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst1332 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle1332_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1332_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1332_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1332_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1332_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,27,16,38,28]⟩
def cycle1332_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data1332 : PartitionData E W := ⟨6,![cycle1332_0,cycle1332_1,cycle1332_2,cycle1332_3,cycle1332_4,cycle1332_5]⟩
lemma valid_data1332 : data1332.Valid src1332 dst1332 Finset.univ := by decide +kernel

def src1333 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst1333 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle1333_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1333_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1333_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1333_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1333_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,27,16,38,28]⟩
def cycle1333_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data1333 : PartitionData E W := ⟨6,![cycle1333_0,cycle1333_1,cycle1333_2,cycle1333_3,cycle1333_4,cycle1333_5]⟩
lemma valid_data1333 : data1333.Valid src1333 dst1333 Finset.univ := by decide +kernel

def src1334 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst1334 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle1334_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1334_1 : CycleData E W := ⟨4,![2,20,14,10,17,7],![3,8,28,4,27,16]⟩
def cycle1334_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1334_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1334_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1334_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data1334 : PartitionData E W := ⟨6,![cycle1334_0,cycle1334_1,cycle1334_2,cycle1334_3,cycle1334_4,cycle1334_5]⟩
lemma valid_data1334 : data1334.Valid src1334 dst1334 Finset.univ := by decide +kernel

def src1335 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst1335 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle1335_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1335_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1335_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1335_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle1335_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle1335_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1335 : PartitionData E W := ⟨6,![cycle1335_0,cycle1335_1,cycle1335_2,cycle1335_3,cycle1335_4,cycle1335_5]⟩
lemma valid_data1335 : data1335.Valid src1335 dst1335 Finset.univ := by decide +kernel

def src1336 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst1336 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle1336_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1336_1 : CycleData E W := ⟨4,![2,23,14,10,18,7],![3,8,28,4,27,16]⟩
def cycle1336_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1336_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1336_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle1336_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1336 : PartitionData E W := ⟨6,![cycle1336_0,cycle1336_1,cycle1336_2,cycle1336_3,cycle1336_4,cycle1336_5]⟩
lemma valid_data1336 : data1336.Valid src1336 dst1336 Finset.univ := by decide +kernel

def src1337 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst1337 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle1337_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,27,6]⟩
def cycle1337_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1337_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1337_3 : CycleData E W := ⟨3,![5,12,13,21,9],![2,14,26,28,18]⟩
def cycle1337_4 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle1337_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1337 : PartitionData E W := ⟨6,![cycle1337_0,cycle1337_1,cycle1337_2,cycle1337_3,cycle1337_4,cycle1337_5]⟩
lemma valid_data1337 : data1337.Valid src1337 dst1337 Finset.univ := by decide +kernel

def src1338 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst1338 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle1338_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1338_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1338_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1338_3 : CycleData E W := ⟨4,![4,15,12,13,21,9],![2,6,26,14,28,18]⟩
def cycle1338_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1338_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1338 : PartitionData E W := ⟨6,![cycle1338_0,cycle1338_1,cycle1338_2,cycle1338_3,cycle1338_4,cycle1338_5]⟩
lemma valid_data1338 : data1338.Valid src1338 dst1338 Finset.univ := by decide +kernel

def src1339 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst1339 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle1339_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1339_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle1339_2 : CycleData E W := ⟨3,![3,23,13,12,15],![6,8,28,14,26]⟩
def cycle1339_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1339_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1339_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1339 : PartitionData E W := ⟨6,![cycle1339_0,cycle1339_1,cycle1339_2,cycle1339_3,cycle1339_4,cycle1339_5]⟩
lemma valid_data1339 : data1339.Valid src1339 dst1339 Finset.univ := by decide +kernel

def src1340 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst1340 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle1340_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,16,18]⟩
def cycle1340_1 : CycleData E W := ⟨2,![2,20,13,6],![3,8,28,14]⟩
def cycle1340_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1340_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1340_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def cycle1340_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1340 : PartitionData E W := ⟨6,![cycle1340_0,cycle1340_1,cycle1340_2,cycle1340_3,cycle1340_4,cycle1340_5]⟩
lemma valid_data1340 : data1340.Valid src1340 dst1340 Finset.univ := by decide +kernel

def src1341 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst1341 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle1341_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1341_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1341_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1341_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle1341_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle1341_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data1341 : PartitionData E W := ⟨6,![cycle1341_0,cycle1341_1,cycle1341_2,cycle1341_3,cycle1341_4,cycle1341_5]⟩
lemma valid_data1341 : data1341.Valid src1341 dst1341 Finset.univ := by decide +kernel

def src1342 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst1342 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle1342_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle1342_1 : CycleData E W := ⟨4,![2,23,14,10,18,7],![3,8,28,4,27,16]⟩
def cycle1342_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1342_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1342_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle1342_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data1342 : PartitionData E W := ⟨6,![cycle1342_0,cycle1342_1,cycle1342_2,cycle1342_3,cycle1342_4,cycle1342_5]⟩
lemma valid_data1342 : data1342.Valid src1342 dst1342 Finset.univ := by decide +kernel

def src1343 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst1343 : E → W := ![4,3,8,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle1343_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle1343_1 : CycleData E W := ⟨2,![1,10,18,7],![3,4,27,16]⟩
def cycle1343_2 : CycleData E W := ⟨3,![2,23,16,12,6],![3,8,38,26,14]⟩
def cycle1343_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,6,8,28,18]⟩
def cycle1343_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1343_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data1343 : PartitionData E W := ⟨6,![cycle1343_0,cycle1343_1,cycle1343_2,cycle1343_3,cycle1343_4,cycle1343_5]⟩
lemma valid_data1343 : data1343.Valid src1343 dst1343 Finset.univ := by decide +kernel

def src1344 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst1344 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle1344_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1344_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1344_2 : CycleData E W := ⟨4,![10,15,3,20,21,14],![4,26,6,8,18,28]⟩
def cycle1344_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1344_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle1344_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1344 : PartitionData E W := ⟨6,![cycle1344_0,cycle1344_1,cycle1344_2,cycle1344_3,cycle1344_4,cycle1344_5]⟩
lemma valid_data1344 : data1344.Valid src1344 dst1344 Finset.univ := by decide +kernel

def src1345 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst1345 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle1345_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1345_1 : CycleData E W := ⟨3,![2,20,21,17,7],![3,8,18,38,16]⟩
def cycle1345_2 : CycleData E W := ⟨3,![10,15,3,23,14],![4,26,6,8,28]⟩
def cycle1345_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1345_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle1345_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1345 : PartitionData E W := ⟨6,![cycle1345_0,cycle1345_1,cycle1345_2,cycle1345_3,cycle1345_4,cycle1345_5]⟩
lemma valid_data1345 : data1345.Valid src1345 dst1345 Finset.univ := by decide +kernel

def src1346 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst1346 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle1346_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1346_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1346_2 : CycleData E W := ⟨3,![10,15,3,20,14],![4,26,6,8,28]⟩
def cycle1346_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1346_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle1346_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data1346 : PartitionData E W := ⟨6,![cycle1346_0,cycle1346_1,cycle1346_2,cycle1346_3,cycle1346_4,cycle1346_5]⟩
lemma valid_data1346 : data1346.Valid src1346 dst1346 Finset.univ := by decide +kernel

def src1347 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst1347 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1347_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1347_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1347_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle1347_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1347_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle1347_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data1347 : PartitionData E W := ⟨6,![cycle1347_0,cycle1347_1,cycle1347_2,cycle1347_3,cycle1347_4,cycle1347_5]⟩
lemma valid_data1347 : data1347.Valid src1347 dst1347 Finset.univ := by decide +kernel

def src1348 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst1348 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle1348_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1348_1 : CycleData E W := ⟨3,![2,20,21,17,7],![3,8,18,38,16]⟩
def cycle1348_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1348_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1348_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle1348_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data1348 : PartitionData E W := ⟨6,![cycle1348_0,cycle1348_1,cycle1348_2,cycle1348_3,cycle1348_4,cycle1348_5]⟩
lemma valid_data1348 : data1348.Valid src1348 dst1348 Finset.univ := by decide +kernel

def src1349 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst1349 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle1349_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1349_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1349_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1349_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1349_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle1349_5 : CycleData E W := ⟨3,![10,16,22,21,14],![4,26,38,18,28]⟩
def data1349 : PartitionData E W := ⟨6,![cycle1349_0,cycle1349_1,cycle1349_2,cycle1349_3,cycle1349_4,cycle1349_5]⟩
lemma valid_data1349 : data1349.Valid src1349 dst1349 Finset.univ := by decide +kernel

def src1350 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst1350 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle1350_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1350_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1350_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1350_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1350_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1350_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data1350 : PartitionData E W := ⟨6,![cycle1350_0,cycle1350_1,cycle1350_2,cycle1350_3,cycle1350_4,cycle1350_5]⟩
lemma valid_data1350 : data1350.Valid src1350 dst1350 Finset.univ := by decide +kernel

def src1351 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst1351 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle1351_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1351_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1351_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1351_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1351_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1351_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data1351 : PartitionData E W := ⟨6,![cycle1351_0,cycle1351_1,cycle1351_2,cycle1351_3,cycle1351_4,cycle1351_5]⟩
lemma valid_data1351 : data1351.Valid src1351 dst1351 Finset.univ := by decide +kernel

def src1352 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst1352 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle1352_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1352_1 : CycleData E W := ⟨3,![2,20,13,16,7],![3,8,28,27,16]⟩
def cycle1352_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1352_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1352_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle1352_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def data1352 : PartitionData E W := ⟨6,![cycle1352_0,cycle1352_1,cycle1352_2,cycle1352_3,cycle1352_4,cycle1352_5]⟩
lemma valid_data1352 : data1352.Valid src1352 dst1352 Finset.univ := by decide +kernel

def src1353 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst1353 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle1353_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1353_1 : CycleData E W := ⟨2,![1,14,17,7],![3,4,27,16]⟩
def cycle1353_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1353_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1353_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1353_5 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle1353_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1353 : PartitionData E W := ⟨7,![cycle1353_0,cycle1353_1,cycle1353_2,cycle1353_3,cycle1353_4,cycle1353_5,cycle1353_6]⟩
lemma valid_data1353 : data1353.Valid src1353 dst1353 Finset.univ := by decide +kernel

def src1354 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst1354 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle1354_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1354_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1354_2 : CycleData E W := ⟨3,![3,23,12,11,15],![6,8,28,14,26]⟩
def cycle1354_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1354_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1354_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1354 : PartitionData E W := ⟨6,![cycle1354_0,cycle1354_1,cycle1354_2,cycle1354_3,cycle1354_4,cycle1354_5]⟩
lemma valid_data1354 : data1354.Valid src1354 dst1354 Finset.univ := by decide +kernel

def src1355 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst1355 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle1355_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1355_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,16]⟩
def cycle1355_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1355_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1355_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1355_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data1355 : PartitionData E W := ⟨6,![cycle1355_0,cycle1355_1,cycle1355_2,cycle1355_3,cycle1355_4,cycle1355_5]⟩
lemma valid_data1355 : data1355.Valid src1355 dst1355 Finset.univ := by decide +kernel

def src1356 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst1356 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1356_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1356_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle1356_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1356_3 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1356_4 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1356_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data1356 : PartitionData E W := ⟨6,![cycle1356_0,cycle1356_1,cycle1356_2,cycle1356_3,cycle1356_4,cycle1356_5]⟩
lemma valid_data1356 : data1356.Valid src1356 dst1356 Finset.univ := by decide +kernel

def src1357 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst1357 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1357_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1357_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle1357_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1357_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1357_4 : CycleData E W := ⟨3,![4,15,16,21,9],![2,6,26,38,18]⟩
def cycle1357_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data1357 : PartitionData E W := ⟨6,![cycle1357_0,cycle1357_1,cycle1357_2,cycle1357_3,cycle1357_4,cycle1357_5]⟩
lemma valid_data1357 : data1357.Valid src1357 dst1357 Finset.univ := by decide +kernel

def src1358 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst1358 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1358_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1358_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle1358_2 : CycleData E W := ⟨2,![2,23,22,8],![3,8,38,18]⟩
def cycle1358_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1358_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1358_5 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def data1358 : PartitionData E W := ⟨6,![cycle1358_0,cycle1358_1,cycle1358_2,cycle1358_3,cycle1358_4,cycle1358_5]⟩
lemma valid_data1358 : data1358.Valid src1358 dst1358 Finset.univ := by decide +kernel

def src1359 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst1359 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1359_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1359_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1359_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1359_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1359_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1359_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1359 : PartitionData E W := ⟨6,![cycle1359_0,cycle1359_1,cycle1359_2,cycle1359_3,cycle1359_4,cycle1359_5]⟩
lemma valid_data1359 : data1359.Valid src1359 dst1359 Finset.univ := by decide +kernel

def src1360 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst1360 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1360_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1360_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1360_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1360_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1360_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1360_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1360 : PartitionData E W := ⟨6,![cycle1360_0,cycle1360_1,cycle1360_2,cycle1360_3,cycle1360_4,cycle1360_5]⟩
lemma valid_data1360 : data1360.Valid src1360 dst1360 Finset.univ := by decide +kernel

def src1361 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst1361 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1361_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle1361_1 : CycleData E W := ⟨2,![1,10,17,7],![3,4,26,16]⟩
def cycle1361_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle1361_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1361_4 : CycleData E W := ⟨3,![5,11,18,22,9],![2,14,26,38,18]⟩
def cycle1361_5 : CycleData E W := ⟨2,![6,16,13,12],![14,16,27,28]⟩
def data1361 : PartitionData E W := ⟨6,![cycle1361_0,cycle1361_1,cycle1361_2,cycle1361_3,cycle1361_4,cycle1361_5]⟩
lemma valid_data1361 : data1361.Valid src1361 dst1361 Finset.univ := by decide +kernel

def src1362 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst1362 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle1362_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1362_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1362_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1362_3 : CycleData E W := ⟨3,![4,15,11,21,9],![2,6,26,28,18]⟩
def cycle1362_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1362_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1362 : PartitionData E W := ⟨6,![cycle1362_0,cycle1362_1,cycle1362_2,cycle1362_3,cycle1362_4,cycle1362_5]⟩
lemma valid_data1362 : data1362.Valid src1362 dst1362 Finset.univ := by decide +kernel

def src1363 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst1363 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle1363_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1363_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1363_2 : CycleData E W := ⟨2,![3,23,11,15],![6,8,28,26]⟩
def cycle1363_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1363_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1363_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1363 : PartitionData E W := ⟨6,![cycle1363_0,cycle1363_1,cycle1363_2,cycle1363_3,cycle1363_4,cycle1363_5]⟩
lemma valid_data1363 : data1363.Valid src1363 dst1363 Finset.univ := by decide +kernel

def src1364 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst1364 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle1364_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1364_1 : CycleData E W := ⟨2,![1,14,17,7],![3,4,27,16]⟩
def cycle1364_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle1364_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1364_4 : CycleData E W := ⟨3,![5,13,18,22,9],![2,14,27,38,18]⟩
def cycle1364_5 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def data1364 : PartitionData E W := ⟨6,![cycle1364_0,cycle1364_1,cycle1364_2,cycle1364_3,cycle1364_4,cycle1364_5]⟩
lemma valid_data1364 : data1364.Valid src1364 dst1364 Finset.univ := by decide +kernel

def src1365 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst1365 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle1365_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1365_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1365_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1365_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1365_4 : CycleData E W := ⟨3,![4,15,11,21,9],![2,6,26,28,18]⟩
def cycle1365_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data1365 : PartitionData E W := ⟨6,![cycle1365_0,cycle1365_1,cycle1365_2,cycle1365_3,cycle1365_4,cycle1365_5]⟩
lemma valid_data1365 : data1365.Valid src1365 dst1365 Finset.univ := by decide +kernel

def src1366 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst1366 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle1366_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1366_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1366_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1366_3 : CycleData E W := ⟨2,![3,23,11,15],![6,8,28,26]⟩
def cycle1366_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle1366_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data1366 : PartitionData E W := ⟨6,![cycle1366_0,cycle1366_1,cycle1366_2,cycle1366_3,cycle1366_4,cycle1366_5]⟩
lemma valid_data1366 : data1366.Valid src1366 dst1366 Finset.univ := by decide +kernel

def src1367 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst1367 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle1367_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1367_1 : CycleData E W := ⟨2,![1,10,16,7],![3,4,26,16]⟩
def cycle1367_2 : CycleData E W := ⟨2,![2,23,22,8],![3,8,38,18]⟩
def cycle1367_3 : CycleData E W := ⟨2,![3,20,11,15],![6,8,28,26]⟩
def cycle1367_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1367_5 : CycleData E W := ⟨2,![6,17,18,13],![14,16,38,27]⟩
def data1367 : PartitionData E W := ⟨6,![cycle1367_0,cycle1367_1,cycle1367_2,cycle1367_3,cycle1367_4,cycle1367_5]⟩
lemma valid_data1367 : data1367.Valid src1367 dst1367 Finset.univ := by decide +kernel

def src1368 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst1368 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle1368_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle1368_1 : CycleData E W := ⟨2,![1,10,17,7],![3,4,26,16]⟩
def cycle1368_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1368_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1368_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle1368_5 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle1368_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1368 : PartitionData E W := ⟨7,![cycle1368_0,cycle1368_1,cycle1368_2,cycle1368_3,cycle1368_4,cycle1368_5,cycle1368_6]⟩
lemma valid_data1368 : data1368.Valid src1368 dst1368 Finset.univ := by decide +kernel

def src1369 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst1369 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle1369_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1369_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1369_2 : CycleData E W := ⟨3,![3,23,12,13,15],![6,8,28,14,27]⟩
def cycle1369_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1369_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1369_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1369 : PartitionData E W := ⟨6,![cycle1369_0,cycle1369_1,cycle1369_2,cycle1369_3,cycle1369_4,cycle1369_5]⟩
lemma valid_data1369 : data1369.Valid src1369 dst1369 Finset.univ := by decide +kernel

def src1370 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst1370 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle1370_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1370_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,16]⟩
def cycle1370_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1370_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1370_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1370_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data1370 : PartitionData E W := ⟨6,![cycle1370_0,cycle1370_1,cycle1370_2,cycle1370_3,cycle1370_4,cycle1370_5]⟩
lemma valid_data1370 : data1370.Valid src1370 dst1370 Finset.univ := by decide +kernel

def src1371 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst1371 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1371_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1371_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1371_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1371_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1371_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1371_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data1371 : PartitionData E W := ⟨6,![cycle1371_0,cycle1371_1,cycle1371_2,cycle1371_3,cycle1371_4,cycle1371_5]⟩
lemma valid_data1371 : data1371.Valid src1371 dst1371 Finset.univ := by decide +kernel

def src1372 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst1372 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1372_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle1372_1 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle1372_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1372_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1372_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1372_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data1372 : PartitionData E W := ⟨6,![cycle1372_0,cycle1372_1,cycle1372_2,cycle1372_3,cycle1372_4,cycle1372_5]⟩
lemma valid_data1372 : data1372.Valid src1372 dst1372 Finset.univ := by decide +kernel

def src1373 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst1373 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1373_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1373_1 : CycleData E W := ⟨3,![2,20,13,16,7],![3,8,28,26,16]⟩
def cycle1373_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1373_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1373_4 : CycleData E W := ⟨1,![6,17,11],![14,16,27]⟩
def cycle1373_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data1373 : PartitionData E W := ⟨6,![cycle1373_0,cycle1373_1,cycle1373_2,cycle1373_3,cycle1373_4,cycle1373_5]⟩
lemma valid_data1373 : data1373.Valid src1373 dst1373 Finset.univ := by decide +kernel

def src1374 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst1374 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1374_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1374_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1374_2 : CycleData E W := ⟨3,![3,20,21,13,15],![6,8,18,28,26]⟩
def cycle1374_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1374_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle1374_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1374 : PartitionData E W := ⟨6,![cycle1374_0,cycle1374_1,cycle1374_2,cycle1374_3,cycle1374_4,cycle1374_5]⟩
lemma valid_data1374 : data1374.Valid src1374 dst1374 Finset.univ := by decide +kernel

def src1375 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst1375 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1375_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1375_1 : CycleData E W := ⟨3,![2,20,21,17,7],![3,8,18,38,16]⟩
def cycle1375_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1375_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1375_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle1375_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1375 : PartitionData E W := ⟨6,![cycle1375_0,cycle1375_1,cycle1375_2,cycle1375_3,cycle1375_4,cycle1375_5]⟩
lemma valid_data1375 : data1375.Valid src1375 dst1375 Finset.univ := by decide +kernel

def src1376 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst1376 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1376_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1376_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1376_2 : CycleData E W := ⟨2,![3,20,13,15],![6,8,28,26]⟩
def cycle1376_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1376_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle1376_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data1376 : PartitionData E W := ⟨6,![cycle1376_0,cycle1376_1,cycle1376_2,cycle1376_3,cycle1376_4,cycle1376_5]⟩
lemma valid_data1376 : data1376.Valid src1376 dst1376 Finset.univ := by decide +kernel

def src1377 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst1377 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle1377_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1377_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1377_2 : CycleData E W := ⟨4,![10,19,3,20,21,14],![4,27,6,8,18,28]⟩
def cycle1377_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1377_4 : CycleData E W := ⟨1,![6,18,11],![14,16,27]⟩
def cycle1377_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1377 : PartitionData E W := ⟨6,![cycle1377_0,cycle1377_1,cycle1377_2,cycle1377_3,cycle1377_4,cycle1377_5]⟩
lemma valid_data1377 : data1377.Valid src1377 dst1377 Finset.univ := by decide +kernel

def src1378 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst1378 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle1378_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1378_1 : CycleData E W := ⟨3,![2,20,21,17,7],![3,8,18,38,16]⟩
def cycle1378_2 : CycleData E W := ⟨3,![10,19,3,23,14],![4,27,6,8,28]⟩
def cycle1378_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1378_4 : CycleData E W := ⟨1,![6,18,11],![14,16,27]⟩
def cycle1378_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1378 : PartitionData E W := ⟨6,![cycle1378_0,cycle1378_1,cycle1378_2,cycle1378_3,cycle1378_4,cycle1378_5]⟩
lemma valid_data1378 : data1378.Valid src1378 dst1378 Finset.univ := by decide +kernel

def src1379 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst1379 : E → W := ![4,3,8,6,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle1379_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1379_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle1379_2 : CycleData E W := ⟨3,![10,19,3,20,14],![4,27,6,8,28]⟩
def cycle1379_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1379_4 : CycleData E W := ⟨1,![6,18,11],![14,16,27]⟩
def cycle1379_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data1379 : PartitionData E W := ⟨6,![cycle1379_0,cycle1379_1,cycle1379_2,cycle1379_3,cycle1379_4,cycle1379_5]⟩
lemma valid_data1379 : data1379.Valid src1379 dst1379 Finset.univ := by decide +kernel

def src1380 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst1380 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1380_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1380_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1380_2 : CycleData E W := ⟨4,![4,3,23,16,11,5],![2,6,8,38,26,14]⟩
def cycle1380_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1380_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1380_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1380 : PartitionData E W := ⟨6,![cycle1380_0,cycle1380_1,cycle1380_2,cycle1380_3,cycle1380_4,cycle1380_5]⟩
lemma valid_data1380 : data1380.Valid src1380 dst1380 Finset.univ := by decide +kernel

def src1381 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst1381 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle1381_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1381_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1381_2 : CycleData E W := ⟨4,![4,3,23,14,10,5],![2,6,8,28,4,14]⟩
def cycle1381_3 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle1381_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1381_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1381 : PartitionData E W := ⟨6,![cycle1381_0,cycle1381_1,cycle1381_2,cycle1381_3,cycle1381_4,cycle1381_5]⟩
lemma valid_data1381 : data1381.Valid src1381 dst1381 Finset.univ := by decide +kernel

def src1382 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst1382 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle1382_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1382_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1382_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1382_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1382_4 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1382_5 : CycleData E W := ⟨2,![17,16,12,18],![16,38,26,27]⟩
def data1382 : PartitionData E W := ⟨6,![cycle1382_0,cycle1382_1,cycle1382_2,cycle1382_3,cycle1382_4,cycle1382_5]⟩
lemma valid_data1382 : data1382.Valid src1382 dst1382 Finset.univ := by decide +kernel

def src1383 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst1383 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle1383_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1383_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1383_2 : CycleData E W := ⟨4,![4,3,23,18,11,5],![2,6,8,38,26,14]⟩
def cycle1383_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1383_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle1383_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data1383 : PartitionData E W := ⟨6,![cycle1383_0,cycle1383_1,cycle1383_2,cycle1383_3,cycle1383_4,cycle1383_5]⟩
lemma valid_data1383 : data1383.Valid src1383 dst1383 Finset.univ := by decide +kernel

def src1384 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst1384 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle1384_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1384_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1384_2 : CycleData E W := ⟨4,![4,3,23,14,10,5],![2,6,8,28,4,14]⟩
def cycle1384_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle1384_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle1384_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data1384 : PartitionData E W := ⟨6,![cycle1384_0,cycle1384_1,cycle1384_2,cycle1384_3,cycle1384_4,cycle1384_5]⟩
lemma valid_data1384 : data1384.Valid src1384 dst1384 Finset.univ := by decide +kernel

def src1385 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst1385 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle1385_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1385_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1385_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1385_3 : CycleData E W := ⟨4,![4,15,13,14,10,5],![2,6,27,28,4,14]⟩
def cycle1385_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle1385_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data1385 : PartitionData E W := ⟨6,![cycle1385_0,cycle1385_1,cycle1385_2,cycle1385_3,cycle1385_4,cycle1385_5]⟩
lemma valid_data1385 : data1385.Valid src1385 dst1385 Finset.univ := by decide +kernel

def src1386 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst1386 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle1386_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1386_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,27,16]⟩
def cycle1386_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1386_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1386_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle1386_5 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle1386_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1386 : PartitionData E W := ⟨7,![cycle1386_0,cycle1386_1,cycle1386_2,cycle1386_3,cycle1386_4,cycle1386_5,cycle1386_6]⟩
lemma valid_data1386 : data1386.Valid src1386 dst1386 Finset.univ := by decide +kernel

def src1387 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst1387 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle1387_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1387_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1387_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1387_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1387_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle1387_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1387 : PartitionData E W := ⟨6,![cycle1387_0,cycle1387_1,cycle1387_2,cycle1387_3,cycle1387_4,cycle1387_5]⟩
lemma valid_data1387 : data1387.Valid src1387 dst1387 Finset.univ := by decide +kernel

def src1388 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst1388 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle1388_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1388_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1388_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1388_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1388_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,27]⟩
def cycle1388_5 : CycleData E W := ⟨2,![16,12,13,17],![16,26,28,27]⟩
def data1388 : PartitionData E W := ⟨6,![cycle1388_0,cycle1388_1,cycle1388_2,cycle1388_3,cycle1388_4,cycle1388_5]⟩
lemma valid_data1388 : data1388.Valid src1388 dst1388 Finset.univ := by decide +kernel

def src1389 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst1389 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle1389_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1389_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1389_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1389_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1389_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle1389_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1389 : PartitionData E W := ⟨6,![cycle1389_0,cycle1389_1,cycle1389_2,cycle1389_3,cycle1389_4,cycle1389_5]⟩
lemma valid_data1389 : data1389.Valid src1389 dst1389 Finset.univ := by decide +kernel

def src1390 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst1390 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle1390_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1390_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1390_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1390_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1390_4 : CycleData E W := ⟨3,![6,21,17,16,11],![14,18,38,16,26]⟩
def cycle1390_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1390 : PartitionData E W := ⟨6,![cycle1390_0,cycle1390_1,cycle1390_2,cycle1390_3,cycle1390_4,cycle1390_5]⟩
lemma valid_data1390 : data1390.Valid src1390 dst1390 Finset.univ := by decide +kernel

def src1391 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst1391 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle1391_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1391_1 : CycleData E W := ⟨3,![1,14,18,17,8],![3,4,27,38,16]⟩
def cycle1391_2 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1391_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1391_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle1391_5 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def data1391 : PartitionData E W := ⟨6,![cycle1391_0,cycle1391_1,cycle1391_2,cycle1391_3,cycle1391_4,cycle1391_5]⟩
lemma valid_data1391 : data1391.Valid src1391 dst1391 Finset.univ := by decide +kernel

def src1392 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst1392 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1392_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1392_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1392_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1392_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1392_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle1392_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1392 : PartitionData E W := ⟨6,![cycle1392_0,cycle1392_1,cycle1392_2,cycle1392_3,cycle1392_4,cycle1392_5]⟩
lemma valid_data1392 : data1392.Valid src1392 dst1392 Finset.univ := by decide +kernel

def src1393 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst1393 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1393_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1393_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1393_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1393_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1393_4 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle1393_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1393 : PartitionData E W := ⟨6,![cycle1393_0,cycle1393_1,cycle1393_2,cycle1393_3,cycle1393_4,cycle1393_5]⟩
lemma valid_data1393 : data1393.Valid src1393 dst1393 Finset.univ := by decide +kernel

def src1394 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst1394 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1394_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1394_1 : CycleData E W := ⟨2,![1,14,18,8],![3,4,27,16]⟩
def cycle1394_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1394_3 : CycleData E W := ⟨3,![4,3,23,17,9],![2,6,8,38,16]⟩
def cycle1394_4 : CycleData E W := ⟨2,![6,22,16,11],![14,18,38,26]⟩
def cycle1394_5 : CycleData E W := ⟨2,![15,12,13,19],![6,26,28,27]⟩
def data1394 : PartitionData E W := ⟨6,![cycle1394_0,cycle1394_1,cycle1394_2,cycle1394_3,cycle1394_4,cycle1394_5]⟩
lemma valid_data1394 : data1394.Valid src1394 dst1394 Finset.univ := by decide +kernel

def src1395 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst1395 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1395_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1395_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1395_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1395_3 : CycleData E W := ⟨3,![4,15,14,10,5],![2,6,27,4,14]⟩
def cycle1395_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle1395_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data1395 : PartitionData E W := ⟨6,![cycle1395_0,cycle1395_1,cycle1395_2,cycle1395_3,cycle1395_4,cycle1395_5]⟩
lemma valid_data1395 : data1395.Valid src1395 dst1395 Finset.univ := by decide +kernel

def src1396 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst1396 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1396_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1396_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1396_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1396_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1396_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle1396_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data1396 : PartitionData E W := ⟨6,![cycle1396_0,cycle1396_1,cycle1396_2,cycle1396_3,cycle1396_4,cycle1396_5]⟩
lemma valid_data1396 : data1396.Valid src1396 dst1396 Finset.univ := by decide +kernel

def src1397 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst1397 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1397_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1397_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1397_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1397_3 : CycleData E W := ⟨3,![4,15,14,10,5],![2,6,27,4,14]⟩
def cycle1397_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle1397_5 : CycleData E W := ⟨2,![16,13,12,17],![16,27,28,26]⟩
def data1397 : PartitionData E W := ⟨6,![cycle1397_0,cycle1397_1,cycle1397_2,cycle1397_3,cycle1397_4,cycle1397_5]⟩
lemma valid_data1397 : data1397.Valid src1397 dst1397 Finset.univ := by decide +kernel

def src1398 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst1398 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1398_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1398_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1398_2 : CycleData E W := ⟨4,![4,3,23,18,11,5],![2,6,8,38,27,14]⟩
def cycle1398_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1398_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle1398_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data1398 : PartitionData E W := ⟨6,![cycle1398_0,cycle1398_1,cycle1398_2,cycle1398_3,cycle1398_4,cycle1398_5]⟩
lemma valid_data1398 : data1398.Valid src1398 dst1398 Finset.univ := by decide +kernel

def src1399 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst1399 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1399_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1399_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1399_2 : CycleData E W := ⟨4,![4,3,23,14,10,5],![2,6,8,28,4,14]⟩
def cycle1399_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def cycle1399_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle1399_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data1399 : PartitionData E W := ⟨6,![cycle1399_0,cycle1399_1,cycle1399_2,cycle1399_3,cycle1399_4,cycle1399_5]⟩
lemma valid_data1399 : data1399.Valid src1399 dst1399 Finset.univ := by decide +kernel

def lookupB6 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data1200 else (if j < 2 then data1201 else data1202)) else (if j < 4 then data1203 else (if j < 5 then data1204 else data1205))) else (if j < 9 then (if j < 7 then data1206 else (if j < 8 then data1207 else data1208)) else (if j < 10 then data1209 else (if j < 11 then data1210 else data1211)))) else (if j < 18 then (if j < 15 then (if j < 13 then data1212 else (if j < 14 then data1213 else data1214)) else (if j < 16 then data1215 else (if j < 17 then data1216 else data1217))) else (if j < 21 then (if j < 19 then data1218 else (if j < 20 then data1219 else data1220)) else (if j < 23 then (if j < 22 then data1221 else data1222) else (if j < 24 then data1223 else data1224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data1225 else (if j < 27 then data1226 else data1227)) else (if j < 29 then data1228 else (if j < 30 then data1229 else data1230))) else (if j < 34 then (if j < 32 then data1231 else (if j < 33 then data1232 else data1233)) else (if j < 35 then data1234 else (if j < 36 then data1235 else data1236)))) else (if j < 43 then (if j < 40 then (if j < 38 then data1237 else (if j < 39 then data1238 else data1239)) else (if j < 41 then data1240 else (if j < 42 then data1241 else data1242))) else (if j < 46 then (if j < 44 then data1243 else (if j < 45 then data1244 else data1245)) else (if j < 48 then (if j < 47 then data1246 else data1247) else (if j < 49 then data1248 else data1249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data1250 else (if j < 52 then data1251 else data1252)) else (if j < 54 then data1253 else (if j < 55 then data1254 else data1255))) else (if j < 59 then (if j < 57 then data1256 else (if j < 58 then data1257 else data1258)) else (if j < 60 then data1259 else (if j < 61 then data1260 else data1261)))) else (if j < 68 then (if j < 65 then (if j < 63 then data1262 else (if j < 64 then data1263 else data1264)) else (if j < 66 then data1265 else (if j < 67 then data1266 else data1267))) else (if j < 71 then (if j < 69 then data1268 else (if j < 70 then data1269 else data1270)) else (if j < 73 then (if j < 72 then data1271 else data1272) else (if j < 74 then data1273 else data1274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data1275 else (if j < 77 then data1276 else data1277)) else (if j < 79 then data1278 else (if j < 80 then data1279 else data1280))) else (if j < 84 then (if j < 82 then data1281 else (if j < 83 then data1282 else data1283)) else (if j < 85 then data1284 else (if j < 86 then data1285 else data1286)))) else (if j < 93 then (if j < 90 then (if j < 88 then data1287 else (if j < 89 then data1288 else data1289)) else (if j < 91 then data1290 else (if j < 92 then data1291 else data1292))) else (if j < 96 then (if j < 94 then data1293 else (if j < 95 then data1294 else data1295)) else (if j < 98 then (if j < 97 then data1296 else data1297) else (if j < 99 then data1298 else data1299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data1300 else (if j < 102 then data1301 else data1302)) else (if j < 104 then data1303 else (if j < 105 then data1304 else data1305))) else (if j < 109 then (if j < 107 then data1306 else (if j < 108 then data1307 else data1308)) else (if j < 110 then data1309 else (if j < 111 then data1310 else data1311)))) else (if j < 118 then (if j < 115 then (if j < 113 then data1312 else (if j < 114 then data1313 else data1314)) else (if j < 116 then data1315 else (if j < 117 then data1316 else data1317))) else (if j < 121 then (if j < 119 then data1318 else (if j < 120 then data1319 else data1320)) else (if j < 123 then (if j < 122 then data1321 else data1322) else (if j < 124 then data1323 else data1324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data1325 else (if j < 127 then data1326 else data1327)) else (if j < 129 then data1328 else (if j < 130 then data1329 else data1330))) else (if j < 134 then (if j < 132 then data1331 else (if j < 133 then data1332 else data1333)) else (if j < 135 then data1334 else (if j < 136 then data1335 else data1336)))) else (if j < 143 then (if j < 140 then (if j < 138 then data1337 else (if j < 139 then data1338 else data1339)) else (if j < 141 then data1340 else (if j < 142 then data1341 else data1342))) else (if j < 146 then (if j < 144 then data1343 else (if j < 145 then data1344 else data1345)) else (if j < 148 then (if j < 147 then data1346 else data1347) else (if j < 149 then data1348 else data1349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data1350 else (if j < 152 then data1351 else data1352)) else (if j < 154 then data1353 else (if j < 155 then data1354 else data1355))) else (if j < 159 then (if j < 157 then data1356 else (if j < 158 then data1357 else data1358)) else (if j < 160 then data1359 else (if j < 161 then data1360 else data1361)))) else (if j < 168 then (if j < 165 then (if j < 163 then data1362 else (if j < 164 then data1363 else data1364)) else (if j < 166 then data1365 else (if j < 167 then data1366 else data1367))) else (if j < 171 then (if j < 169 then data1368 else (if j < 170 then data1369 else data1370)) else (if j < 173 then (if j < 172 then data1371 else data1372) else (if j < 174 then data1373 else data1374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data1375 else (if j < 177 then data1376 else data1377)) else (if j < 179 then data1378 else (if j < 180 then data1379 else data1380))) else (if j < 184 then (if j < 182 then data1381 else (if j < 183 then data1382 else data1383)) else (if j < 185 then data1384 else (if j < 186 then data1385 else data1386)))) else (if j < 193 then (if j < 190 then (if j < 188 then data1387 else (if j < 189 then data1388 else data1389)) else (if j < 191 then data1390 else (if j < 192 then data1391 else data1392))) else (if j < 196 then (if j < 194 then data1393 else (if j < 195 then data1394 else data1395)) else (if j < 198 then (if j < 197 then data1396 else data1397) else (if j < 199 then data1398 else data1399))))))))

def srcTableB6 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src1200 else (if j < 2 then src1201 else src1202)) else (if j < 4 then src1203 else (if j < 5 then src1204 else src1205))) else (if j < 9 then (if j < 7 then src1206 else (if j < 8 then src1207 else src1208)) else (if j < 10 then src1209 else (if j < 11 then src1210 else src1211)))) else (if j < 18 then (if j < 15 then (if j < 13 then src1212 else (if j < 14 then src1213 else src1214)) else (if j < 16 then src1215 else (if j < 17 then src1216 else src1217))) else (if j < 21 then (if j < 19 then src1218 else (if j < 20 then src1219 else src1220)) else (if j < 23 then (if j < 22 then src1221 else src1222) else (if j < 24 then src1223 else src1224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src1225 else (if j < 27 then src1226 else src1227)) else (if j < 29 then src1228 else (if j < 30 then src1229 else src1230))) else (if j < 34 then (if j < 32 then src1231 else (if j < 33 then src1232 else src1233)) else (if j < 35 then src1234 else (if j < 36 then src1235 else src1236)))) else (if j < 43 then (if j < 40 then (if j < 38 then src1237 else (if j < 39 then src1238 else src1239)) else (if j < 41 then src1240 else (if j < 42 then src1241 else src1242))) else (if j < 46 then (if j < 44 then src1243 else (if j < 45 then src1244 else src1245)) else (if j < 48 then (if j < 47 then src1246 else src1247) else (if j < 49 then src1248 else src1249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src1250 else (if j < 52 then src1251 else src1252)) else (if j < 54 then src1253 else (if j < 55 then src1254 else src1255))) else (if j < 59 then (if j < 57 then src1256 else (if j < 58 then src1257 else src1258)) else (if j < 60 then src1259 else (if j < 61 then src1260 else src1261)))) else (if j < 68 then (if j < 65 then (if j < 63 then src1262 else (if j < 64 then src1263 else src1264)) else (if j < 66 then src1265 else (if j < 67 then src1266 else src1267))) else (if j < 71 then (if j < 69 then src1268 else (if j < 70 then src1269 else src1270)) else (if j < 73 then (if j < 72 then src1271 else src1272) else (if j < 74 then src1273 else src1274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src1275 else (if j < 77 then src1276 else src1277)) else (if j < 79 then src1278 else (if j < 80 then src1279 else src1280))) else (if j < 84 then (if j < 82 then src1281 else (if j < 83 then src1282 else src1283)) else (if j < 85 then src1284 else (if j < 86 then src1285 else src1286)))) else (if j < 93 then (if j < 90 then (if j < 88 then src1287 else (if j < 89 then src1288 else src1289)) else (if j < 91 then src1290 else (if j < 92 then src1291 else src1292))) else (if j < 96 then (if j < 94 then src1293 else (if j < 95 then src1294 else src1295)) else (if j < 98 then (if j < 97 then src1296 else src1297) else (if j < 99 then src1298 else src1299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src1300 else (if j < 102 then src1301 else src1302)) else (if j < 104 then src1303 else (if j < 105 then src1304 else src1305))) else (if j < 109 then (if j < 107 then src1306 else (if j < 108 then src1307 else src1308)) else (if j < 110 then src1309 else (if j < 111 then src1310 else src1311)))) else (if j < 118 then (if j < 115 then (if j < 113 then src1312 else (if j < 114 then src1313 else src1314)) else (if j < 116 then src1315 else (if j < 117 then src1316 else src1317))) else (if j < 121 then (if j < 119 then src1318 else (if j < 120 then src1319 else src1320)) else (if j < 123 then (if j < 122 then src1321 else src1322) else (if j < 124 then src1323 else src1324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src1325 else (if j < 127 then src1326 else src1327)) else (if j < 129 then src1328 else (if j < 130 then src1329 else src1330))) else (if j < 134 then (if j < 132 then src1331 else (if j < 133 then src1332 else src1333)) else (if j < 135 then src1334 else (if j < 136 then src1335 else src1336)))) else (if j < 143 then (if j < 140 then (if j < 138 then src1337 else (if j < 139 then src1338 else src1339)) else (if j < 141 then src1340 else (if j < 142 then src1341 else src1342))) else (if j < 146 then (if j < 144 then src1343 else (if j < 145 then src1344 else src1345)) else (if j < 148 then (if j < 147 then src1346 else src1347) else (if j < 149 then src1348 else src1349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src1350 else (if j < 152 then src1351 else src1352)) else (if j < 154 then src1353 else (if j < 155 then src1354 else src1355))) else (if j < 159 then (if j < 157 then src1356 else (if j < 158 then src1357 else src1358)) else (if j < 160 then src1359 else (if j < 161 then src1360 else src1361)))) else (if j < 168 then (if j < 165 then (if j < 163 then src1362 else (if j < 164 then src1363 else src1364)) else (if j < 166 then src1365 else (if j < 167 then src1366 else src1367))) else (if j < 171 then (if j < 169 then src1368 else (if j < 170 then src1369 else src1370)) else (if j < 173 then (if j < 172 then src1371 else src1372) else (if j < 174 then src1373 else src1374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src1375 else (if j < 177 then src1376 else src1377)) else (if j < 179 then src1378 else (if j < 180 then src1379 else src1380))) else (if j < 184 then (if j < 182 then src1381 else (if j < 183 then src1382 else src1383)) else (if j < 185 then src1384 else (if j < 186 then src1385 else src1386)))) else (if j < 193 then (if j < 190 then (if j < 188 then src1387 else (if j < 189 then src1388 else src1389)) else (if j < 191 then src1390 else (if j < 192 then src1391 else src1392))) else (if j < 196 then (if j < 194 then src1393 else (if j < 195 then src1394 else src1395)) else (if j < 198 then (if j < 197 then src1396 else src1397) else (if j < 199 then src1398 else src1399))))))))

def dstTableB6 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst1200 else (if j < 2 then dst1201 else dst1202)) else (if j < 4 then dst1203 else (if j < 5 then dst1204 else dst1205))) else (if j < 9 then (if j < 7 then dst1206 else (if j < 8 then dst1207 else dst1208)) else (if j < 10 then dst1209 else (if j < 11 then dst1210 else dst1211)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst1212 else (if j < 14 then dst1213 else dst1214)) else (if j < 16 then dst1215 else (if j < 17 then dst1216 else dst1217))) else (if j < 21 then (if j < 19 then dst1218 else (if j < 20 then dst1219 else dst1220)) else (if j < 23 then (if j < 22 then dst1221 else dst1222) else (if j < 24 then dst1223 else dst1224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst1225 else (if j < 27 then dst1226 else dst1227)) else (if j < 29 then dst1228 else (if j < 30 then dst1229 else dst1230))) else (if j < 34 then (if j < 32 then dst1231 else (if j < 33 then dst1232 else dst1233)) else (if j < 35 then dst1234 else (if j < 36 then dst1235 else dst1236)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst1237 else (if j < 39 then dst1238 else dst1239)) else (if j < 41 then dst1240 else (if j < 42 then dst1241 else dst1242))) else (if j < 46 then (if j < 44 then dst1243 else (if j < 45 then dst1244 else dst1245)) else (if j < 48 then (if j < 47 then dst1246 else dst1247) else (if j < 49 then dst1248 else dst1249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst1250 else (if j < 52 then dst1251 else dst1252)) else (if j < 54 then dst1253 else (if j < 55 then dst1254 else dst1255))) else (if j < 59 then (if j < 57 then dst1256 else (if j < 58 then dst1257 else dst1258)) else (if j < 60 then dst1259 else (if j < 61 then dst1260 else dst1261)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst1262 else (if j < 64 then dst1263 else dst1264)) else (if j < 66 then dst1265 else (if j < 67 then dst1266 else dst1267))) else (if j < 71 then (if j < 69 then dst1268 else (if j < 70 then dst1269 else dst1270)) else (if j < 73 then (if j < 72 then dst1271 else dst1272) else (if j < 74 then dst1273 else dst1274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst1275 else (if j < 77 then dst1276 else dst1277)) else (if j < 79 then dst1278 else (if j < 80 then dst1279 else dst1280))) else (if j < 84 then (if j < 82 then dst1281 else (if j < 83 then dst1282 else dst1283)) else (if j < 85 then dst1284 else (if j < 86 then dst1285 else dst1286)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst1287 else (if j < 89 then dst1288 else dst1289)) else (if j < 91 then dst1290 else (if j < 92 then dst1291 else dst1292))) else (if j < 96 then (if j < 94 then dst1293 else (if j < 95 then dst1294 else dst1295)) else (if j < 98 then (if j < 97 then dst1296 else dst1297) else (if j < 99 then dst1298 else dst1299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst1300 else (if j < 102 then dst1301 else dst1302)) else (if j < 104 then dst1303 else (if j < 105 then dst1304 else dst1305))) else (if j < 109 then (if j < 107 then dst1306 else (if j < 108 then dst1307 else dst1308)) else (if j < 110 then dst1309 else (if j < 111 then dst1310 else dst1311)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst1312 else (if j < 114 then dst1313 else dst1314)) else (if j < 116 then dst1315 else (if j < 117 then dst1316 else dst1317))) else (if j < 121 then (if j < 119 then dst1318 else (if j < 120 then dst1319 else dst1320)) else (if j < 123 then (if j < 122 then dst1321 else dst1322) else (if j < 124 then dst1323 else dst1324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst1325 else (if j < 127 then dst1326 else dst1327)) else (if j < 129 then dst1328 else (if j < 130 then dst1329 else dst1330))) else (if j < 134 then (if j < 132 then dst1331 else (if j < 133 then dst1332 else dst1333)) else (if j < 135 then dst1334 else (if j < 136 then dst1335 else dst1336)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst1337 else (if j < 139 then dst1338 else dst1339)) else (if j < 141 then dst1340 else (if j < 142 then dst1341 else dst1342))) else (if j < 146 then (if j < 144 then dst1343 else (if j < 145 then dst1344 else dst1345)) else (if j < 148 then (if j < 147 then dst1346 else dst1347) else (if j < 149 then dst1348 else dst1349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst1350 else (if j < 152 then dst1351 else dst1352)) else (if j < 154 then dst1353 else (if j < 155 then dst1354 else dst1355))) else (if j < 159 then (if j < 157 then dst1356 else (if j < 158 then dst1357 else dst1358)) else (if j < 160 then dst1359 else (if j < 161 then dst1360 else dst1361)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst1362 else (if j < 164 then dst1363 else dst1364)) else (if j < 166 then dst1365 else (if j < 167 then dst1366 else dst1367))) else (if j < 171 then (if j < 169 then dst1368 else (if j < 170 then dst1369 else dst1370)) else (if j < 173 then (if j < 172 then dst1371 else dst1372) else (if j < 174 then dst1373 else dst1374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst1375 else (if j < 177 then dst1376 else dst1377)) else (if j < 179 then dst1378 else (if j < 180 then dst1379 else dst1380))) else (if j < 184 then (if j < 182 then dst1381 else (if j < 183 then dst1382 else dst1383)) else (if j < 185 then dst1384 else (if j < 186 then dst1385 else dst1386)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst1387 else (if j < 189 then dst1388 else dst1389)) else (if j < 191 then dst1390 else (if j < 192 then dst1391 else dst1392))) else (if j < 196 then (if j < 194 then dst1393 else (if j < 195 then dst1394 else dst1395)) else (if j < 198 then (if j < 197 then dst1396 else dst1397) else (if j < 199 then dst1398 else dst1399))))))))

def caseB6 (i : Fin 200) : Cases := ⟨1200 + i.val,by have := i.isLt; omega⟩
lemma tableB6_valid (i : Fin 200) :
    (lookupB6 i.val).Valid (srcTableB6 i.val) (dstTableB6 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data1200
  · exact valid_data1201
  · exact valid_data1202
  · exact valid_data1203
  · exact valid_data1204
  · exact valid_data1205
  · exact valid_data1206
  · exact valid_data1207
  · exact valid_data1208
  · exact valid_data1209
  · exact valid_data1210
  · exact valid_data1211
  · exact valid_data1212
  · exact valid_data1213
  · exact valid_data1214
  · exact valid_data1215
  · exact valid_data1216
  · exact valid_data1217
  · exact valid_data1218
  · exact valid_data1219
  · exact valid_data1220
  · exact valid_data1221
  · exact valid_data1222
  · exact valid_data1223
  · exact valid_data1224
  · exact valid_data1225
  · exact valid_data1226
  · exact valid_data1227
  · exact valid_data1228
  · exact valid_data1229
  · exact valid_data1230
  · exact valid_data1231
  · exact valid_data1232
  · exact valid_data1233
  · exact valid_data1234
  · exact valid_data1235
  · exact valid_data1236
  · exact valid_data1237
  · exact valid_data1238
  · exact valid_data1239
  · exact valid_data1240
  · exact valid_data1241
  · exact valid_data1242
  · exact valid_data1243
  · exact valid_data1244
  · exact valid_data1245
  · exact valid_data1246
  · exact valid_data1247
  · exact valid_data1248
  · exact valid_data1249
  · exact valid_data1250
  · exact valid_data1251
  · exact valid_data1252
  · exact valid_data1253
  · exact valid_data1254
  · exact valid_data1255
  · exact valid_data1256
  · exact valid_data1257
  · exact valid_data1258
  · exact valid_data1259
  · exact valid_data1260
  · exact valid_data1261
  · exact valid_data1262
  · exact valid_data1263
  · exact valid_data1264
  · exact valid_data1265
  · exact valid_data1266
  · exact valid_data1267
  · exact valid_data1268
  · exact valid_data1269
  · exact valid_data1270
  · exact valid_data1271
  · exact valid_data1272
  · exact valid_data1273
  · exact valid_data1274
  · exact valid_data1275
  · exact valid_data1276
  · exact valid_data1277
  · exact valid_data1278
  · exact valid_data1279
  · exact valid_data1280
  · exact valid_data1281
  · exact valid_data1282
  · exact valid_data1283
  · exact valid_data1284
  · exact valid_data1285
  · exact valid_data1286
  · exact valid_data1287
  · exact valid_data1288
  · exact valid_data1289
  · exact valid_data1290
  · exact valid_data1291
  · exact valid_data1292
  · exact valid_data1293
  · exact valid_data1294
  · exact valid_data1295
  · exact valid_data1296
  · exact valid_data1297
  · exact valid_data1298
  · exact valid_data1299
  · exact valid_data1300
  · exact valid_data1301
  · exact valid_data1302
  · exact valid_data1303
  · exact valid_data1304
  · exact valid_data1305
  · exact valid_data1306
  · exact valid_data1307
  · exact valid_data1308
  · exact valid_data1309
  · exact valid_data1310
  · exact valid_data1311
  · exact valid_data1312
  · exact valid_data1313
  · exact valid_data1314
  · exact valid_data1315
  · exact valid_data1316
  · exact valid_data1317
  · exact valid_data1318
  · exact valid_data1319
  · exact valid_data1320
  · exact valid_data1321
  · exact valid_data1322
  · exact valid_data1323
  · exact valid_data1324
  · exact valid_data1325
  · exact valid_data1326
  · exact valid_data1327
  · exact valid_data1328
  · exact valid_data1329
  · exact valid_data1330
  · exact valid_data1331
  · exact valid_data1332
  · exact valid_data1333
  · exact valid_data1334
  · exact valid_data1335
  · exact valid_data1336
  · exact valid_data1337
  · exact valid_data1338
  · exact valid_data1339
  · exact valid_data1340
  · exact valid_data1341
  · exact valid_data1342
  · exact valid_data1343
  · exact valid_data1344
  · exact valid_data1345
  · exact valid_data1346
  · exact valid_data1347
  · exact valid_data1348
  · exact valid_data1349
  · exact valid_data1350
  · exact valid_data1351
  · exact valid_data1352
  · exact valid_data1353
  · exact valid_data1354
  · exact valid_data1355
  · exact valid_data1356
  · exact valid_data1357
  · exact valid_data1358
  · exact valid_data1359
  · exact valid_data1360
  · exact valid_data1361
  · exact valid_data1362
  · exact valid_data1363
  · exact valid_data1364
  · exact valid_data1365
  · exact valid_data1366
  · exact valid_data1367
  · exact valid_data1368
  · exact valid_data1369
  · exact valid_data1370
  · exact valid_data1371
  · exact valid_data1372
  · exact valid_data1373
  · exact valid_data1374
  · exact valid_data1375
  · exact valid_data1376
  · exact valid_data1377
  · exact valid_data1378
  · exact valid_data1379
  · exact valid_data1380
  · exact valid_data1381
  · exact valid_data1382
  · exact valid_data1383
  · exact valid_data1384
  · exact valid_data1385
  · exact valid_data1386
  · exact valid_data1387
  · exact valid_data1388
  · exact valid_data1389
  · exact valid_data1390
  · exact valid_data1391
  · exact valid_data1392
  · exact valid_data1393
  · exact valid_data1394
  · exact valid_data1395
  · exact valid_data1396
  · exact valid_data1397
  · exact valid_data1398
  · exact valid_data1399

lemma srcB6_row : ∀ (i : Fin 200) (e : E),
    srcTableB6 i.val e = caseSource (caseB6 i) e := by decide +kernel

lemma dstB6_row : ∀ (i : Fin 200) (e : E),
    dstTableB6 i.val e = caseTarget (caseB6 i) e := by decide +kernel

lemma sizeB6 : ∀ i : Fin 200, (lookupB6 i.val).size ≤ 5 →
    (lookupB6 i.val).size = 2 ∧
      (⟨caseKey (caseB6 i),caseKey_lt (caseB6 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB6 (i : Fin 200) : Certificate (caseB6 i) := by
  refine ⟨lookupB6 i.val,?_,sizeB6 i⟩
  have hv := tableB6_valid i
  rw [funext (srcB6_row i),funext (dstB6_row i)] at hv
  exact hv
lemma certificateInterval6 : FiniteIntervals.Covers CertificateAt 1200 1400 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1200 200 (fun i _ => certificateB6 i)
#print axioms certificateInterval6
end Erdos184Work.FiveRows3

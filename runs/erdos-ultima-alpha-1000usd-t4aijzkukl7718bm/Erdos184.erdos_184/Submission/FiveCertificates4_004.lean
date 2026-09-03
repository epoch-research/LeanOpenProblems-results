import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src200 : E → W := ![2,4,6,3,8,5,2,3,14,16,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst200 : E → W := ![4,6,3,8,5,2,3,14,16,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle200_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle200_1 : CycleData E W := ⟨2,![3,4,13,7],![3,8,5,14]⟩
def cycle200_2 : CycleData E W := ⟨3,![5,12,18,9,10],![2,5,26,16,18]⟩
def cycle200_3 : CycleData E W := ⟨2,![8,17,22,14],![14,16,38,28]⟩
def cycle200_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle200_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data200 : PartitionData E W := ⟨6,![cycle200_0,cycle200_1,cycle200_2,cycle200_3,cycle200_4,cycle200_5]⟩
lemma valid_data200 : data200.Valid src200 dst200 Finset.univ := by decide +kernel

def src201 : E → W := ![2,4,6,3,8,5,2,3,14,16,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst201 : E → W := ![4,6,3,8,5,2,3,14,16,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle201_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle201_1 : CycleData E W := ⟨2,![3,4,13,7],![3,8,5,14]⟩
def cycle201_2 : CycleData E W := ⟨3,![5,12,18,9,10],![2,5,26,16,18]⟩
def cycle201_3 : CycleData E W := ⟨2,![8,19,24,14],![14,16,39,28]⟩
def cycle201_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle201_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data201 : PartitionData E W := ⟨6,![cycle201_0,cycle201_1,cycle201_2,cycle201_3,cycle201_4,cycle201_5]⟩
lemma valid_data201 : data201.Valid src201 dst201 Finset.univ := by decide +kernel

def src202 : E → W := ![2,4,6,3,8,5,2,3,14,18,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst202 : E → W := ![4,6,3,8,5,2,3,14,18,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle202_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle202_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,8,5,26,14]⟩
def cycle202_2 : CycleData E W := ⟨3,![5,14,22,17,10],![2,5,28,38,16]⟩
def cycle202_3 : CycleData E W := ⟨2,![11,8,23,15],![4,14,18,28]⟩
def cycle202_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle202_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data202 : PartitionData E W := ⟨6,![cycle202_0,cycle202_1,cycle202_2,cycle202_3,cycle202_4,cycle202_5]⟩
lemma valid_data202 : data202.Valid src202 dst202 Finset.univ := by decide +kernel

def src203 : E → W := ![2,4,6,3,8,5,2,3,14,18,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst203 : E → W := ![4,6,3,8,5,2,3,14,18,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle203_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle203_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,8,5,26,14]⟩
def cycle203_2 : CycleData E W := ⟨3,![5,14,24,19,10],![2,5,28,39,16]⟩
def cycle203_3 : CycleData E W := ⟨2,![11,8,23,15],![4,14,18,28]⟩
def cycle203_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle203_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data203 : PartitionData E W := ⟨6,![cycle203_0,cycle203_1,cycle203_2,cycle203_3,cycle203_4,cycle203_5]⟩
lemma valid_data203 : data203.Valid src203 dst203 Finset.univ := by decide +kernel

def src204 : E → W := ![2,4,6,3,8,5,2,3,14,18,16,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst204 : E → W := ![4,6,3,8,5,2,3,14,18,16,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle204_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle204_1 : CycleData E W := ⟨2,![3,4,13,7],![3,8,5,14]⟩
def cycle204_2 : CycleData E W := ⟨2,![5,12,18,10],![2,5,26,16]⟩
def cycle204_3 : CycleData E W := ⟨3,![8,9,17,22,14],![14,18,16,38,28]⟩
def cycle204_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle204_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data204 : PartitionData E W := ⟨6,![cycle204_0,cycle204_1,cycle204_2,cycle204_3,cycle204_4,cycle204_5]⟩
lemma valid_data204 : data204.Valid src204 dst204 Finset.univ := by decide +kernel

def src205 : E → W := ![2,4,6,3,8,5,2,3,14,18,16,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst205 : E → W := ![4,6,3,8,5,2,3,14,18,16,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle205_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle205_1 : CycleData E W := ⟨2,![3,4,13,7],![3,8,5,14]⟩
def cycle205_2 : CycleData E W := ⟨2,![5,12,18,10],![2,5,26,16]⟩
def cycle205_3 : CycleData E W := ⟨4,![11,17,22,8,14,15],![4,26,38,18,14,28]⟩
def cycle205_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle205_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data205 : PartitionData E W := ⟨6,![cycle205_0,cycle205_1,cycle205_2,cycle205_3,cycle205_4,cycle205_5]⟩
lemma valid_data205 : data205.Valid src205 dst205 Finset.univ := by decide +kernel

def src206 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,38,18,28,39]
def dst206 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle206_0 : CycleData E W := ⟨4,![0,11,8,3,4,5],![2,4,14,3,8,5]⟩
def cycle206_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle206_2 : CycleData E W := ⟨1,![2,16,7],![3,6,16]⟩
def cycle206_3 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle206_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle206_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data206 : PartitionData E W := ⟨6,![cycle206_0,cycle206_1,cycle206_2,cycle206_3,cycle206_4,cycle206_5]⟩
lemma valid_data206 : data206.Valid src206 dst206 Finset.univ := by decide +kernel

def src207 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,38,28,18,39]
def dst207 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle207_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle207_1 : CycleData E W := ⟨3,![1,16,17,22,15],![4,6,16,38,28]⟩
def cycle207_2 : CycleData E W := ⟨2,![2,20,25,3],![3,6,39,8]⟩
def cycle207_3 : CycleData E W := ⟨2,![4,21,18,13],![5,8,38,26]⟩
def cycle207_4 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle207_5 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def data207 : PartitionData E W := ⟨6,![cycle207_0,cycle207_1,cycle207_2,cycle207_3,cycle207_4,cycle207_5]⟩
lemma valid_data207 : data207.Valid src207 dst207 Finset.univ := by decide +kernel

def src208 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,38,18,28,39]
def dst208 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle208_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle208_1 : CycleData E W := ⟨3,![1,16,17,24,15],![4,6,16,39,28]⟩
def cycle208_2 : CycleData E W := ⟨2,![2,20,21,3],![3,6,38,8]⟩
def cycle208_3 : CycleData E W := ⟨2,![4,25,18,13],![5,8,39,26]⟩
def cycle208_4 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle208_5 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def data208 : PartitionData E W := ⟨6,![cycle208_0,cycle208_1,cycle208_2,cycle208_3,cycle208_4,cycle208_5]⟩
lemma valid_data208 : data208.Valid src208 dst208 Finset.univ := by decide +kernel

def src209 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,38,28,18,39]
def dst209 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle209_0 : CycleData E W := ⟨4,![0,11,8,3,4,5],![2,4,14,3,8,5]⟩
def cycle209_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,38,28]⟩
def cycle209_2 : CycleData E W := ⟨1,![2,16,7],![3,6,16]⟩
def cycle209_3 : CycleData E W := ⟨2,![6,17,24,10],![2,16,39,18]⟩
def cycle209_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle209_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data209 : PartitionData E W := ⟨6,![cycle209_0,cycle209_1,cycle209_2,cycle209_3,cycle209_4,cycle209_5]⟩
lemma valid_data209 : data209.Valid src209 dst209 Finset.univ := by decide +kernel

def src210 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,38,28,39]
def dst210 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle210_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle210_1 : CycleData E W := ⟨2,![1,16,23,15],![4,6,38,28]⟩
def cycle210_2 : CycleData E W := ⟨2,![2,20,25,3],![3,6,39,8]⟩
def cycle210_3 : CycleData E W := ⟨2,![5,4,21,10],![2,5,8,18]⟩
def cycle210_4 : CycleData E W := ⟨3,![9,22,17,18,12],![14,18,38,16,26]⟩
def cycle210_5 : CycleData E W := ⟨2,![13,19,24,14],![5,26,39,28]⟩
def data210 : PartitionData E W := ⟨6,![cycle210_0,cycle210_1,cycle210_2,cycle210_3,cycle210_4,cycle210_5]⟩
lemma valid_data210 : data210.Valid src210 dst210 Finset.univ := by decide +kernel

def src211 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,39,28,38]
def dst211 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle211_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle211_1 : CycleData E W := ⟨2,![1,20,23,15],![4,6,39,28]⟩
def cycle211_2 : CycleData E W := ⟨2,![2,16,25,3],![3,6,38,8]⟩
def cycle211_3 : CycleData E W := ⟨2,![5,4,21,10],![2,5,8,18]⟩
def cycle211_4 : CycleData E W := ⟨2,![9,22,19,12],![14,18,39,26]⟩
def cycle211_5 : CycleData E W := ⟨3,![13,18,17,24,14],![5,26,16,38,28]⟩
def data211 : PartitionData E W := ⟨6,![cycle211_0,cycle211_1,cycle211_2,cycle211_3,cycle211_4,cycle211_5]⟩
lemma valid_data211 : data211.Valid src211 dst211 Finset.univ := by decide +kernel

def src212 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst212 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle212_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle212_1 : CycleData E W := ⟨2,![1,16,22,15],![4,6,38,28]⟩
def cycle212_2 : CycleData E W := ⟨2,![2,20,25,3],![3,6,39,8]⟩
def cycle212_3 : CycleData E W := ⟨3,![4,21,17,18,13],![5,8,38,16,26]⟩
def cycle212_4 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle212_5 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def data212 : PartitionData E W := ⟨6,![cycle212_0,cycle212_1,cycle212_2,cycle212_3,cycle212_4,cycle212_5]⟩
lemma valid_data212 : data212.Valid src212 dst212 Finset.univ := by decide +kernel

def src213 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,38,28,39]
def dst213 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle213_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle213_1 : CycleData E W := ⟨2,![1,16,23,15],![4,6,38,28]⟩
def cycle213_2 : CycleData E W := ⟨2,![2,20,25,3],![3,6,39,8]⟩
def cycle213_3 : CycleData E W := ⟨2,![5,4,21,10],![2,5,8,18]⟩
def cycle213_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle213_5 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def data213 : PartitionData E W := ⟨6,![cycle213_0,cycle213_1,cycle213_2,cycle213_3,cycle213_4,cycle213_5]⟩
lemma valid_data213 : data213.Valid src213 dst213 Finset.univ := by decide +kernel

def src214 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,39,28,38]
def dst214 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle214_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle214_1 : CycleData E W := ⟨2,![1,20,23,15],![4,6,39,28]⟩
def cycle214_2 : CycleData E W := ⟨2,![2,16,25,3],![3,6,38,8]⟩
def cycle214_3 : CycleData E W := ⟨2,![5,4,21,10],![2,5,8,18]⟩
def cycle214_4 : CycleData E W := ⟨3,![9,22,19,18,12],![14,18,39,16,26]⟩
def cycle214_5 : CycleData E W := ⟨2,![13,17,24,14],![5,26,38,28]⟩
def data214 : PartitionData E W := ⟨6,![cycle214_0,cycle214_1,cycle214_2,cycle214_3,cycle214_4,cycle214_5]⟩
lemma valid_data214 : data214.Valid src214 dst214 Finset.univ := by decide +kernel

def src215 : E → W := ![2,4,6,3,8,5,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst215 : E → W := ![4,6,3,8,5,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle215_0 : CycleData E W := ⟨3,![0,11,8,7,6],![2,4,14,3,16]⟩
def cycle215_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle215_2 : CycleData E W := ⟨2,![2,16,21,3],![3,6,38,8]⟩
def cycle215_3 : CycleData E W := ⟨3,![4,25,19,18,13],![5,8,39,16,26]⟩
def cycle215_4 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle215_5 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def data215 : PartitionData E W := ⟨6,![cycle215_0,cycle215_1,cycle215_2,cycle215_3,cycle215_4,cycle215_5]⟩
lemma valid_data215 : data215.Valid src215 dst215 Finset.univ := by decide +kernel

def src216 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,38,18,28,39]
def dst216 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle216_0 : CycleData E W := ⟨2,![0,11,12,5],![2,4,26,5]⟩
def cycle216_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle216_2 : CycleData E W := ⟨3,![2,20,24,23,9],![3,6,39,28,18]⟩
def cycle216_3 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle216_4 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle216_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data216 : PartitionData E W := ⟨6,![cycle216_0,cycle216_1,cycle216_2,cycle216_3,cycle216_4,cycle216_5]⟩
lemma valid_data216 : data216.Valid src216 dst216 Finset.univ := by decide +kernel

def src217 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,38,28,18,39]
def dst217 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle217_0 : CycleData E W := ⟨2,![0,11,12,5],![2,4,26,5]⟩
def cycle217_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle217_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle217_3 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle217_4 : CycleData E W := ⟨3,![6,17,22,23,10],![2,16,38,28,18]⟩
def cycle217_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data217 : PartitionData E W := ⟨6,![cycle217_0,cycle217_1,cycle217_2,cycle217_3,cycle217_4,cycle217_5]⟩
lemma valid_data217 : data217.Valid src217 dst217 Finset.univ := by decide +kernel

def src218 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,38,18,28,39]
def dst218 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle218_0 : CycleData E W := ⟨2,![0,11,12,5],![2,4,26,5]⟩
def cycle218_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle218_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle218_3 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle218_4 : CycleData E W := ⟨3,![6,17,24,23,10],![2,16,39,28,18]⟩
def cycle218_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data218 : PartitionData E W := ⟨6,![cycle218_0,cycle218_1,cycle218_2,cycle218_3,cycle218_4,cycle218_5]⟩
lemma valid_data218 : data218.Valid src218 dst218 Finset.univ := by decide +kernel

def src219 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,38,28,18,39]
def dst219 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle219_0 : CycleData E W := ⟨2,![0,11,12,5],![2,4,26,5]⟩
def cycle219_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle219_2 : CycleData E W := ⟨3,![2,20,22,23,9],![3,6,38,28,18]⟩
def cycle219_3 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle219_4 : CycleData E W := ⟨2,![6,17,24,10],![2,16,39,18]⟩
def cycle219_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data219 : PartitionData E W := ⟨6,![cycle219_0,cycle219_1,cycle219_2,cycle219_3,cycle219_4,cycle219_5]⟩
lemma valid_data219 : data219.Valid src219 dst219 Finset.univ := by decide +kernel

def src220 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,38,28,39]
def dst220 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle220_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle220_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle220_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle220_3 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def cycle220_4 : CycleData E W := ⟨2,![11,19,24,15],![4,26,39,28]⟩
def cycle220_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data220 : PartitionData E W := ⟨6,![cycle220_0,cycle220_1,cycle220_2,cycle220_3,cycle220_4,cycle220_5]⟩
lemma valid_data220 : data220.Valid src220 dst220 Finset.univ := by decide +kernel

def src221 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,28,38]
def dst221 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle221_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle221_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle221_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle221_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,38,28]⟩
def cycle221_4 : CycleData E W := ⟨2,![11,19,23,15],![4,26,39,28]⟩
def cycle221_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data221 : PartitionData E W := ⟨6,![cycle221_0,cycle221_1,cycle221_2,cycle221_3,cycle221_4,cycle221_5]⟩
lemma valid_data221 : data221.Valid src221 dst221 Finset.univ := by decide +kernel

def src222 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst222 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle222_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle222_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle222_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle222_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle222_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle222_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data222 : PartitionData E W := ⟨6,![cycle222_0,cycle222_1,cycle222_2,cycle222_3,cycle222_4,cycle222_5]⟩
lemma valid_data222 : data222.Valid src222 dst222 Finset.univ := by decide +kernel

def src223 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,28,39]
def dst223 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle223_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle223_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle223_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle223_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle223_4 : CycleData E W := ⟨2,![11,17,23,15],![4,26,38,28]⟩
def cycle223_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data223 : PartitionData E W := ⟨6,![cycle223_0,cycle223_1,cycle223_2,cycle223_3,cycle223_4,cycle223_5]⟩
lemma valid_data223 : data223.Valid src223 dst223 Finset.univ := by decide +kernel

def src224 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,39,28,38]
def dst224 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle224_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle224_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle224_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle224_3 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def cycle224_4 : CycleData E W := ⟨2,![11,17,24,15],![4,26,38,28]⟩
def cycle224_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data224 : PartitionData E W := ⟨6,![cycle224_0,cycle224_1,cycle224_2,cycle224_3,cycle224_4,cycle224_5]⟩
lemma valid_data224 : data224.Valid src224 dst224 Finset.univ := by decide +kernel

def src225 : E → W := ![2,4,6,3,8,5,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst225 : E → W := ![4,6,3,8,5,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle225_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle225_1 : CycleData E W := ⟨2,![3,4,13,8],![3,8,5,14]⟩
def cycle225_2 : CycleData E W := ⟨2,![5,12,18,6],![2,5,26,16]⟩
def cycle225_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle225_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle225_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data225 : PartitionData E W := ⟨6,![cycle225_0,cycle225_1,cycle225_2,cycle225_3,cycle225_4,cycle225_5]⟩
lemma valid_data225 : data225.Valid src225 dst225 Finset.univ := by decide +kernel

def src226 : E → W := ![2,4,6,8,3,5,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst226 : E → W := ![4,6,8,3,5,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle226_0 : CycleData E W := ⟨3,![0,11,8,4,5],![2,4,14,3,5]⟩
def cycle226_1 : CycleData E W := ⟨2,![1,16,22,15],![4,6,38,28]⟩
def cycle226_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle226_3 : CycleData E W := ⟨2,![3,21,17,7],![3,8,38,16]⟩
def cycle226_4 : CycleData E W := ⟨3,![6,18,12,9,10],![2,16,26,14,18]⟩
def cycle226_5 : CycleData E W := ⟨3,![13,19,24,23,14],![5,26,39,18,28]⟩
def data226 : PartitionData E W := ⟨6,![cycle226_0,cycle226_1,cycle226_2,cycle226_3,cycle226_4,cycle226_5]⟩
lemma valid_data226 : data226.Valid src226 dst226 Finset.univ := by decide +kernel

def src227 : E → W := ![2,4,6,8,3,5,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst227 : E → W := ![4,6,8,3,5,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle227_0 : CycleData E W := ⟨3,![0,11,8,4,5],![2,4,14,3,5]⟩
def cycle227_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle227_2 : CycleData E W := ⟨1,![2,21,16],![6,8,38]⟩
def cycle227_3 : CycleData E W := ⟨2,![3,25,19,7],![3,8,39,16]⟩
def cycle227_4 : CycleData E W := ⟨3,![6,18,12,9,10],![2,16,26,14,18]⟩
def cycle227_5 : CycleData E W := ⟨3,![13,17,22,23,14],![5,26,38,18,28]⟩
def data227 : PartitionData E W := ⟨6,![cycle227_0,cycle227_1,cycle227_2,cycle227_3,cycle227_4,cycle227_5]⟩
lemma valid_data227 : data227.Valid src227 dst227 Finset.univ := by decide +kernel

def src228 : E → W := ![2,4,6,8,3,5,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst228 : E → W := ![4,6,8,3,5,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle228_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle228_1 : CycleData E W := ⟨3,![1,16,17,18,15],![4,6,38,16,26]⟩
def cycle228_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle228_3 : CycleData E W := ⟨3,![3,21,22,12,8],![3,8,38,28,14]⟩
def cycle228_4 : CycleData E W := ⟨2,![5,4,9,10],![2,5,3,18]⟩
def cycle228_5 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def data228 : PartitionData E W := ⟨6,![cycle228_0,cycle228_1,cycle228_2,cycle228_3,cycle228_4,cycle228_5]⟩
lemma valid_data228 : data228.Valid src228 dst228 Finset.univ := by decide +kernel

def src229 : E → W := ![2,4,6,8,3,5,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst229 : E → W := ![4,6,8,3,5,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle229_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle229_1 : CycleData E W := ⟨2,![1,16,17,15],![4,6,38,26]⟩
def cycle229_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle229_3 : CycleData E W := ⟨2,![3,21,22,9],![3,8,38,18]⟩
def cycle229_4 : CycleData E W := ⟨2,![4,13,12,8],![3,5,28,14]⟩
def cycle229_5 : CycleData E W := ⟨5,![5,14,18,19,24,23,10],![2,5,26,16,39,28,18]⟩
def data229 : PartitionData E W := ⟨6,![cycle229_0,cycle229_1,cycle229_2,cycle229_3,cycle229_4,cycle229_5]⟩
lemma valid_data229 : data229.Valid src229 dst229 Finset.univ := by decide +kernel

def src230 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst230 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle230_0 : CycleData E W := ⟨2,![0,11,3,6],![2,4,5,3]⟩
def cycle230_1 : CycleData E W := ⟨2,![1,25,19,15],![4,8,39,26]⟩
def cycle230_2 : CycleData E W := ⟨2,![2,21,17,7],![3,8,38,16]⟩
def cycle230_3 : CycleData E W := ⟨2,![4,16,22,12],![5,6,38,28]⟩
def cycle230_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle230_5 : CycleData E W := ⟨1,![8,18,14],![14,16,26]⟩
def cycle230_6 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def data230 : PartitionData E W := ⟨7,![cycle230_0,cycle230_1,cycle230_2,cycle230_3,cycle230_4,cycle230_5,cycle230_6]⟩
lemma valid_data230 : data230.Valid src230 dst230 Finset.univ := by decide +kernel

def src231 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst231 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle231_0 : CycleData E W := ⟨2,![0,11,3,6],![2,4,5,3]⟩
def cycle231_1 : CycleData E W := ⟨2,![1,21,17,15],![4,8,38,26]⟩
def cycle231_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle231_3 : CycleData E W := ⟨2,![4,20,24,12],![5,6,39,28]⟩
def cycle231_4 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle231_5 : CycleData E W := ⟨1,![8,18,14],![14,16,26]⟩
def cycle231_6 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def data231 : PartitionData E W := ⟨7,![cycle231_0,cycle231_1,cycle231_2,cycle231_3,cycle231_4,cycle231_5,cycle231_6]⟩
lemma valid_data231 : data231.Valid src231 dst231 Finset.univ := by decide +kernel

def src232 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,5,26,28,6,38,16,26,39,8,38,28,18,39]
def dst232 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,5,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle232_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle232_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,16]⟩
def cycle232_2 : CycleData E W := ⟨3,![4,16,17,18,13],![5,6,38,16,26]⟩
def cycle232_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle232_4 : CycleData E W := ⟨2,![11,9,23,15],![4,14,18,28]⟩
def cycle232_5 : CycleData E W := ⟨3,![21,22,14,19,25],![8,38,28,26,39]⟩
def data232 : PartitionData E W := ⟨6,![cycle232_0,cycle232_1,cycle232_2,cycle232_3,cycle232_4,cycle232_5]⟩
lemma valid_data232 : data232.Valid src232 dst232 Finset.univ := by decide +kernel

def src233 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,5,26,28,6,38,26,16,39,8,38,18,28,39]
def dst233 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,5,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle233_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle233_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,16]⟩
def cycle233_2 : CycleData E W := ⟨2,![4,16,17,13],![5,6,38,26]⟩
def cycle233_3 : CycleData E W := ⟨4,![5,20,25,21,22,10],![2,6,39,8,38,18]⟩
def cycle233_4 : CycleData E W := ⟨2,![11,9,23,15],![4,14,18,28]⟩
def cycle233_5 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def data233 : PartitionData E W := ⟨6,![cycle233_0,cycle233_1,cycle233_2,cycle233_3,cycle233_4,cycle233_5]⟩
lemma valid_data233 : data233.Valid src233 dst233 Finset.univ := by decide +kernel

def src234 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,5,28,26,6,38,16,26,39,8,38,28,18,39]
def dst234 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,5,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle234_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle234_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,16]⟩
def cycle234_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle234_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle234_4 : CycleData E W := ⟨3,![11,9,23,14,15],![4,14,18,28,26]⟩
def cycle234_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data234 : PartitionData E W := ⟨6,![cycle234_0,cycle234_1,cycle234_2,cycle234_3,cycle234_4,cycle234_5]⟩
lemma valid_data234 : data234.Valid src234 dst234 Finset.univ := by decide +kernel

def src235 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,5,28,26,6,38,26,16,39,8,38,18,28,39]
def dst235 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,5,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle235_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle235_1 : CycleData E W := ⟨2,![3,12,8,7],![3,5,14,16]⟩
def cycle235_2 : CycleData E W := ⟨3,![5,4,13,23,10],![2,6,5,28,18]⟩
def cycle235_3 : CycleData E W := ⟨3,![11,9,22,17,15],![4,14,18,38,26]⟩
def cycle235_4 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def cycle235_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data235 : PartitionData E W := ⟨6,![cycle235_0,cycle235_1,cycle235_2,cycle235_3,cycle235_4,cycle235_5]⟩
lemma valid_data235 : data235.Valid src235 dst235 Finset.univ := by decide +kernel

def src236 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst236 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle236_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle236_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,28,14,16]⟩
def cycle236_2 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle236_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle236_4 : CycleData E W := ⟨3,![11,9,22,17,15],![4,14,18,38,26]⟩
def cycle236_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data236 : PartitionData E W := ⟨6,![cycle236_0,cycle236_1,cycle236_2,cycle236_3,cycle236_4,cycle236_5]⟩
lemma valid_data236 : data236.Valid src236 dst236 Finset.univ := by decide +kernel

def src237 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst237 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle237_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle237_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,28,14,16]⟩
def cycle237_2 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle237_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle237_4 : CycleData E W := ⟨4,![11,9,23,22,17,15],![4,14,18,28,38,26]⟩
def cycle237_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data237 : PartitionData E W := ⟨6,![cycle237_0,cycle237_1,cycle237_2,cycle237_3,cycle237_4,cycle237_5]⟩
lemma valid_data237 : data237.Valid src237 dst237 Finset.univ := by decide +kernel

def src238 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst238 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle238_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle238_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,28,14,16]⟩
def cycle238_2 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle238_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle238_4 : CycleData E W := ⟨4,![11,9,23,24,17,15],![4,14,18,28,39,26]⟩
def cycle238_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data238 : PartitionData E W := ⟨6,![cycle238_0,cycle238_1,cycle238_2,cycle238_3,cycle238_4,cycle238_5]⟩
lemma valid_data238 : data238.Valid src238 dst238 Finset.univ := by decide +kernel

def src239 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst239 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle239_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle239_1 : CycleData E W := ⟨3,![3,13,12,8,7],![3,5,28,14,16]⟩
def cycle239_2 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle239_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle239_4 : CycleData E W := ⟨3,![11,9,24,17,15],![4,14,18,39,26]⟩
def cycle239_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data239 : PartitionData E W := ⟨6,![cycle239_0,cycle239_1,cycle239_2,cycle239_3,cycle239_4,cycle239_5]⟩
lemma valid_data239 : data239.Valid src239 dst239 Finset.univ := by decide +kernel

def src240 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst240 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle240_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle240_1 : CycleData E W := ⟨3,![3,4,16,17,7],![3,5,6,38,16]⟩
def cycle240_2 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle240_3 : CycleData E W := ⟨2,![11,8,18,15],![4,14,16,26]⟩
def cycle240_4 : CycleData E W := ⟨2,![9,23,22,12],![14,18,38,28]⟩
def cycle240_5 : CycleData E W := ⟨3,![13,21,25,19,14],![5,28,8,39,26]⟩
def data240 : PartitionData E W := ⟨6,![cycle240_0,cycle240_1,cycle240_2,cycle240_3,cycle240_4,cycle240_5]⟩
lemma valid_data240 : data240.Valid src240 dst240 Finset.univ := by decide +kernel

def src241 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst241 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle241_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle241_1 : CycleData E W := ⟨3,![3,4,16,17,7],![3,5,6,38,16]⟩
def cycle241_2 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle241_3 : CycleData E W := ⟨2,![11,8,18,15],![4,14,16,26]⟩
def cycle241_4 : CycleData E W := ⟨3,![21,12,9,24,25],![8,28,14,18,38]⟩
def cycle241_5 : CycleData E W := ⟨2,![13,22,19,14],![5,28,39,26]⟩
def data241 : PartitionData E W := ⟨6,![cycle241_0,cycle241_1,cycle241_2,cycle241_3,cycle241_4,cycle241_5]⟩
lemma valid_data241 : data241.Valid src241 dst241 Finset.univ := by decide +kernel

def src242 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst242 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle242_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle242_1 : CycleData E W := ⟨4,![3,14,15,11,8,7],![3,5,26,4,14,16]⟩
def cycle242_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle242_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle242_4 : CycleData E W := ⟨1,![9,23,12],![14,18,28]⟩
def cycle242_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data242 : PartitionData E W := ⟨6,![cycle242_0,cycle242_1,cycle242_2,cycle242_3,cycle242_4,cycle242_5]⟩
lemma valid_data242 : data242.Valid src242 dst242 Finset.univ := by decide +kernel

def src243 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst243 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle243_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle243_1 : CycleData E W := ⟨2,![3,14,18,7],![3,5,26,16]⟩
def cycle243_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle243_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle243_4 : CycleData E W := ⟨3,![21,12,8,19,25],![8,28,14,16,39]⟩
def cycle243_5 : CycleData E W := ⟨3,![11,9,23,17,15],![4,14,18,38,26]⟩
def data243 : PartitionData E W := ⟨6,![cycle243_0,cycle243_1,cycle243_2,cycle243_3,cycle243_4,cycle243_5]⟩
lemma valid_data243 : data243.Valid src243 dst243 Finset.univ := by decide +kernel

def src244 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst244 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle244_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle244_1 : CycleData E W := ⟨2,![3,14,18,7],![3,5,26,16]⟩
def cycle244_2 : CycleData E W := ⟨2,![4,20,22,13],![5,6,39,28]⟩
def cycle244_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle244_4 : CycleData E W := ⟨2,![8,19,23,9],![14,16,39,18]⟩
def cycle244_5 : CycleData E W := ⟨4,![11,12,21,25,17,15],![4,14,28,8,38,26]⟩
def data244 : PartitionData E W := ⟨6,![cycle244_0,cycle244_1,cycle244_2,cycle244_3,cycle244_4,cycle244_5]⟩
lemma valid_data244 : data244.Valid src244 dst244 Finset.univ := by decide +kernel

def src245 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst245 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle245_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle245_1 : CycleData E W := ⟨4,![3,14,15,11,8,7],![3,5,26,4,14,16]⟩
def cycle245_2 : CycleData E W := ⟨2,![4,20,24,13],![5,6,39,28]⟩
def cycle245_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle245_4 : CycleData E W := ⟨1,![9,23,12],![14,18,28]⟩
def cycle245_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data245 : PartitionData E W := ⟨6,![cycle245_0,cycle245_1,cycle245_2,cycle245_3,cycle245_4,cycle245_5]⟩
lemma valid_data245 : data245.Valid src245 dst245 Finset.univ := by decide +kernel

def src246 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst246 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle246_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle246_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle246_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle246_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle246_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle246_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data246 : PartitionData E W := ⟨6,![cycle246_0,cycle246_1,cycle246_2,cycle246_3,cycle246_4,cycle246_5]⟩
lemma valid_data246 : data246.Valid src246 dst246 Finset.univ := by decide +kernel

def src247 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst247 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle247_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle247_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle247_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle247_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle247_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle247_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data247 : PartitionData E W := ⟨6,![cycle247_0,cycle247_1,cycle247_2,cycle247_3,cycle247_4,cycle247_5]⟩
lemma valid_data247 : data247.Valid src247 dst247 Finset.univ := by decide +kernel

def src248 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst248 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle248_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle248_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle248_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle248_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle248_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle248_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data248 : PartitionData E W := ⟨6,![cycle248_0,cycle248_1,cycle248_2,cycle248_3,cycle248_4,cycle248_5]⟩
lemma valid_data248 : data248.Valid src248 dst248 Finset.univ := by decide +kernel

def src249 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst249 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle249_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle249_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle249_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle249_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle249_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle249_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data249 : PartitionData E W := ⟨6,![cycle249_0,cycle249_1,cycle249_2,cycle249_3,cycle249_4,cycle249_5]⟩
lemma valid_data249 : data249.Valid src249 dst249 Finset.univ := by decide +kernel

def lookupB4 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data200 else (if j < 2 then data201 else data202)) else (if j < 4 then data203 else (if j < 5 then data204 else data205))) else (if j < 9 then (if j < 7 then data206 else (if j < 8 then data207 else data208)) else (if j < 10 then data209 else (if j < 11 then data210 else data211)))) else (if j < 18 then (if j < 15 then (if j < 13 then data212 else (if j < 14 then data213 else data214)) else (if j < 16 then data215 else (if j < 17 then data216 else data217))) else (if j < 21 then (if j < 19 then data218 else (if j < 20 then data219 else data220)) else (if j < 23 then (if j < 22 then data221 else data222) else (if j < 24 then data223 else data224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data225 else (if j < 27 then data226 else data227)) else (if j < 29 then data228 else (if j < 30 then data229 else data230))) else (if j < 34 then (if j < 32 then data231 else (if j < 33 then data232 else data233)) else (if j < 35 then data234 else (if j < 36 then data235 else data236)))) else (if j < 43 then (if j < 40 then (if j < 38 then data237 else (if j < 39 then data238 else data239)) else (if j < 41 then data240 else (if j < 42 then data241 else data242))) else (if j < 46 then (if j < 44 then data243 else (if j < 45 then data244 else data245)) else (if j < 48 then (if j < 47 then data246 else data247) else (if j < 49 then data248 else data249))))))

def srcTableB4 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src200 else (if j < 2 then src201 else src202)) else (if j < 4 then src203 else (if j < 5 then src204 else src205))) else (if j < 9 then (if j < 7 then src206 else (if j < 8 then src207 else src208)) else (if j < 10 then src209 else (if j < 11 then src210 else src211)))) else (if j < 18 then (if j < 15 then (if j < 13 then src212 else (if j < 14 then src213 else src214)) else (if j < 16 then src215 else (if j < 17 then src216 else src217))) else (if j < 21 then (if j < 19 then src218 else (if j < 20 then src219 else src220)) else (if j < 23 then (if j < 22 then src221 else src222) else (if j < 24 then src223 else src224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src225 else (if j < 27 then src226 else src227)) else (if j < 29 then src228 else (if j < 30 then src229 else src230))) else (if j < 34 then (if j < 32 then src231 else (if j < 33 then src232 else src233)) else (if j < 35 then src234 else (if j < 36 then src235 else src236)))) else (if j < 43 then (if j < 40 then (if j < 38 then src237 else (if j < 39 then src238 else src239)) else (if j < 41 then src240 else (if j < 42 then src241 else src242))) else (if j < 46 then (if j < 44 then src243 else (if j < 45 then src244 else src245)) else (if j < 48 then (if j < 47 then src246 else src247) else (if j < 49 then src248 else src249))))))

def dstTableB4 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst200 else (if j < 2 then dst201 else dst202)) else (if j < 4 then dst203 else (if j < 5 then dst204 else dst205))) else (if j < 9 then (if j < 7 then dst206 else (if j < 8 then dst207 else dst208)) else (if j < 10 then dst209 else (if j < 11 then dst210 else dst211)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst212 else (if j < 14 then dst213 else dst214)) else (if j < 16 then dst215 else (if j < 17 then dst216 else dst217))) else (if j < 21 then (if j < 19 then dst218 else (if j < 20 then dst219 else dst220)) else (if j < 23 then (if j < 22 then dst221 else dst222) else (if j < 24 then dst223 else dst224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst225 else (if j < 27 then dst226 else dst227)) else (if j < 29 then dst228 else (if j < 30 then dst229 else dst230))) else (if j < 34 then (if j < 32 then dst231 else (if j < 33 then dst232 else dst233)) else (if j < 35 then dst234 else (if j < 36 then dst235 else dst236)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst237 else (if j < 39 then dst238 else dst239)) else (if j < 41 then dst240 else (if j < 42 then dst241 else dst242))) else (if j < 46 then (if j < 44 then dst243 else (if j < 45 then dst244 else dst245)) else (if j < 48 then (if j < 47 then dst246 else dst247) else (if j < 49 then dst248 else dst249))))))

def caseB4 (i : Fin 50) : Cases := ⟨200 + i.val,by have := i.isLt; omega⟩
lemma tableB4_valid (i : Fin 50) :
    (lookupB4 i.val).Valid (srcTableB4 i.val) (dstTableB4 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB4_row : ∀ (i : Fin 50) (e : E),
    srcTableB4 i.val e = caseSource (caseB4 i) e := by decide +kernel

lemma dstB4_row : ∀ (i : Fin 50) (e : E),
    dstTableB4 i.val e = caseTarget (caseB4 i) e := by decide +kernel

lemma sizeB4 : ∀ i : Fin 50, (lookupB4 i.val).size ≤ 5 →
    (lookupB4 i.val).size = 2 ∧
      (⟨caseKey (caseB4 i),caseKey_lt (caseB4 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB4 (i : Fin 50) : Certificate (caseB4 i) := by
  refine ⟨lookupB4 i.val,?_,sizeB4 i⟩
  have hv := tableB4_valid i
  rw [funext (srcB4_row i),funext (dstB4_row i)] at hv
  exact hv
lemma certificateInterval4 : FiniteIntervals.Covers CertificateAt 200 250 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 200 50 (fun i _ => certificateB4 i)
#print axioms certificateInterval4
end Erdos184Work.FiveRows4

import Submission.FiveCertificates1Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src200 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst200 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle200_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle200_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle200_2 : CycleData E W := ⟨2,![2,18,11,10],![4,8,28,14]⟩
def cycle200_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle200_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle200_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data200 : PartitionData E W := ⟨6,![cycle200_0,cycle200_1,cycle200_2,cycle200_3,cycle200_4,cycle200_5]⟩
lemma valid_data200 : data200.Valid src200 dst200 Finset.univ := by decide +kernel

def src201 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst201 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle201_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle201_1 : CycleData E W := ⟨2,![1,2,18,7],![3,4,8,18]⟩
def cycle201_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle201_3 : CycleData E W := ⟨3,![4,17,13,10,5],![2,6,26,4,14]⟩
def cycle201_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle201_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data201 : PartitionData E W := ⟨6,![cycle201_0,cycle201_1,cycle201_2,cycle201_3,cycle201_4,cycle201_5]⟩
lemma valid_data201 : data201.Valid src201 dst201 Finset.univ := by decide +kernel

def src202 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst202 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle202_0 : CycleData E W := ⟨2,![0,1,10,5],![2,3,4,14]⟩
def cycle202_1 : CycleData E W := ⟨2,![2,3,17,13],![4,8,6,26]⟩
def cycle202_2 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle202_3 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle202_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle202_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data202 : PartitionData E W := ⟨6,![cycle202_0,cycle202_1,cycle202_2,cycle202_3,cycle202_4,cycle202_5]⟩
lemma valid_data202 : data202.Valid src202 dst202 Finset.univ := by decide +kernel

def src203 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst203 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle203_0 : CycleData E W := ⟨2,![0,1,10,5],![2,3,4,14]⟩
def cycle203_1 : CycleData E W := ⟨2,![2,3,17,13],![4,8,6,26]⟩
def cycle203_2 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle203_3 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle203_4 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def cycle203_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data203 : PartitionData E W := ⟨6,![cycle203_0,cycle203_1,cycle203_2,cycle203_3,cycle203_4,cycle203_5]⟩
lemma valid_data203 : data203.Valid src203 dst203 Finset.univ := by decide +kernel

def src204 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst204 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle204_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle204_1 : CycleData E W := ⟨2,![1,2,18,7],![3,4,8,18]⟩
def cycle204_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle204_3 : CycleData E W := ⟨3,![4,14,13,10,5],![2,6,26,4,14]⟩
def cycle204_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle204_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data204 : PartitionData E W := ⟨6,![cycle204_0,cycle204_1,cycle204_2,cycle204_3,cycle204_4,cycle204_5]⟩
lemma valid_data204 : data204.Valid src204 dst204 Finset.univ := by decide +kernel

def src205 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst205 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle205_0 : CycleData E W := ⟨9,![4,17,16,8,7,18,2,13,12,11,5],![2,6,38,16,3,18,8,4,26,28,14]⟩
def cycle205_1 : CycleData E W := ⟨9,![0,1,10,6,19,20,21,3,14,15,9],![2,3,4,14,18,38,28,8,6,26,16]⟩
def data205 : PartitionData E W := ⟨2,![cycle205_0,cycle205_1]⟩
lemma valid_data205 : data205.Valid src205 dst205 Finset.univ := by decide +kernel

def src206 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst206 : E → W := ![3,4,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle206_0 : CycleData E W := ⟨2,![0,1,10,5],![2,3,4,14]⟩
def cycle206_1 : CycleData E W := ⟨2,![2,18,12,13],![4,8,28,26]⟩
def cycle206_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle206_3 : CycleData E W := ⟨2,![4,14,15,9],![2,6,26,16]⟩
def cycle206_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle206_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data206 : PartitionData E W := ⟨6,![cycle206_0,cycle206_1,cycle206_2,cycle206_3,cycle206_4,cycle206_5]⟩
lemma valid_data206 : data206.Valid src206 dst206 Finset.univ := by decide +kernel

def src207 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst207 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle207_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle207_1 : CycleData E W := ⟨2,![1,10,15,8],![3,4,26,16]⟩
def cycle207_2 : CycleData E W := ⟨2,![2,18,19,13],![4,8,18,28]⟩
def cycle207_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle207_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle207_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data207 : PartitionData E W := ⟨6,![cycle207_0,cycle207_1,cycle207_2,cycle207_3,cycle207_4,cycle207_5]⟩
lemma valid_data207 : data207.Valid src207 dst207 Finset.univ := by decide +kernel

def src208 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst208 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle208_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle208_1 : CycleData E W := ⟨2,![1,10,15,8],![3,4,26,16]⟩
def cycle208_2 : CycleData E W := ⟨1,![2,21,13],![4,8,28]⟩
def cycle208_3 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle208_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle208_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data208 : PartitionData E W := ⟨6,![cycle208_0,cycle208_1,cycle208_2,cycle208_3,cycle208_4,cycle208_5]⟩
lemma valid_data208 : data208.Valid src208 dst208 Finset.univ := by decide +kernel

def src209 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst209 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle209_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle209_1 : CycleData E W := ⟨2,![1,10,15,8],![3,4,26,16]⟩
def cycle209_2 : CycleData E W := ⟨1,![2,18,13],![4,8,28]⟩
def cycle209_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle209_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle209_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data209 : PartitionData E W := ⟨6,![cycle209_0,cycle209_1,cycle209_2,cycle209_3,cycle209_4,cycle209_5]⟩
lemma valid_data209 : data209.Valid src209 dst209 Finset.univ := by decide +kernel

def src210 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst210 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle210_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle210_1 : CycleData E W := ⟨2,![1,2,18,7],![3,4,8,18]⟩
def cycle210_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle210_3 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle210_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle210_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data210 : PartitionData E W := ⟨6,![cycle210_0,cycle210_1,cycle210_2,cycle210_3,cycle210_4,cycle210_5]⟩
lemma valid_data210 : data210.Valid src210 dst210 Finset.univ := by decide +kernel

def src211 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst211 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle211_0 : CycleData E W := ⟨9,![4,3,18,7,8,15,16,10,13,12,5],![2,6,8,18,3,16,38,26,4,28,14]⟩
def cycle211_1 : CycleData E W := ⟨9,![0,1,2,21,20,19,6,11,17,14,9],![2,3,4,8,28,38,18,14,26,6,16]⟩
def data211 : PartitionData E W := ⟨2,![cycle211_0,cycle211_1]⟩
lemma valid_data211 : data211.Valid src211 dst211 Finset.univ := by decide +kernel

def src212 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst212 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle212_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle212_1 : CycleData E W := ⟨3,![1,10,16,20,7],![3,4,26,38,18]⟩
def cycle212_2 : CycleData E W := ⟨1,![2,18,13],![4,8,28]⟩
def cycle212_3 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle212_4 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle212_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data212 : PartitionData E W := ⟨6,![cycle212_0,cycle212_1,cycle212_2,cycle212_3,cycle212_4,cycle212_5]⟩
lemma valid_data212 : data212.Valid src212 dst212 Finset.univ := by decide +kernel

def src213 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst213 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle213_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle213_1 : CycleData E W := ⟨2,![1,2,18,7],![3,4,8,18]⟩
def cycle213_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle213_3 : CycleData E W := ⟨2,![4,14,11,5],![2,6,26,14]⟩
def cycle213_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle213_5 : CycleData E W := ⟨3,![10,15,16,20,13],![4,26,16,38,28]⟩
def data213 : PartitionData E W := ⟨6,![cycle213_0,cycle213_1,cycle213_2,cycle213_3,cycle213_4,cycle213_5]⟩
lemma valid_data213 : data213.Valid src213 dst213 Finset.univ := by decide +kernel

def src214 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst214 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle214_0 : CycleData E W := ⟨9,![0,7,18,3,17,16,15,10,13,12,5],![2,3,18,8,6,38,16,26,4,28,14]⟩
def cycle214_1 : CycleData E W := ⟨9,![4,14,11,6,19,20,21,2,1,8,9],![2,6,26,14,18,38,28,8,4,3,16]⟩
def data214 : PartitionData E W := ⟨2,![cycle214_0,cycle214_1]⟩
lemma valid_data214 : data214.Valid src214 dst214 Finset.univ := by decide +kernel

def src215 : E → W := ![2,3,4,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst215 : E → W := ![3,4,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle215_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle215_1 : CycleData E W := ⟨4,![1,10,15,16,20,7],![3,4,26,16,38,18]⟩
def cycle215_2 : CycleData E W := ⟨1,![2,18,13],![4,8,28]⟩
def cycle215_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle215_4 : CycleData E W := ⟨2,![4,14,11,5],![2,6,26,14]⟩
def cycle215_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data215 : PartitionData E W := ⟨6,![cycle215_0,cycle215_1,cycle215_2,cycle215_3,cycle215_4,cycle215_5]⟩
lemma valid_data215 : data215.Valid src215 dst215 Finset.univ := by decide +kernel

def src216 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst216 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle216_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle216_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle216_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle216_3 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle216_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle216_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data216 : PartitionData E W := ⟨6,![cycle216_0,cycle216_1,cycle216_2,cycle216_3,cycle216_4,cycle216_5]⟩
lemma valid_data216 : data216.Valid src216 dst216 Finset.univ := by decide +kernel

def src217 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst217 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle217_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle217_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle217_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle217_3 : CycleData E W := ⟨4,![4,18,19,17,14,9],![2,8,18,38,6,16]⟩
def cycle217_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle217_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data217 : PartitionData E W := ⟨6,![cycle217_0,cycle217_1,cycle217_2,cycle217_3,cycle217_4,cycle217_5]⟩
lemma valid_data217 : data217.Valid src217 dst217 Finset.univ := by decide +kernel

def src218 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst218 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle218_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle218_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle218_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle218_3 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle218_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle218_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data218 : PartitionData E W := ⟨6,![cycle218_0,cycle218_1,cycle218_2,cycle218_3,cycle218_4,cycle218_5]⟩
lemma valid_data218 : data218.Valid src218 dst218 Finset.univ := by decide +kernel

def src219 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst219 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle219_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle219_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle219_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle219_3 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle219_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle219_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data219 : PartitionData E W := ⟨6,![cycle219_0,cycle219_1,cycle219_2,cycle219_3,cycle219_4,cycle219_5]⟩
lemma valid_data219 : data219.Valid src219 dst219 Finset.univ := by decide +kernel

def src220 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst220 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle220_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle220_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle220_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle220_3 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle220_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle220_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data220 : PartitionData E W := ⟨6,![cycle220_0,cycle220_1,cycle220_2,cycle220_3,cycle220_4,cycle220_5]⟩
lemma valid_data220 : data220.Valid src220 dst220 Finset.univ := by decide +kernel

def src221 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst221 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle221_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle221_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle221_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle221_3 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle221_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle221_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data221 : PartitionData E W := ⟨6,![cycle221_0,cycle221_1,cycle221_2,cycle221_3,cycle221_4,cycle221_5]⟩
lemma valid_data221 : data221.Valid src221 dst221 Finset.univ := by decide +kernel

def src222 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst222 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle222_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle222_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle222_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle222_3 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle222_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle222_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data222 : PartitionData E W := ⟨6,![cycle222_0,cycle222_1,cycle222_2,cycle222_3,cycle222_4,cycle222_5]⟩
lemma valid_data222 : data222.Valid src222 dst222 Finset.univ := by decide +kernel

def src223 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst223 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle223_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle223_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle223_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle223_3 : CycleData E W := ⟨3,![4,18,19,16,9],![2,8,18,38,16]⟩
def cycle223_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle223_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data223 : PartitionData E W := ⟨6,![cycle223_0,cycle223_1,cycle223_2,cycle223_3,cycle223_4,cycle223_5]⟩
lemma valid_data223 : data223.Valid src223 dst223 Finset.univ := by decide +kernel

def src224 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst224 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle224_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle224_1 : CycleData E W := ⟨3,![1,2,10,7,6],![3,6,4,14,18]⟩
def cycle224_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle224_3 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle224_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle224_5 : CycleData E W := ⟨3,![14,12,19,20,17],![6,26,28,18,38]⟩
def data224 : PartitionData E W := ⟨6,![cycle224_0,cycle224_1,cycle224_2,cycle224_3,cycle224_4,cycle224_5]⟩
lemma valid_data224 : data224.Valid src224 dst224 Finset.univ := by decide +kernel

def src225 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst225 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle225_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle225_1 : CycleData E W := ⟨3,![1,2,3,18,6],![3,6,4,8,18]⟩
def cycle225_2 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle225_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle225_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle225_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data225 : PartitionData E W := ⟨6,![cycle225_0,cycle225_1,cycle225_2,cycle225_3,cycle225_4,cycle225_5]⟩
lemma valid_data225 : data225.Valid src225 dst225 Finset.univ := by decide +kernel

def src226 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst226 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle226_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle226_1 : CycleData E W := ⟨2,![1,17,19,6],![3,6,38,18]⟩
def cycle226_2 : CycleData E W := ⟨3,![4,3,2,14,9],![2,8,4,6,16]⟩
def cycle226_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle226_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle226_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data226 : PartitionData E W := ⟨6,![cycle226_0,cycle226_1,cycle226_2,cycle226_3,cycle226_4,cycle226_5]⟩
lemma valid_data226 : data226.Valid src226 dst226 Finset.univ := by decide +kernel

def src227 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst227 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle227_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle227_1 : CycleData E W := ⟨2,![1,17,20,6],![3,6,38,18]⟩
def cycle227_2 : CycleData E W := ⟨3,![4,3,2,14,9],![2,8,4,6,16]⟩
def cycle227_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle227_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle227_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data227 : PartitionData E W := ⟨6,![cycle227_0,cycle227_1,cycle227_2,cycle227_3,cycle227_4,cycle227_5]⟩
lemma valid_data227 : data227.Valid src227 dst227 Finset.univ := by decide +kernel

def src228 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst228 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle228_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle228_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle228_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle228_3 : CycleData E W := ⟨3,![3,18,19,11,10],![4,8,18,28,14]⟩
def cycle228_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle228_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data228 : PartitionData E W := ⟨6,![cycle228_0,cycle228_1,cycle228_2,cycle228_3,cycle228_4,cycle228_5]⟩
lemma valid_data228 : data228.Valid src228 dst228 Finset.univ := by decide +kernel

def src229 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst229 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle229_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle229_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle229_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle229_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle229_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle229_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data229 : PartitionData E W := ⟨6,![cycle229_0,cycle229_1,cycle229_2,cycle229_3,cycle229_4,cycle229_5]⟩
lemma valid_data229 : data229.Valid src229 dst229 Finset.univ := by decide +kernel

def src230 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst230 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle230_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle230_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle230_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle230_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle230_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle230_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data230 : PartitionData E W := ⟨6,![cycle230_0,cycle230_1,cycle230_2,cycle230_3,cycle230_4,cycle230_5]⟩
lemma valid_data230 : data230.Valid src230 dst230 Finset.univ := by decide +kernel

def src231 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst231 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle231_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle231_1 : CycleData E W := ⟨3,![1,2,3,18,6],![3,6,4,8,18]⟩
def cycle231_2 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle231_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle231_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle231_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data231 : PartitionData E W := ⟨6,![cycle231_0,cycle231_1,cycle231_2,cycle231_3,cycle231_4,cycle231_5]⟩
lemma valid_data231 : data231.Valid src231 dst231 Finset.univ := by decide +kernel

def src232 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst232 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle232_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle232_1 : CycleData E W := ⟨2,![1,17,19,6],![3,6,38,18]⟩
def cycle232_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle232_3 : CycleData E W := ⟨3,![4,3,10,8,9],![2,8,4,14,16]⟩
def cycle232_4 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle232_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data232 : PartitionData E W := ⟨6,![cycle232_0,cycle232_1,cycle232_2,cycle232_3,cycle232_4,cycle232_5]⟩
lemma valid_data232 : data232.Valid src232 dst232 Finset.univ := by decide +kernel

def src233 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst233 : E → W := ![3,6,4,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle233_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle233_1 : CycleData E W := ⟨2,![1,17,20,6],![3,6,38,18]⟩
def cycle233_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle233_3 : CycleData E W := ⟨3,![4,3,10,8,9],![2,8,4,14,16]⟩
def cycle233_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle233_5 : CycleData E W := ⟨3,![18,12,15,16,21],![8,28,26,16,38]⟩
def data233 : PartitionData E W := ⟨6,![cycle233_0,cycle233_1,cycle233_2,cycle233_3,cycle233_4,cycle233_5]⟩
lemma valid_data233 : data233.Valid src233 dst233 Finset.univ := by decide +kernel

def src234 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst234 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle234_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle234_1 : CycleData E W := ⟨3,![1,2,3,18,6],![3,6,4,8,18]⟩
def cycle234_2 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle234_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle234_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle234_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data234 : PartitionData E W := ⟨6,![cycle234_0,cycle234_1,cycle234_2,cycle234_3,cycle234_4,cycle234_5]⟩
lemma valid_data234 : data234.Valid src234 dst234 Finset.univ := by decide +kernel

def src235 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst235 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle235_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle235_1 : CycleData E W := ⟨4,![4,18,6,1,14,9],![2,8,18,3,6,16]⟩
def cycle235_2 : CycleData E W := ⟨2,![2,17,16,10],![4,6,38,26]⟩
def cycle235_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle235_4 : CycleData E W := ⟨2,![7,19,20,12],![14,18,38,28]⟩
def cycle235_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data235 : PartitionData E W := ⟨6,![cycle235_0,cycle235_1,cycle235_2,cycle235_3,cycle235_4,cycle235_5]⟩
lemma valid_data235 : data235.Valid src235 dst235 Finset.univ := by decide +kernel

def src236 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst236 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle236_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle236_1 : CycleData E W := ⟨4,![1,2,10,16,20,6],![3,6,4,26,38,18]⟩
def cycle236_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle236_3 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle236_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle236_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data236 : PartitionData E W := ⟨6,![cycle236_0,cycle236_1,cycle236_2,cycle236_3,cycle236_4,cycle236_5]⟩
lemma valid_data236 : data236.Valid src236 dst236 Finset.univ := by decide +kernel

def src237 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst237 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle237_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle237_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle237_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle237_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle237_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle237_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data237 : PartitionData E W := ⟨6,![cycle237_0,cycle237_1,cycle237_2,cycle237_3,cycle237_4,cycle237_5]⟩
lemma valid_data237 : data237.Valid src237 dst237 Finset.univ := by decide +kernel

def src238 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst238 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle238_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle238_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle238_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle238_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle238_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle238_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data238 : PartitionData E W := ⟨6,![cycle238_0,cycle238_1,cycle238_2,cycle238_3,cycle238_4,cycle238_5]⟩
lemma valid_data238 : data238.Valid src238 dst238 Finset.univ := by decide +kernel

def src239 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst239 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle239_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle239_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,14,18]⟩
def cycle239_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle239_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle239_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle239_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data239 : PartitionData E W := ⟨6,![cycle239_0,cycle239_1,cycle239_2,cycle239_3,cycle239_4,cycle239_5]⟩
lemma valid_data239 : data239.Valid src239 dst239 Finset.univ := by decide +kernel

def src240 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst240 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle240_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle240_1 : CycleData E W := ⟨3,![1,2,3,18,6],![3,6,4,8,18]⟩
def cycle240_2 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle240_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle240_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle240_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data240 : PartitionData E W := ⟨6,![cycle240_0,cycle240_1,cycle240_2,cycle240_3,cycle240_4,cycle240_5]⟩
lemma valid_data240 : data240.Valid src240 dst240 Finset.univ := by decide +kernel

def src241 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst241 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle241_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle241_1 : CycleData E W := ⟨5,![4,18,6,1,17,16,9],![2,8,18,3,6,38,16]⟩
def cycle241_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle241_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle241_4 : CycleData E W := ⟨2,![7,19,20,12],![14,18,38,28]⟩
def cycle241_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data241 : PartitionData E W := ⟨6,![cycle241_0,cycle241_1,cycle241_2,cycle241_3,cycle241_4,cycle241_5]⟩
lemma valid_data241 : data241.Valid src241 dst241 Finset.univ := by decide +kernel

def src242 : E → W := ![2,3,6,4,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst242 : E → W := ![3,6,4,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle242_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle242_1 : CycleData E W := ⟨2,![1,17,20,6],![3,6,38,18]⟩
def cycle242_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle242_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle242_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle242_5 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle242_6 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data242 : PartitionData E W := ⟨7,![cycle242_0,cycle242_1,cycle242_2,cycle242_3,cycle242_4,cycle242_5,cycle242_6]⟩
lemma valid_data242 : data242.Valid src242 dst242 Finset.univ := by decide +kernel

def src243 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst243 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle243_0 : CycleData E W := ⟨9,![5,6,7,18,3,13,12,16,17,14,9],![2,14,3,18,8,4,28,26,38,6,16]⟩
def cycle243_1 : CycleData E W := ⟨9,![0,1,2,10,11,15,8,19,20,21,4],![2,3,6,4,14,26,16,18,28,38,8]⟩
def data243 : PartitionData E W := ⟨2,![cycle243_0,cycle243_1]⟩
lemma valid_data243 : data243.Valid src243 dst243 Finset.univ := by decide +kernel

def src244 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst244 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle244_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle244_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle244_2 : CycleData E W := ⟨3,![2,14,15,11,10],![4,6,16,26,14]⟩
def cycle244_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle244_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle244_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data244 : PartitionData E W := ⟨6,![cycle244_0,cycle244_1,cycle244_2,cycle244_3,cycle244_4,cycle244_5]⟩
lemma valid_data244 : data244.Valid src244 dst244 Finset.univ := by decide +kernel

def src245 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst245 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle245_0 : CycleData E W := ⟨9,![5,10,3,18,12,16,17,1,7,8,9],![2,14,4,8,28,26,38,6,3,18,16]⟩
def cycle245_1 : CycleData E W := ⟨9,![0,6,11,15,14,2,13,19,20,21,4],![2,3,14,26,16,6,4,28,18,38,8]⟩
def data245 : PartitionData E W := ⟨2,![cycle245_0,cycle245_1]⟩
lemma valid_data245 : data245.Valid src245 dst245 Finset.univ := by decide +kernel

def src246 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst246 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle246_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle246_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle246_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle246_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle246_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle246_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data246 : PartitionData E W := ⟨6,![cycle246_0,cycle246_1,cycle246_2,cycle246_3,cycle246_4,cycle246_5]⟩
lemma valid_data246 : data246.Valid src246 dst246 Finset.univ := by decide +kernel

def src247 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst247 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle247_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle247_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle247_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle247_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle247_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle247_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data247 : PartitionData E W := ⟨6,![cycle247_0,cycle247_1,cycle247_2,cycle247_3,cycle247_4,cycle247_5]⟩
lemma valid_data247 : data247.Valid src247 dst247 Finset.univ := by decide +kernel

def src248 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst248 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle248_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle248_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle248_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle248_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle248_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle248_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data248 : PartitionData E W := ⟨6,![cycle248_0,cycle248_1,cycle248_2,cycle248_3,cycle248_4,cycle248_5]⟩
lemma valid_data248 : data248.Valid src248 dst248 Finset.univ := by decide +kernel

def src249 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst249 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle249_0 : CycleData E W := ⟨9,![0,1,17,16,8,18,3,13,12,11,5],![2,3,6,38,16,18,8,4,28,26,14]⟩
def cycle249_1 : CycleData E W := ⟨9,![4,21,20,19,7,6,10,2,14,15,9],![2,8,38,28,18,3,14,4,6,26,16]⟩
def data249 : PartitionData E W := ⟨2,![cycle249_0,cycle249_1]⟩
lemma valid_data249 : data249.Valid src249 dst249 Finset.univ := by decide +kernel

def src250 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst250 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle250_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle250_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle250_2 : CycleData E W := ⟨2,![2,14,11,10],![4,6,26,14]⟩
def cycle250_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle250_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle250_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data250 : PartitionData E W := ⟨6,![cycle250_0,cycle250_1,cycle250_2,cycle250_3,cycle250_4,cycle250_5]⟩
lemma valid_data250 : data250.Valid src250 dst250 Finset.univ := by decide +kernel

def src251 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst251 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle251_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle251_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle251_2 : CycleData E W := ⟨2,![2,14,11,10],![4,6,26,14]⟩
def cycle251_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle251_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle251_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data251 : PartitionData E W := ⟨6,![cycle251_0,cycle251_1,cycle251_2,cycle251_3,cycle251_4,cycle251_5]⟩
lemma valid_data251 : data251.Valid src251 dst251 Finset.univ := by decide +kernel

def src252 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst252 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle252_0 : CycleData E W := ⟨9,![0,6,11,12,16,17,2,3,18,8,9],![2,3,14,28,26,38,6,4,8,18,16]⟩
def cycle252_1 : CycleData E W := ⟨9,![4,21,20,19,7,1,14,15,13,10,5],![2,8,38,28,18,3,6,16,26,4,14]⟩
def data252 : PartitionData E W := ⟨2,![cycle252_0,cycle252_1]⟩
lemma valid_data252 : data252.Valid src252 dst252 Finset.univ := by decide +kernel

def src253 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst253 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle253_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle253_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle253_2 : CycleData E W := ⟨2,![2,14,15,13],![4,6,16,26]⟩
def cycle253_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle253_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle253_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data253 : PartitionData E W := ⟨6,![cycle253_0,cycle253_1,cycle253_2,cycle253_3,cycle253_4,cycle253_5]⟩
lemma valid_data253 : data253.Valid src253 dst253 Finset.univ := by decide +kernel

def src254 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst254 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle254_0 : CycleData E W := ⟨9,![4,18,12,16,17,2,10,6,7,8,9],![2,8,28,26,38,6,4,14,3,18,16]⟩
def cycle254_1 : CycleData E W := ⟨9,![0,1,14,15,13,3,21,20,19,11,5],![2,3,6,16,26,4,8,38,18,28,14]⟩
def data254 : PartitionData E W := ⟨2,![cycle254_0,cycle254_1]⟩
lemma valid_data254 : data254.Valid src254 dst254 Finset.univ := by decide +kernel

def src255 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst255 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle255_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle255_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle255_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle255_3 : CycleData E W := ⟨3,![3,18,19,11,10],![4,8,18,28,14]⟩
def cycle255_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle255_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data255 : PartitionData E W := ⟨6,![cycle255_0,cycle255_1,cycle255_2,cycle255_3,cycle255_4,cycle255_5]⟩
lemma valid_data255 : data255.Valid src255 dst255 Finset.univ := by decide +kernel

def src256 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst256 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle256_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle256_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle256_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle256_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle256_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle256_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data256 : PartitionData E W := ⟨6,![cycle256_0,cycle256_1,cycle256_2,cycle256_3,cycle256_4,cycle256_5]⟩
lemma valid_data256 : data256.Valid src256 dst256 Finset.univ := by decide +kernel

def src257 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst257 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle257_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle257_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle257_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle257_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle257_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle257_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data257 : PartitionData E W := ⟨6,![cycle257_0,cycle257_1,cycle257_2,cycle257_3,cycle257_4,cycle257_5]⟩
lemma valid_data257 : data257.Valid src257 dst257 Finset.univ := by decide +kernel

def src258 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst258 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle258_0 : CycleData E W := ⟨9,![0,1,17,16,8,18,3,13,12,11,5],![2,3,6,38,16,18,8,4,26,28,14]⟩
def cycle258_1 : CycleData E W := ⟨9,![4,21,20,19,7,6,10,2,14,15,9],![2,8,38,28,18,3,14,4,6,26,16]⟩
def data258 : PartitionData E W := ⟨2,![cycle258_0,cycle258_1]⟩
lemma valid_data258 : data258.Valid src258 dst258 Finset.univ := by decide +kernel

def src259 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst259 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle259_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle259_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle259_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle259_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle259_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle259_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data259 : PartitionData E W := ⟨6,![cycle259_0,cycle259_1,cycle259_2,cycle259_3,cycle259_4,cycle259_5]⟩
lemma valid_data259 : data259.Valid src259 dst259 Finset.univ := by decide +kernel

def src260 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst260 : E → W := ![3,6,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle260_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle260_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle260_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle260_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle260_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle260_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data260 : PartitionData E W := ⟨6,![cycle260_0,cycle260_1,cycle260_2,cycle260_3,cycle260_4,cycle260_5]⟩
lemma valid_data260 : data260.Valid src260 dst260 Finset.univ := by decide +kernel

def src261 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst261 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle261_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,16,17,14,9],![2,8,18,3,14,28,4,26,38,6,16]⟩
def cycle261_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,3,6,4,8,38,28,18,16,26,14]⟩
def data261 : PartitionData E W := ⟨2,![cycle261_0,cycle261_1]⟩
lemma valid_data261 : data261.Valid src261 dst261 Finset.univ := by decide +kernel

def src262 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst262 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle262_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle262_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle262_2 : CycleData E W := ⟨2,![2,14,15,10],![4,6,16,26]⟩
def cycle262_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle262_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle262_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data262 : PartitionData E W := ⟨6,![cycle262_0,cycle262_1,cycle262_2,cycle262_3,cycle262_4,cycle262_5]⟩
lemma valid_data262 : data262.Valid src262 dst262 Finset.univ := by decide +kernel

def src263 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst263 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle263_0 : CycleData E W := ⟨9,![5,12,18,3,10,16,17,1,7,8,9],![2,14,28,8,4,26,38,6,3,18,16]⟩
def cycle263_1 : CycleData E W := ⟨9,![0,6,11,15,14,2,13,19,20,21,4],![2,3,14,26,16,6,4,28,18,38,8]⟩
def data263 : PartitionData E W := ⟨2,![cycle263_0,cycle263_1]⟩
lemma valid_data263 : data263.Valid src263 dst263 Finset.univ := by decide +kernel

def src264 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst264 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle264_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle264_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle264_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle264_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle264_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle264_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data264 : PartitionData E W := ⟨6,![cycle264_0,cycle264_1,cycle264_2,cycle264_3,cycle264_4,cycle264_5]⟩
lemma valid_data264 : data264.Valid src264 dst264 Finset.univ := by decide +kernel

def src265 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst265 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle265_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle265_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle265_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle265_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle265_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle265_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data265 : PartitionData E W := ⟨6,![cycle265_0,cycle265_1,cycle265_2,cycle265_3,cycle265_4,cycle265_5]⟩
lemma valid_data265 : data265.Valid src265 dst265 Finset.univ := by decide +kernel

def src266 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst266 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle266_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle266_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle266_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle266_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle266_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle266_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data266 : PartitionData E W := ⟨6,![cycle266_0,cycle266_1,cycle266_2,cycle266_3,cycle266_4,cycle266_5]⟩
lemma valid_data266 : data266.Valid src266 dst266 Finset.univ := by decide +kernel

def src267 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst267 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle267_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,14,17,16,9],![2,8,18,3,14,28,4,26,6,38,16]⟩
def cycle267_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,3,6,4,8,38,28,18,16,26,14]⟩
def data267 : PartitionData E W := ⟨2,![cycle267_0,cycle267_1]⟩
lemma valid_data267 : data267.Valid src267 dst267 Finset.univ := by decide +kernel

def src268 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst268 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle268_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle268_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle268_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle268_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle268_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle268_5 : CycleData E W := ⟨3,![11,15,16,20,12],![14,26,16,38,28]⟩
def data268 : PartitionData E W := ⟨6,![cycle268_0,cycle268_1,cycle268_2,cycle268_3,cycle268_4,cycle268_5]⟩
lemma valid_data268 : data268.Valid src268 dst268 Finset.univ := by decide +kernel

def src269 : E → W := ![2,3,6,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst269 : E → W := ![3,6,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle269_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle269_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle269_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle269_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle269_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle269_5 : CycleData E W := ⟨3,![11,15,8,19,12],![14,26,16,18,28]⟩
def data269 : PartitionData E W := ⟨6,![cycle269_0,cycle269_1,cycle269_2,cycle269_3,cycle269_4,cycle269_5]⟩
lemma valid_data269 : data269.Valid src269 dst269 Finset.univ := by decide +kernel

def src270 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst270 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle270_0 : CycleData E W := ⟨2,![0,7,18,4],![2,3,18,8]⟩
def cycle270_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle270_2 : CycleData E W := ⟨2,![2,17,21,3],![4,6,38,8]⟩
def cycle270_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle270_4 : CycleData E W := ⟨2,![10,6,19,13],![4,14,18,28]⟩
def cycle270_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data270 : PartitionData E W := ⟨6,![cycle270_0,cycle270_1,cycle270_2,cycle270_3,cycle270_4,cycle270_5]⟩
lemma valid_data270 : data270.Valid src270 dst270 Finset.univ := by decide +kernel

def src271 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst271 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle271_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle271_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle271_2 : CycleData E W := ⟨3,![2,14,15,11,10],![4,6,16,26,14]⟩
def cycle271_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle271_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle271_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data271 : PartitionData E W := ⟨6,![cycle271_0,cycle271_1,cycle271_2,cycle271_3,cycle271_4,cycle271_5]⟩
lemma valid_data271 : data271.Valid src271 dst271 Finset.univ := by decide +kernel

def src272 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst272 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle272_0 : CycleData E W := ⟨9,![4,18,13,2,17,16,11,6,7,8,9],![2,8,28,4,6,38,26,14,18,3,16]⟩
def cycle272_1 : CycleData E W := ⟨9,![0,1,14,15,12,19,20,21,3,10,5],![2,3,6,16,26,28,18,38,8,4,14]⟩
def data272 : PartitionData E W := ⟨2,![cycle272_0,cycle272_1]⟩
lemma valid_data272 : data272.Valid src272 dst272 Finset.univ := by decide +kernel

def src273 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst273 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle273_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle273_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle273_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle273_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle273_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle273_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data273 : PartitionData E W := ⟨6,![cycle273_0,cycle273_1,cycle273_2,cycle273_3,cycle273_4,cycle273_5]⟩
lemma valid_data273 : data273.Valid src273 dst273 Finset.univ := by decide +kernel

def src274 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst274 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle274_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle274_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle274_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle274_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle274_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle274_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data274 : PartitionData E W := ⟨6,![cycle274_0,cycle274_1,cycle274_2,cycle274_3,cycle274_4,cycle274_5]⟩
lemma valid_data274 : data274.Valid src274 dst274 Finset.univ := by decide +kernel

def src275 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst275 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle275_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle275_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle275_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle275_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle275_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle275_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data275 : PartitionData E W := ⟨6,![cycle275_0,cycle275_1,cycle275_2,cycle275_3,cycle275_4,cycle275_5]⟩
lemma valid_data275 : data275.Valid src275 dst275 Finset.univ := by decide +kernel

def src276 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst276 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle276_0 : CycleData E W := ⟨9,![0,8,16,17,2,13,12,11,6,18,4],![2,3,16,38,6,4,28,26,14,18,8]⟩
def cycle276_1 : CycleData E W := ⟨9,![5,10,3,21,20,19,7,1,14,15,9],![2,14,4,8,38,28,18,3,6,26,16]⟩
def data276 : PartitionData E W := ⟨2,![cycle276_0,cycle276_1]⟩
lemma valid_data276 : data276.Valid src276 dst276 Finset.univ := by decide +kernel

def src277 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst277 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle277_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle277_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle277_2 : CycleData E W := ⟨2,![2,14,11,10],![4,6,26,14]⟩
def cycle277_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle277_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle277_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data277 : PartitionData E W := ⟨6,![cycle277_0,cycle277_1,cycle277_2,cycle277_3,cycle277_4,cycle277_5]⟩
lemma valid_data277 : data277.Valid src277 dst277 Finset.univ := by decide +kernel

def src278 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst278 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle278_0 : CycleData E W := ⟨9,![0,7,6,10,3,18,12,14,17,16,9],![2,3,18,14,4,8,28,26,6,38,16]⟩
def cycle278_1 : CycleData E W := ⟨9,![4,21,20,19,13,2,1,8,15,11,5],![2,8,38,18,28,4,6,3,16,26,14]⟩
def data278 : PartitionData E W := ⟨2,![cycle278_0,cycle278_1]⟩
lemma valid_data278 : data278.Valid src278 dst278 Finset.univ := by decide +kernel

def src279 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst279 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle279_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle279_1 : CycleData E W := ⟨3,![1,17,21,18,7],![3,6,38,8,18]⟩
def cycle279_2 : CycleData E W := ⟨2,![2,14,15,13],![4,6,16,26]⟩
def cycle279_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle279_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle279_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data279 : PartitionData E W := ⟨6,![cycle279_0,cycle279_1,cycle279_2,cycle279_3,cycle279_4,cycle279_5]⟩
lemma valid_data279 : data279.Valid src279 dst279 Finset.univ := by decide +kernel

def src280 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst280 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle280_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle280_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle280_2 : CycleData E W := ⟨2,![2,14,15,13],![4,6,16,26]⟩
def cycle280_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle280_4 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle280_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data280 : PartitionData E W := ⟨6,![cycle280_0,cycle280_1,cycle280_2,cycle280_3,cycle280_4,cycle280_5]⟩
lemma valid_data280 : data280.Valid src280 dst280 Finset.univ := by decide +kernel

def src281 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst281 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle281_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle281_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle281_2 : CycleData E W := ⟨2,![2,14,15,13],![4,6,16,26]⟩
def cycle281_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle281_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle281_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data281 : PartitionData E W := ⟨6,![cycle281_0,cycle281_1,cycle281_2,cycle281_3,cycle281_4,cycle281_5]⟩
lemma valid_data281 : data281.Valid src281 dst281 Finset.univ := by decide +kernel

def src282 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst282 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle282_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle282_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle282_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle282_3 : CycleData E W := ⟨3,![3,18,19,11,10],![4,8,18,28,14]⟩
def cycle282_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle282_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data282 : PartitionData E W := ⟨6,![cycle282_0,cycle282_1,cycle282_2,cycle282_3,cycle282_4,cycle282_5]⟩
lemma valid_data282 : data282.Valid src282 dst282 Finset.univ := by decide +kernel

def src283 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst283 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle283_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle283_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle283_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle283_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle283_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle283_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data283 : PartitionData E W := ⟨6,![cycle283_0,cycle283_1,cycle283_2,cycle283_3,cycle283_4,cycle283_5]⟩
lemma valid_data283 : data283.Valid src283 dst283 Finset.univ := by decide +kernel

def src284 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst284 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle284_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle284_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle284_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle284_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle284_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle284_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data284 : PartitionData E W := ⟨6,![cycle284_0,cycle284_1,cycle284_2,cycle284_3,cycle284_4,cycle284_5]⟩
lemma valid_data284 : data284.Valid src284 dst284 Finset.univ := by decide +kernel

def src285 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst285 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle285_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle285_1 : CycleData E W := ⟨3,![1,17,21,18,7],![3,6,38,8,18]⟩
def cycle285_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle285_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle285_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle285_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data285 : PartitionData E W := ⟨6,![cycle285_0,cycle285_1,cycle285_2,cycle285_3,cycle285_4,cycle285_5]⟩
lemma valid_data285 : data285.Valid src285 dst285 Finset.univ := by decide +kernel

def src286 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst286 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle286_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle286_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle286_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle286_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle286_4 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle286_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data286 : PartitionData E W := ⟨6,![cycle286_0,cycle286_1,cycle286_2,cycle286_3,cycle286_4,cycle286_5]⟩
lemma valid_data286 : data286.Valid src286 dst286 Finset.univ := by decide +kernel

def src287 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst287 : E → W := ![3,6,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle287_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle287_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle287_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle287_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle287_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle287_5 : CycleData E W := ⟨3,![18,12,15,16,21],![8,28,26,16,38]⟩
def data287 : PartitionData E W := ⟨6,![cycle287_0,cycle287_1,cycle287_2,cycle287_3,cycle287_4,cycle287_5]⟩
lemma valid_data287 : data287.Valid src287 dst287 Finset.univ := by decide +kernel

def src288 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst288 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle288_0 : CycleData E W := ⟨2,![0,7,18,4],![2,3,18,8]⟩
def cycle288_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle288_2 : CycleData E W := ⟨2,![2,17,16,10],![4,6,38,26]⟩
def cycle288_3 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle288_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle288_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data288 : PartitionData E W := ⟨6,![cycle288_0,cycle288_1,cycle288_2,cycle288_3,cycle288_4,cycle288_5]⟩
lemma valid_data288 : data288.Valid src288 dst288 Finset.univ := by decide +kernel

def src289 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst289 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle289_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle289_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle289_2 : CycleData E W := ⟨2,![2,14,15,10],![4,6,16,26]⟩
def cycle289_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle289_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle289_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data289 : PartitionData E W := ⟨6,![cycle289_0,cycle289_1,cycle289_2,cycle289_3,cycle289_4,cycle289_5]⟩
lemma valid_data289 : data289.Valid src289 dst289 Finset.univ := by decide +kernel

def src290 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst290 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle290_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle290_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle290_2 : CycleData E W := ⟨2,![2,14,15,10],![4,6,16,26]⟩
def cycle290_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle290_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle290_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data290 : PartitionData E W := ⟨6,![cycle290_0,cycle290_1,cycle290_2,cycle290_3,cycle290_4,cycle290_5]⟩
lemma valid_data290 : data290.Valid src290 dst290 Finset.univ := by decide +kernel

def src291 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst291 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle291_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle291_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle291_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle291_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle291_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle291_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data291 : PartitionData E W := ⟨6,![cycle291_0,cycle291_1,cycle291_2,cycle291_3,cycle291_4,cycle291_5]⟩
lemma valid_data291 : data291.Valid src291 dst291 Finset.univ := by decide +kernel

def src292 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst292 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle292_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle292_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle292_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle292_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle292_4 : CycleData E W := ⟨3,![4,18,19,15,9],![2,8,18,38,16]⟩
def cycle292_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data292 : PartitionData E W := ⟨6,![cycle292_0,cycle292_1,cycle292_2,cycle292_3,cycle292_4,cycle292_5]⟩
lemma valid_data292 : data292.Valid src292 dst292 Finset.univ := by decide +kernel

def src293 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst293 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle293_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,18,14]⟩
def cycle293_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle293_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle293_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle293_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle293_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data293 : PartitionData E W := ⟨6,![cycle293_0,cycle293_1,cycle293_2,cycle293_3,cycle293_4,cycle293_5]⟩
lemma valid_data293 : data293.Valid src293 dst293 Finset.univ := by decide +kernel

def src294 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst294 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle294_0 : CycleData E W := ⟨2,![0,7,18,4],![2,3,18,8]⟩
def cycle294_1 : CycleData E W := ⟨2,![1,17,16,8],![3,6,38,16]⟩
def cycle294_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle294_3 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle294_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle294_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data294 : PartitionData E W := ⟨6,![cycle294_0,cycle294_1,cycle294_2,cycle294_3,cycle294_4,cycle294_5]⟩
lemma valid_data294 : data294.Valid src294 dst294 Finset.univ := by decide +kernel

def src295 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst295 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle295_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle295_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle295_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle295_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle295_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle295_5 : CycleData E W := ⟨3,![11,15,16,20,12],![14,26,16,38,28]⟩
def data295 : PartitionData E W := ⟨6,![cycle295_0,cycle295_1,cycle295_2,cycle295_3,cycle295_4,cycle295_5]⟩
lemma valid_data295 : data295.Valid src295 dst295 Finset.univ := by decide +kernel

def src296 : E → W := ![2,3,6,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst296 : E → W := ![3,6,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle296_0 : CycleData E W := ⟨1,![0,8,9],![2,3,16]⟩
def cycle296_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle296_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle296_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle296_4 : CycleData E W := ⟨4,![4,21,16,15,11,5],![2,8,38,16,26,14]⟩
def cycle296_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data296 : PartitionData E W := ⟨6,![cycle296_0,cycle296_1,cycle296_2,cycle296_3,cycle296_4,cycle296_5]⟩
lemma valid_data296 : data296.Valid src296 dst296 Finset.univ := by decide +kernel

def src297 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst297 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle297_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle297_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle297_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle297_3 : CycleData E W := ⟨3,![4,21,17,14,5],![2,8,38,6,16]⟩
def cycle297_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle297_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data297 : PartitionData E W := ⟨6,![cycle297_0,cycle297_1,cycle297_2,cycle297_3,cycle297_4,cycle297_5]⟩
lemma valid_data297 : data297.Valid src297 dst297 Finset.univ := by decide +kernel

def src298 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst298 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle298_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle298_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle298_2 : CycleData E W := ⟨3,![2,14,15,11,10],![4,6,16,26,14]⟩
def cycle298_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle298_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle298_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data298 : PartitionData E W := ⟨6,![cycle298_0,cycle298_1,cycle298_2,cycle298_3,cycle298_4,cycle298_5]⟩
lemma valid_data298 : data298.Valid src298 dst298 Finset.univ := by decide +kernel

def src299 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst299 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle299_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle299_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle299_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle299_3 : CycleData E W := ⟨3,![4,21,17,14,5],![2,8,38,6,16]⟩
def cycle299_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle299_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data299 : PartitionData E W := ⟨6,![cycle299_0,cycle299_1,cycle299_2,cycle299_3,cycle299_4,cycle299_5]⟩
lemma valid_data299 : data299.Valid src299 dst299 Finset.univ := by decide +kernel

def src300 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst300 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle300_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle300_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle300_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle300_3 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle300_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle300_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data300 : PartitionData E W := ⟨6,![cycle300_0,cycle300_1,cycle300_2,cycle300_3,cycle300_4,cycle300_5]⟩
lemma valid_data300 : data300.Valid src300 dst300 Finset.univ := by decide +kernel

def src301 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst301 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle301_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle301_1 : CycleData E W := ⟨3,![1,14,15,19,8],![3,6,16,38,18]⟩
def cycle301_2 : CycleData E W := ⟨2,![2,17,11,10],![4,6,26,14]⟩
def cycle301_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle301_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle301_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data301 : PartitionData E W := ⟨6,![cycle301_0,cycle301_1,cycle301_2,cycle301_3,cycle301_4,cycle301_5]⟩
lemma valid_data301 : data301.Valid src301 dst301 Finset.univ := by decide +kernel

def src302 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst302 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle302_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle302_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle302_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle302_3 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle302_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle302_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data302 : PartitionData E W := ⟨6,![cycle302_0,cycle302_1,cycle302_2,cycle302_3,cycle302_4,cycle302_5]⟩
lemma valid_data302 : data302.Valid src302 dst302 Finset.univ := by decide +kernel

def src303 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst303 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle303_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle303_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle303_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle303_3 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle303_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle303_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data303 : PartitionData E W := ⟨6,![cycle303_0,cycle303_1,cycle303_2,cycle303_3,cycle303_4,cycle303_5]⟩
lemma valid_data303 : data303.Valid src303 dst303 Finset.univ := by decide +kernel

def src304 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst304 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle304_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle304_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle304_2 : CycleData E W := ⟨2,![2,14,11,10],![4,6,26,14]⟩
def cycle304_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle304_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle304_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data304 : PartitionData E W := ⟨6,![cycle304_0,cycle304_1,cycle304_2,cycle304_3,cycle304_4,cycle304_5]⟩
lemma valid_data304 : data304.Valid src304 dst304 Finset.univ := by decide +kernel

def src305 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst305 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle305_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle305_1 : CycleData E W := ⟨2,![1,2,10,7],![3,6,4,14]⟩
def cycle305_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle305_3 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle305_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle305_5 : CycleData E W := ⟨3,![14,12,19,20,17],![6,26,28,18,38]⟩
def data305 : PartitionData E W := ⟨6,![cycle305_0,cycle305_1,cycle305_2,cycle305_3,cycle305_4,cycle305_5]⟩
lemma valid_data305 : data305.Valid src305 dst305 Finset.univ := by decide +kernel

def src306 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst306 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle306_0 : CycleData E W := ⟨2,![0,1,14,5],![2,3,6,16]⟩
def cycle306_1 : CycleData E W := ⟨2,![2,17,21,3],![4,6,38,8]⟩
def cycle306_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle306_3 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle306_4 : CycleData E W := ⟨2,![7,11,19,8],![3,14,28,18]⟩
def cycle306_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data306 : PartitionData E W := ⟨6,![cycle306_0,cycle306_1,cycle306_2,cycle306_3,cycle306_4,cycle306_5]⟩
lemma valid_data306 : data306.Valid src306 dst306 Finset.univ := by decide +kernel

def src307 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst307 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle307_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle307_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle307_2 : CycleData E W := ⟨2,![2,14,15,13],![4,6,16,26]⟩
def cycle307_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle307_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle307_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data307 : PartitionData E W := ⟨6,![cycle307_0,cycle307_1,cycle307_2,cycle307_3,cycle307_4,cycle307_5]⟩
lemma valid_data307 : data307.Valid src307 dst307 Finset.univ := by decide +kernel

def src308 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst308 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle308_0 : CycleData E W := ⟨9,![5,6,11,18,3,13,16,17,1,8,9],![2,16,14,28,8,4,26,38,6,3,18]⟩
def cycle308_1 : CycleData E W := ⟨9,![0,7,10,2,14,15,12,19,20,21,4],![2,3,14,4,6,16,26,28,18,38,8]⟩
def data308 : PartitionData E W := ⟨2,![cycle308_0,cycle308_1]⟩
lemma valid_data308 : data308.Valid src308 dst308 Finset.univ := by decide +kernel

def src309 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst309 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle309_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle309_1 : CycleData E W := ⟨2,![1,14,6,7],![3,6,16,14]⟩
def cycle309_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle309_3 : CycleData E W := ⟨3,![3,18,19,11,10],![4,8,18,28,14]⟩
def cycle309_4 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle309_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data309 : PartitionData E W := ⟨6,![cycle309_0,cycle309_1,cycle309_2,cycle309_3,cycle309_4,cycle309_5]⟩
lemma valid_data309 : data309.Valid src309 dst309 Finset.univ := by decide +kernel

def src310 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst310 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle310_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle310_1 : CycleData E W := ⟨3,![1,14,15,19,8],![3,6,16,38,18]⟩
def cycle310_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle310_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle310_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle310_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data310 : PartitionData E W := ⟨6,![cycle310_0,cycle310_1,cycle310_2,cycle310_3,cycle310_4,cycle310_5]⟩
lemma valid_data310 : data310.Valid src310 dst310 Finset.univ := by decide +kernel

def src311 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst311 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle311_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle311_1 : CycleData E W := ⟨2,![1,14,6,7],![3,6,16,14]⟩
def cycle311_2 : CycleData E W := ⟨1,![2,17,13],![4,6,26]⟩
def cycle311_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle311_4 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle311_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data311 : PartitionData E W := ⟨6,![cycle311_0,cycle311_1,cycle311_2,cycle311_3,cycle311_4,cycle311_5]⟩
lemma valid_data311 : data311.Valid src311 dst311 Finset.univ := by decide +kernel

def src312 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst312 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle312_0 : CycleData E W := ⟨9,![4,18,8,7,11,12,13,2,17,16,5],![2,8,18,3,14,28,26,4,6,38,16]⟩
def cycle312_1 : CycleData E W := ⟨9,![0,1,14,15,6,10,3,21,20,19,9],![2,3,6,26,16,14,4,8,38,28,18]⟩
def data312 : PartitionData E W := ⟨2,![cycle312_0,cycle312_1]⟩
lemma valid_data312 : data312.Valid src312 dst312 Finset.univ := by decide +kernel

def src313 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst313 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle313_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle313_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle313_2 : CycleData E W := ⟨1,![2,14,13],![4,6,26]⟩
def cycle313_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle313_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle313_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data313 : PartitionData E W := ⟨6,![cycle313_0,cycle313_1,cycle313_2,cycle313_3,cycle313_4,cycle313_5]⟩
lemma valid_data313 : data313.Valid src313 dst313 Finset.univ := by decide +kernel

def src314 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst314 : E → W := ![3,6,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle314_0 : CycleData E W := ⟨9,![4,18,12,13,10,6,16,17,1,8,9],![2,8,28,26,4,14,16,38,6,3,18]⟩
def cycle314_1 : CycleData E W := ⟨9,![0,7,11,19,20,21,3,2,14,15,5],![2,3,14,28,18,38,8,4,6,26,16]⟩
def data314 : PartitionData E W := ⟨2,![cycle314_0,cycle314_1]⟩
lemma valid_data314 : data314.Valid src314 dst314 Finset.univ := by decide +kernel

def src315 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst315 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle315_0 : CycleData E W := ⟨2,![0,1,14,5],![2,3,6,16]⟩
def cycle315_1 : CycleData E W := ⟨2,![2,17,16,10],![4,6,38,26]⟩
def cycle315_2 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle315_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle315_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle315_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data315 : PartitionData E W := ⟨6,![cycle315_0,cycle315_1,cycle315_2,cycle315_3,cycle315_4,cycle315_5]⟩
lemma valid_data315 : data315.Valid src315 dst315 Finset.univ := by decide +kernel

def src316 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst316 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle316_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle316_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle316_2 : CycleData E W := ⟨2,![2,14,15,10],![4,6,16,26]⟩
def cycle316_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle316_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle316_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data316 : PartitionData E W := ⟨6,![cycle316_0,cycle316_1,cycle316_2,cycle316_3,cycle316_4,cycle316_5]⟩
lemma valid_data316 : data316.Valid src316 dst316 Finset.univ := by decide +kernel

def src317 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst317 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle317_0 : CycleData E W := ⟨2,![0,1,14,5],![2,3,6,16]⟩
def cycle317_1 : CycleData E W := ⟨2,![2,17,16,10],![4,6,38,26]⟩
def cycle317_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle317_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle317_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle317_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data317 : PartitionData E W := ⟨6,![cycle317_0,cycle317_1,cycle317_2,cycle317_3,cycle317_4,cycle317_5]⟩
lemma valid_data317 : data317.Valid src317 dst317 Finset.univ := by decide +kernel

def src318 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst318 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle318_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle318_1 : CycleData E W := ⟨2,![1,14,6,7],![3,6,16,14]⟩
def cycle318_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle318_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle318_4 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle318_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data318 : PartitionData E W := ⟨6,![cycle318_0,cycle318_1,cycle318_2,cycle318_3,cycle318_4,cycle318_5]⟩
lemma valid_data318 : data318.Valid src318 dst318 Finset.univ := by decide +kernel

def src319 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst319 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle319_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle319_1 : CycleData E W := ⟨3,![1,14,15,19,8],![3,6,16,38,18]⟩
def cycle319_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle319_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle319_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle319_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data319 : PartitionData E W := ⟨6,![cycle319_0,cycle319_1,cycle319_2,cycle319_3,cycle319_4,cycle319_5]⟩
lemma valid_data319 : data319.Valid src319 dst319 Finset.univ := by decide +kernel

def src320 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst320 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle320_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle320_1 : CycleData E W := ⟨2,![1,14,6,7],![3,6,16,14]⟩
def cycle320_2 : CycleData E W := ⟨1,![2,17,10],![4,6,26]⟩
def cycle320_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle320_4 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle320_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data320 : PartitionData E W := ⟨6,![cycle320_0,cycle320_1,cycle320_2,cycle320_3,cycle320_4,cycle320_5]⟩
lemma valid_data320 : data320.Valid src320 dst320 Finset.univ := by decide +kernel

def src321 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst321 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle321_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle321_1 : CycleData E W := ⟨3,![1,17,20,12,7],![3,6,38,28,14]⟩
def cycle321_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle321_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle321_4 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle321_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data321 : PartitionData E W := ⟨6,![cycle321_0,cycle321_1,cycle321_2,cycle321_3,cycle321_4,cycle321_5]⟩
lemma valid_data321 : data321.Valid src321 dst321 Finset.univ := by decide +kernel

def src322 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst322 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle322_0 : CycleData E W := ⟨2,![0,7,6,5],![2,3,14,16]⟩
def cycle322_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle322_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle322_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle322_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle322_5 : CycleData E W := ⟨3,![11,15,16,20,12],![14,26,16,38,28]⟩
def data322 : PartitionData E W := ⟨6,![cycle322_0,cycle322_1,cycle322_2,cycle322_3,cycle322_4,cycle322_5]⟩
lemma valid_data322 : data322.Valid src322 dst322 Finset.univ := by decide +kernel

def src323 : E → W := ![2,3,6,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst323 : E → W := ![3,6,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle323_0 : CycleData E W := ⟨1,![0,8,9],![2,3,18]⟩
def cycle323_1 : CycleData E W := ⟨4,![1,17,20,19,12,7],![3,6,38,18,28,14]⟩
def cycle323_2 : CycleData E W := ⟨1,![2,14,10],![4,6,26]⟩
def cycle323_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle323_4 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle323_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data323 : PartitionData E W := ⟨6,![cycle323_0,cycle323_1,cycle323_2,cycle323_3,cycle323_4,cycle323_5]⟩
lemma valid_data323 : data323.Valid src323 dst323 Finset.univ := by decide +kernel

def src324 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst324 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle324_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle324_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle324_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle324_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle324_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle324_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data324 : PartitionData E W := ⟨6,![cycle324_0,cycle324_1,cycle324_2,cycle324_3,cycle324_4,cycle324_5]⟩
lemma valid_data324 : data324.Valid src324 dst324 Finset.univ := by decide +kernel

def src325 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst325 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle325_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle325_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle325_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle325_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle325_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle325_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data325 : PartitionData E W := ⟨6,![cycle325_0,cycle325_1,cycle325_2,cycle325_3,cycle325_4,cycle325_5]⟩
lemma valid_data325 : data325.Valid src325 dst325 Finset.univ := by decide +kernel

def src326 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst326 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle326_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle326_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle326_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle326_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle326_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle326_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data326 : PartitionData E W := ⟨6,![cycle326_0,cycle326_1,cycle326_2,cycle326_3,cycle326_4,cycle326_5]⟩
lemma valid_data326 : data326.Valid src326 dst326 Finset.univ := by decide +kernel

def src327 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst327 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle327_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle327_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle327_2 : CycleData E W := ⟨3,![4,3,2,14,9],![2,4,8,6,16]⟩
def cycle327_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle327_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle327_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data327 : PartitionData E W := ⟨6,![cycle327_0,cycle327_1,cycle327_2,cycle327_3,cycle327_4,cycle327_5]⟩
lemma valid_data327 : data327.Valid src327 dst327 Finset.univ := by decide +kernel

def src328 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst328 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle328_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle328_1 : CycleData E W := ⟨4,![4,10,6,1,14,9],![2,4,14,3,6,16]⟩
def cycle328_2 : CycleData E W := ⟨3,![2,18,7,11,17],![6,8,18,14,26]⟩
def cycle328_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle328_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle328_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data328 : PartitionData E W := ⟨6,![cycle328_0,cycle328_1,cycle328_2,cycle328_3,cycle328_4,cycle328_5]⟩
lemma valid_data328 : data328.Valid src328 dst328 Finset.univ := by decide +kernel

def src329 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst329 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle329_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle329_1 : CycleData E W := ⟨4,![4,10,6,1,14,9],![2,4,14,3,6,16]⟩
def cycle329_2 : CycleData E W := ⟨2,![2,21,16,17],![6,8,38,26]⟩
def cycle329_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle329_4 : CycleData E W := ⟨2,![7,19,12,11],![14,18,28,26]⟩
def cycle329_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data329 : PartitionData E W := ⟨6,![cycle329_0,cycle329_1,cycle329_2,cycle329_3,cycle329_4,cycle329_5]⟩
lemma valid_data329 : data329.Valid src329 dst329 Finset.univ := by decide +kernel

def src330 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst330 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle330_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle330_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle330_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle330_3 : CycleData E W := ⟨3,![4,3,18,8,9],![2,4,8,18,16]⟩
def cycle330_4 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle330_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data330 : PartitionData E W := ⟨6,![cycle330_0,cycle330_1,cycle330_2,cycle330_3,cycle330_4,cycle330_5]⟩
lemma valid_data330 : data330.Valid src330 dst330 Finset.univ := by decide +kernel

def src331 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst331 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle331_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle331_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle331_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle331_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle331_4 : CycleData E W := ⟨3,![4,10,7,8,9],![2,4,14,18,16]⟩
def cycle331_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data331 : PartitionData E W := ⟨6,![cycle331_0,cycle331_1,cycle331_2,cycle331_3,cycle331_4,cycle331_5]⟩
lemma valid_data331 : data331.Valid src331 dst331 Finset.univ := by decide +kernel

def src332 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst332 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle332_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle332_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle332_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle332_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle332_4 : CycleData E W := ⟨3,![4,10,7,8,9],![2,4,14,18,16]⟩
def cycle332_5 : CycleData E W := ⟨3,![15,12,19,20,16],![16,26,28,18,38]⟩
def data332 : PartitionData E W := ⟨6,![cycle332_0,cycle332_1,cycle332_2,cycle332_3,cycle332_4,cycle332_5]⟩
lemma valid_data332 : data332.Valid src332 dst332 Finset.univ := by decide +kernel

def src333 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst333 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle333_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle333_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle333_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle333_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle333_4 : CycleData E W := ⟨3,![14,8,18,21,17],![6,16,18,8,38]⟩
def cycle333_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data333 : PartitionData E W := ⟨6,![cycle333_0,cycle333_1,cycle333_2,cycle333_3,cycle333_4,cycle333_5]⟩
lemma valid_data333 : data333.Valid src333 dst333 Finset.univ := by decide +kernel

def src334 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst334 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle334_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle334_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle334_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle334_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle334_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle334_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data334 : PartitionData E W := ⟨6,![cycle334_0,cycle334_1,cycle334_2,cycle334_3,cycle334_4,cycle334_5]⟩
lemma valid_data334 : data334.Valid src334 dst334 Finset.univ := by decide +kernel

def src335 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst335 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle335_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle335_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle335_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle335_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle335_4 : CycleData E W := ⟨2,![14,8,20,17],![6,16,18,38]⟩
def cycle335_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data335 : PartitionData E W := ⟨6,![cycle335_0,cycle335_1,cycle335_2,cycle335_3,cycle335_4,cycle335_5]⟩
lemma valid_data335 : data335.Valid src335 dst335 Finset.univ := by decide +kernel

def src336 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst336 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle336_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle336_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle336_2 : CycleData E W := ⟨3,![4,13,17,14,9],![2,4,26,6,16]⟩
def cycle336_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle336_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle336_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data336 : PartitionData E W := ⟨6,![cycle336_0,cycle336_1,cycle336_2,cycle336_3,cycle336_4,cycle336_5]⟩
lemma valid_data336 : data336.Valid src336 dst336 Finset.univ := by decide +kernel

def src337 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst337 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle337_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle337_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle337_2 : CycleData E W := ⟨3,![4,13,17,14,9],![2,4,26,6,16]⟩
def cycle337_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle337_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle337_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data337 : PartitionData E W := ⟨6,![cycle337_0,cycle337_1,cycle337_2,cycle337_3,cycle337_4,cycle337_5]⟩
lemma valid_data337 : data337.Valid src337 dst337 Finset.univ := by decide +kernel

def src338 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst338 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle338_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle338_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle338_2 : CycleData E W := ⟨3,![4,13,17,14,9],![2,4,26,6,16]⟩
def cycle338_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle338_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle338_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data338 : PartitionData E W := ⟨6,![cycle338_0,cycle338_1,cycle338_2,cycle338_3,cycle338_4,cycle338_5]⟩
lemma valid_data338 : data338.Valid src338 dst338 Finset.univ := by decide +kernel

def src339 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst339 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle339_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle339_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle339_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle339_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle339_4 : CycleData E W := ⟨2,![18,8,16,21],![8,18,16,38]⟩
def cycle339_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data339 : PartitionData E W := ⟨6,![cycle339_0,cycle339_1,cycle339_2,cycle339_3,cycle339_4,cycle339_5]⟩
lemma valid_data339 : data339.Valid src339 dst339 Finset.univ := by decide +kernel

def src340 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst340 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle340_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle340_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle340_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle340_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle340_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle340_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data340 : PartitionData E W := ⟨6,![cycle340_0,cycle340_1,cycle340_2,cycle340_3,cycle340_4,cycle340_5]⟩
lemma valid_data340 : data340.Valid src340 dst340 Finset.univ := by decide +kernel

def src341 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst341 : E → W := ![3,6,8,4,2,3,14,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle341_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle341_1 : CycleData E W := ⟨3,![1,2,3,10,6],![3,6,8,4,14]⟩
def cycle341_2 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle341_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle341_4 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def cycle341_5 : CycleData E W := ⟨3,![14,12,18,21,17],![6,26,28,8,38]⟩
def data341 : PartitionData E W := ⟨6,![cycle341_0,cycle341_1,cycle341_2,cycle341_3,cycle341_4,cycle341_5]⟩
lemma valid_data341 : data341.Valid src341 dst341 Finset.univ := by decide +kernel

def src342 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst342 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle342_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle342_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle342_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle342_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle342_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle342_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data342 : PartitionData E W := ⟨6,![cycle342_0,cycle342_1,cycle342_2,cycle342_3,cycle342_4,cycle342_5]⟩
lemma valid_data342 : data342.Valid src342 dst342 Finset.univ := by decide +kernel

def src343 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst343 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle343_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle343_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle343_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle343_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle343_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle343_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data343 : PartitionData E W := ⟨6,![cycle343_0,cycle343_1,cycle343_2,cycle343_3,cycle343_4,cycle343_5]⟩
lemma valid_data343 : data343.Valid src343 dst343 Finset.univ := by decide +kernel

def src344 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst344 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle344_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle344_1 : CycleData E W := ⟨3,![1,14,8,7,6],![3,6,16,18,14]⟩
def cycle344_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle344_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle344_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle344_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data344 : PartitionData E W := ⟨6,![cycle344_0,cycle344_1,cycle344_2,cycle344_3,cycle344_4,cycle344_5]⟩
lemma valid_data344 : data344.Valid src344 dst344 Finset.univ := by decide +kernel

def src345 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst345 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle345_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle345_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle345_2 : CycleData E W := ⟨3,![4,3,2,14,9],![2,4,8,6,16]⟩
def cycle345_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle345_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle345_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data345 : PartitionData E W := ⟨6,![cycle345_0,cycle345_1,cycle345_2,cycle345_3,cycle345_4,cycle345_5]⟩
lemma valid_data345 : data345.Valid src345 dst345 Finset.univ := by decide +kernel

def src346 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst346 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle346_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle346_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle346_2 : CycleData E W := ⟨3,![4,3,2,14,9],![2,4,8,6,16]⟩
def cycle346_3 : CycleData E W := ⟨2,![18,7,12,21],![8,18,14,28]⟩
def cycle346_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle346_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data346 : PartitionData E W := ⟨6,![cycle346_0,cycle346_1,cycle346_2,cycle346_3,cycle346_4,cycle346_5]⟩
lemma valid_data346 : data346.Valid src346 dst346 Finset.univ := by decide +kernel

def src347 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst347 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle347_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle347_1 : CycleData E W := ⟨5,![4,10,11,6,1,14,9],![2,4,26,14,3,6,16]⟩
def cycle347_2 : CycleData E W := ⟨2,![2,21,16,17],![6,8,38,26]⟩
def cycle347_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle347_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle347_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data347 : PartitionData E W := ⟨6,![cycle347_0,cycle347_1,cycle347_2,cycle347_3,cycle347_4,cycle347_5]⟩
lemma valid_data347 : data347.Valid src347 dst347 Finset.univ := by decide +kernel

def src348 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst348 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle348_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle348_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle348_2 : CycleData E W := ⟨3,![2,18,8,16,17],![6,8,18,16,38]⟩
def cycle348_3 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle348_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle348_5 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def data348 : PartitionData E W := ⟨6,![cycle348_0,cycle348_1,cycle348_2,cycle348_3,cycle348_4,cycle348_5]⟩
lemma valid_data348 : data348.Valid src348 dst348 Finset.univ := by decide +kernel

def src349 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst349 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle349_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle349_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle349_2 : CycleData E W := ⟨3,![2,18,8,16,17],![6,8,18,16,38]⟩
def cycle349_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle349_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle349_5 : CycleData E W := ⟨2,![7,19,20,12],![14,18,38,28]⟩
def data349 : PartitionData E W := ⟨6,![cycle349_0,cycle349_1,cycle349_2,cycle349_3,cycle349_4,cycle349_5]⟩
lemma valid_data349 : data349.Valid src349 dst349 Finset.univ := by decide +kernel

def src350 : E → W := ![2,3,6,8,4,2,3,14,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst350 : E → W := ![3,6,8,4,2,3,14,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle350_0 : CycleData E W := ⟨0,![0,5],![2,3]⟩
def cycle350_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle350_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle350_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle350_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle350_5 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle350_6 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data350 : PartitionData E W := ⟨7,![cycle350_0,cycle350_1,cycle350_2,cycle350_3,cycle350_4,cycle350_5,cycle350_6]⟩
lemma valid_data350 : data350.Valid src350 dst350 Finset.univ := by decide +kernel

def src351 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst351 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle351_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle351_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle351_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle351_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle351_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle351_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data351 : PartitionData E W := ⟨6,![cycle351_0,cycle351_1,cycle351_2,cycle351_3,cycle351_4,cycle351_5]⟩
lemma valid_data351 : data351.Valid src351 dst351 Finset.univ := by decide +kernel

def src352 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst352 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle352_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle352_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle352_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle352_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle352_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle352_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data352 : PartitionData E W := ⟨6,![cycle352_0,cycle352_1,cycle352_2,cycle352_3,cycle352_4,cycle352_5]⟩
lemma valid_data352 : data352.Valid src352 dst352 Finset.univ := by decide +kernel

def src353 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst353 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle353_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle353_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle353_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle353_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle353_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle353_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data353 : PartitionData E W := ⟨6,![cycle353_0,cycle353_1,cycle353_2,cycle353_3,cycle353_4,cycle353_5]⟩
lemma valid_data353 : data353.Valid src353 dst353 Finset.univ := by decide +kernel

def src354 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst354 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle354_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,18,16]⟩
def cycle354_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle354_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle354_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle354_4 : CycleData E W := ⟨1,![4,10,5],![2,4,14]⟩
def cycle354_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data354 : PartitionData E W := ⟨6,![cycle354_0,cycle354_1,cycle354_2,cycle354_3,cycle354_4,cycle354_5]⟩
lemma valid_data354 : data354.Valid src354 dst354 Finset.univ := by decide +kernel

def src355 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst355 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle355_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle355_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle355_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle355_3 : CycleData E W := ⟨4,![4,10,11,17,14,9],![2,4,14,26,6,16]⟩
def cycle355_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle355_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data355 : PartitionData E W := ⟨6,![cycle355_0,cycle355_1,cycle355_2,cycle355_3,cycle355_4,cycle355_5]⟩
lemma valid_data355 : data355.Valid src355 dst355 Finset.univ := by decide +kernel

def src356 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst356 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle356_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,18,16]⟩
def cycle356_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle356_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle356_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle356_4 : CycleData E W := ⟨1,![4,10,5],![2,4,14]⟩
def cycle356_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data356 : PartitionData E W := ⟨6,![cycle356_0,cycle356_1,cycle356_2,cycle356_3,cycle356_4,cycle356_5]⟩
lemma valid_data356 : data356.Valid src356 dst356 Finset.univ := by decide +kernel

def src357 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst357 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle357_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,18,16]⟩
def cycle357_1 : CycleData E W := ⟨2,![1,14,11,6],![3,6,26,14]⟩
def cycle357_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle357_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle357_4 : CycleData E W := ⟨1,![4,10,5],![2,4,14]⟩
def cycle357_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data357 : PartitionData E W := ⟨6,![cycle357_0,cycle357_1,cycle357_2,cycle357_3,cycle357_4,cycle357_5]⟩
lemma valid_data357 : data357.Valid src357 dst357 Finset.univ := by decide +kernel

def src358 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst358 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle358_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle358_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle358_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle358_3 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle358_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle358_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data358 : PartitionData E W := ⟨6,![cycle358_0,cycle358_1,cycle358_2,cycle358_3,cycle358_4,cycle358_5]⟩
lemma valid_data358 : data358.Valid src358 dst358 Finset.univ := by decide +kernel

def src359 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst359 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle359_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle359_1 : CycleData E W := ⟨3,![1,14,12,19,7],![3,6,26,28,18]⟩
def cycle359_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle359_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle359_4 : CycleData E W := ⟨3,![4,10,11,15,9],![2,4,14,26,16]⟩
def cycle359_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data359 : PartitionData E W := ⟨6,![cycle359_0,cycle359_1,cycle359_2,cycle359_3,cycle359_4,cycle359_5]⟩
lemma valid_data359 : data359.Valid src359 dst359 Finset.univ := by decide +kernel

def src360 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst360 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle360_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle360_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle360_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle360_3 : CycleData E W := ⟨3,![3,18,19,11,10],![4,8,18,28,14]⟩
def cycle360_4 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle360_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data360 : PartitionData E W := ⟨6,![cycle360_0,cycle360_1,cycle360_2,cycle360_3,cycle360_4,cycle360_5]⟩
lemma valid_data360 : data360.Valid src360 dst360 Finset.univ := by decide +kernel

def src361 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst361 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle361_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle361_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle361_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle361_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle361_4 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle361_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data361 : PartitionData E W := ⟨6,![cycle361_0,cycle361_1,cycle361_2,cycle361_3,cycle361_4,cycle361_5]⟩
lemma valid_data361 : data361.Valid src361 dst361 Finset.univ := by decide +kernel

def src362 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst362 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle362_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle362_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle362_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle362_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle362_4 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle362_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data362 : PartitionData E W := ⟨6,![cycle362_0,cycle362_1,cycle362_2,cycle362_3,cycle362_4,cycle362_5]⟩
lemma valid_data362 : data362.Valid src362 dst362 Finset.univ := by decide +kernel

def src363 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst363 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle363_0 : CycleData E W := ⟨2,![0,1,14,9],![2,3,6,16]⟩
def cycle363_1 : CycleData E W := ⟨2,![3,2,17,13],![4,8,6,26]⟩
def cycle363_2 : CycleData E W := ⟨1,![4,10,5],![2,4,14]⟩
def cycle363_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle363_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle363_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data363 : PartitionData E W := ⟨6,![cycle363_0,cycle363_1,cycle363_2,cycle363_3,cycle363_4,cycle363_5]⟩
lemma valid_data363 : data363.Valid src363 dst363 Finset.univ := by decide +kernel

def src364 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst364 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle364_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle364_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle364_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle364_3 : CycleData E W := ⟨3,![4,13,17,14,9],![2,4,26,6,16]⟩
def cycle364_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle364_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data364 : PartitionData E W := ⟨6,![cycle364_0,cycle364_1,cycle364_2,cycle364_3,cycle364_4,cycle364_5]⟩
lemma valid_data364 : data364.Valid src364 dst364 Finset.univ := by decide +kernel

def src365 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst365 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle365_0 : CycleData E W := ⟨2,![0,1,14,9],![2,3,6,16]⟩
def cycle365_1 : CycleData E W := ⟨2,![3,2,17,13],![4,8,6,26]⟩
def cycle365_2 : CycleData E W := ⟨1,![4,10,5],![2,4,14]⟩
def cycle365_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle365_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle365_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data365 : PartitionData E W := ⟨6,![cycle365_0,cycle365_1,cycle365_2,cycle365_3,cycle365_4,cycle365_5]⟩
lemma valid_data365 : data365.Valid src365 dst365 Finset.univ := by decide +kernel

def src366 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst366 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle366_0 : CycleData E W := ⟨9,![0,1,17,16,8,18,3,13,12,11,5],![2,3,6,38,16,18,8,4,26,28,14]⟩
def cycle366_1 : CycleData E W := ⟨9,![4,10,6,7,19,20,21,2,14,15,9],![2,4,14,3,18,28,38,8,6,26,16]⟩
def data366 : PartitionData E W := ⟨2,![cycle366_0,cycle366_1]⟩
lemma valid_data366 : data366.Valid src366 dst366 Finset.univ := by decide +kernel

def src367 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst367 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle367_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle367_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle367_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle367_3 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle367_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle367_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data367 : PartitionData E W := ⟨6,![cycle367_0,cycle367_1,cycle367_2,cycle367_3,cycle367_4,cycle367_5]⟩
lemma valid_data367 : data367.Valid src367 dst367 Finset.univ := by decide +kernel

def src368 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst368 : E → W := ![3,6,8,4,2,14,3,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle368_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle368_1 : CycleData E W := ⟨3,![1,14,12,19,7],![3,6,26,28,18]⟩
def cycle368_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle368_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle368_4 : CycleData E W := ⟨2,![4,13,15,9],![2,4,26,16]⟩
def cycle368_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data368 : PartitionData E W := ⟨6,![cycle368_0,cycle368_1,cycle368_2,cycle368_3,cycle368_4,cycle368_5]⟩
lemma valid_data368 : data368.Valid src368 dst368 Finset.univ := by decide +kernel

def src369 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst369 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle369_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle369_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle369_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle369_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle369_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle369_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data369 : PartitionData E W := ⟨6,![cycle369_0,cycle369_1,cycle369_2,cycle369_3,cycle369_4,cycle369_5]⟩
lemma valid_data369 : data369.Valid src369 dst369 Finset.univ := by decide +kernel

def src370 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst370 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle370_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle370_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle370_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle370_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle370_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle370_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data370 : PartitionData E W := ⟨6,![cycle370_0,cycle370_1,cycle370_2,cycle370_3,cycle370_4,cycle370_5]⟩
lemma valid_data370 : data370.Valid src370 dst370 Finset.univ := by decide +kernel

def src371 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst371 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle371_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle371_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle371_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle371_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle371_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle371_5 : CycleData E W := ⟨3,![11,16,20,19,12],![14,26,38,18,28]⟩
def data371 : PartitionData E W := ⟨6,![cycle371_0,cycle371_1,cycle371_2,cycle371_3,cycle371_4,cycle371_5]⟩
lemma valid_data371 : data371.Valid src371 dst371 Finset.univ := by decide +kernel

def src372 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst372 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle372_0 : CycleData E W := ⟨9,![0,1,2,18,8,15,16,10,13,12,5],![2,3,6,8,18,16,38,26,4,28,14]⟩
def cycle372_1 : CycleData E W := ⟨9,![4,3,21,20,19,7,6,11,17,14,9],![2,4,8,38,28,18,3,14,26,6,16]⟩
def data372 : PartitionData E W := ⟨2,![cycle372_0,cycle372_1]⟩
lemma valid_data372 : data372.Valid src372 dst372 Finset.univ := by decide +kernel

def src373 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst373 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle373_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle373_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle373_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle373_3 : CycleData E W := ⟨3,![4,10,17,14,9],![2,4,26,6,16]⟩
def cycle373_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle373_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data373 : PartitionData E W := ⟨6,![cycle373_0,cycle373_1,cycle373_2,cycle373_3,cycle373_4,cycle373_5]⟩
lemma valid_data373 : data373.Valid src373 dst373 Finset.univ := by decide +kernel

def src374 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst374 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle374_0 : CycleData E W := ⟨2,![0,1,14,9],![2,3,6,16]⟩
def cycle374_1 : CycleData E W := ⟨2,![2,21,16,17],![6,8,38,26]⟩
def cycle374_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle374_3 : CycleData E W := ⟨2,![4,10,11,5],![2,4,26,14]⟩
def cycle374_4 : CycleData E W := ⟨2,![6,12,19,7],![3,14,28,18]⟩
def cycle374_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data374 : PartitionData E W := ⟨6,![cycle374_0,cycle374_1,cycle374_2,cycle374_3,cycle374_4,cycle374_5]⟩
lemma valid_data374 : data374.Valid src374 dst374 Finset.univ := by decide +kernel

def src375 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst375 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle375_0 : CycleData E W := ⟨9,![0,7,18,3,13,12,11,14,17,16,9],![2,3,18,8,4,28,14,26,6,38,16]⟩
def cycle375_1 : CycleData E W := ⟨9,![4,10,15,8,19,20,21,2,1,6,5],![2,4,26,16,18,28,38,8,6,3,14]⟩
def data375 : PartitionData E W := ⟨2,![cycle375_0,cycle375_1]⟩
lemma valid_data375 : data375.Valid src375 dst375 Finset.univ := by decide +kernel

def src376 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst376 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle376_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle376_1 : CycleData E W := ⟨2,![1,2,18,7],![3,6,8,18]⟩
def cycle376_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle376_3 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle376_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle376_5 : CycleData E W := ⟨3,![14,11,12,20,17],![6,26,14,28,38]⟩
def data376 : PartitionData E W := ⟨6,![cycle376_0,cycle376_1,cycle376_2,cycle376_3,cycle376_4,cycle376_5]⟩
lemma valid_data376 : data376.Valid src376 dst376 Finset.univ := by decide +kernel

def src377 : E → W := ![2,3,6,8,4,2,14,3,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst377 : E → W := ![3,6,8,4,2,14,3,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle377_0 : CycleData E W := ⟨1,![0,6,5],![2,3,14]⟩
def cycle377_1 : CycleData E W := ⟨4,![1,14,11,12,19,7],![3,6,26,14,28,18]⟩
def cycle377_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle377_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle377_4 : CycleData E W := ⟨2,![4,10,15,9],![2,4,26,16]⟩
def cycle377_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data377 : PartitionData E W := ⟨6,![cycle377_0,cycle377_1,cycle377_2,cycle377_3,cycle377_4,cycle377_5]⟩
lemma valid_data377 : data377.Valid src377 dst377 Finset.univ := by decide +kernel

def src378 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst378 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle378_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle378_1 : CycleData E W := ⟨3,![1,14,15,11,7],![3,6,16,26,14]⟩
def cycle378_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle378_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle378_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle378_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data378 : PartitionData E W := ⟨6,![cycle378_0,cycle378_1,cycle378_2,cycle378_3,cycle378_4,cycle378_5]⟩
lemma valid_data378 : data378.Valid src378 dst378 Finset.univ := by decide +kernel

def src379 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst379 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle379_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle379_1 : CycleData E W := ⟨3,![1,14,15,11,7],![3,6,16,26,14]⟩
def cycle379_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle379_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle379_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle379_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data379 : PartitionData E W := ⟨6,![cycle379_0,cycle379_1,cycle379_2,cycle379_3,cycle379_4,cycle379_5]⟩
lemma valid_data379 : data379.Valid src379 dst379 Finset.univ := by decide +kernel

def src380 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst380 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle380_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle380_1 : CycleData E W := ⟨3,![1,14,15,11,7],![3,6,16,26,14]⟩
def cycle380_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle380_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle380_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle380_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data380 : PartitionData E W := ⟨6,![cycle380_0,cycle380_1,cycle380_2,cycle380_3,cycle380_4,cycle380_5]⟩
lemma valid_data380 : data380.Valid src380 dst380 Finset.univ := by decide +kernel

def src381 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst381 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle381_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle381_1 : CycleData E W := ⟨2,![1,17,11,7],![3,6,26,14]⟩
def cycle381_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle381_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle381_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle381_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data381 : PartitionData E W := ⟨6,![cycle381_0,cycle381_1,cycle381_2,cycle381_3,cycle381_4,cycle381_5]⟩
lemma valid_data381 : data381.Valid src381 dst381 Finset.univ := by decide +kernel

def src382 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst382 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle382_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle382_1 : CycleData E W := ⟨2,![1,17,11,7],![3,6,26,14]⟩
def cycle382_2 : CycleData E W := ⟨3,![2,18,19,15,14],![6,8,18,38,16]⟩
def cycle382_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle382_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle382_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data382 : PartitionData E W := ⟨6,![cycle382_0,cycle382_1,cycle382_2,cycle382_3,cycle382_4,cycle382_5]⟩
lemma valid_data382 : data382.Valid src382 dst382 Finset.univ := by decide +kernel

def src383 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst383 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle383_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle383_1 : CycleData E W := ⟨2,![1,17,11,7],![3,6,26,14]⟩
def cycle383_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle383_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle383_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle383_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data383 : PartitionData E W := ⟨6,![cycle383_0,cycle383_1,cycle383_2,cycle383_3,cycle383_4,cycle383_5]⟩
lemma valid_data383 : data383.Valid src383 dst383 Finset.univ := by decide +kernel

def src384 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst384 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle384_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle384_1 : CycleData E W := ⟨2,![1,14,11,7],![3,6,26,14]⟩
def cycle384_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle384_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle384_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle384_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data384 : PartitionData E W := ⟨6,![cycle384_0,cycle384_1,cycle384_2,cycle384_3,cycle384_4,cycle384_5]⟩
lemma valid_data384 : data384.Valid src384 dst384 Finset.univ := by decide +kernel

def src385 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst385 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle385_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle385_1 : CycleData E W := ⟨2,![1,14,11,7],![3,6,26,14]⟩
def cycle385_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle385_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle385_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle385_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data385 : PartitionData E W := ⟨6,![cycle385_0,cycle385_1,cycle385_2,cycle385_3,cycle385_4,cycle385_5]⟩
lemma valid_data385 : data385.Valid src385 dst385 Finset.univ := by decide +kernel

def src386 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst386 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle386_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle386_1 : CycleData E W := ⟨2,![1,14,11,7],![3,6,26,14]⟩
def cycle386_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle386_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle386_4 : CycleData E W := ⟨2,![4,10,8,9],![2,4,14,18]⟩
def cycle386_5 : CycleData E W := ⟨3,![15,12,19,20,16],![16,26,28,18,38]⟩
def data386 : PartitionData E W := ⟨6,![cycle386_0,cycle386_1,cycle386_2,cycle386_3,cycle386_4,cycle386_5]⟩
lemma valid_data386 : data386.Valid src386 dst386 Finset.univ := by decide +kernel

def src387 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst387 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle387_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle387_1 : CycleData E W := ⟨4,![1,14,15,13,10,7],![3,6,16,26,4,14]⟩
def cycle387_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle387_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle387_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle387_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data387 : PartitionData E W := ⟨6,![cycle387_0,cycle387_1,cycle387_2,cycle387_3,cycle387_4,cycle387_5]⟩
lemma valid_data387 : data387.Valid src387 dst387 Finset.univ := by decide +kernel

def src388 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst388 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle388_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,14,18]⟩
def cycle388_1 : CycleData E W := ⟨1,![1,14,6],![3,6,16]⟩
def cycle388_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle388_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle388_4 : CycleData E W := ⟨2,![4,13,15,5],![2,4,26,16]⟩
def cycle388_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data388 : PartitionData E W := ⟨6,![cycle388_0,cycle388_1,cycle388_2,cycle388_3,cycle388_4,cycle388_5]⟩
lemma valid_data388 : data388.Valid src388 dst388 Finset.univ := by decide +kernel

def src389 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst389 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle389_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,14,18]⟩
def cycle389_1 : CycleData E W := ⟨1,![1,14,6],![3,6,16]⟩
def cycle389_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle389_3 : CycleData E W := ⟨2,![3,18,11,10],![4,8,28,14]⟩
def cycle389_4 : CycleData E W := ⟨2,![4,13,15,5],![2,4,26,16]⟩
def cycle389_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data389 : PartitionData E W := ⟨6,![cycle389_0,cycle389_1,cycle389_2,cycle389_3,cycle389_4,cycle389_5]⟩
lemma valid_data389 : data389.Valid src389 dst389 Finset.univ := by decide +kernel

def src390 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst390 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle390_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle390_1 : CycleData E W := ⟨3,![1,17,13,10,7],![3,6,26,4,14]⟩
def cycle390_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle390_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle390_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle390_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data390 : PartitionData E W := ⟨6,![cycle390_0,cycle390_1,cycle390_2,cycle390_3,cycle390_4,cycle390_5]⟩
lemma valid_data390 : data390.Valid src390 dst390 Finset.univ := by decide +kernel

def src391 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst391 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle391_0 : CycleData E W := ⟨2,![0,7,10,4],![2,3,14,4]⟩
def cycle391_1 : CycleData E W := ⟨1,![1,14,6],![3,6,16]⟩
def cycle391_2 : CycleData E W := ⟨2,![3,2,17,13],![4,8,6,26]⟩
def cycle391_3 : CycleData E W := ⟨2,![5,15,19,9],![2,16,38,18]⟩
def cycle391_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle391_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data391 : PartitionData E W := ⟨6,![cycle391_0,cycle391_1,cycle391_2,cycle391_3,cycle391_4,cycle391_5]⟩
lemma valid_data391 : data391.Valid src391 dst391 Finset.univ := by decide +kernel

def src392 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst392 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle392_0 : CycleData E W := ⟨2,![0,7,10,4],![2,3,14,4]⟩
def cycle392_1 : CycleData E W := ⟨1,![1,14,6],![3,6,16]⟩
def cycle392_2 : CycleData E W := ⟨2,![3,2,17,13],![4,8,6,26]⟩
def cycle392_3 : CycleData E W := ⟨2,![5,15,20,9],![2,16,38,18]⟩
def cycle392_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle392_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data392 : PartitionData E W := ⟨6,![cycle392_0,cycle392_1,cycle392_2,cycle392_3,cycle392_4,cycle392_5]⟩
lemma valid_data392 : data392.Valid src392 dst392 Finset.univ := by decide +kernel

def src393 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst393 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle393_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle393_1 : CycleData E W := ⟨3,![1,14,13,10,7],![3,6,26,4,14]⟩
def cycle393_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle393_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle393_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle393_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data393 : PartitionData E W := ⟨6,![cycle393_0,cycle393_1,cycle393_2,cycle393_3,cycle393_4,cycle393_5]⟩
lemma valid_data393 : data393.Valid src393 dst393 Finset.univ := by decide +kernel

def src394 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst394 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle394_0 : CycleData E W := ⟨9,![0,6,16,17,2,18,8,11,12,13,4],![2,3,16,38,6,8,18,14,28,26,4]⟩
def cycle394_1 : CycleData E W := ⟨9,![5,15,14,1,7,10,3,21,20,19,9],![2,16,26,6,3,14,4,8,28,38,18]⟩
def data394 : PartitionData E W := ⟨2,![cycle394_0,cycle394_1]⟩
lemma valid_data394 : data394.Valid src394 dst394 Finset.univ := by decide +kernel

def src395 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst395 : E → W := ![3,6,8,4,2,16,3,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle395_0 : CycleData E W := ⟨2,![0,7,10,4],![2,3,14,4]⟩
def cycle395_1 : CycleData E W := ⟨2,![1,14,15,6],![3,6,26,16]⟩
def cycle395_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle395_3 : CycleData E W := ⟨2,![3,18,12,13],![4,8,28,26]⟩
def cycle395_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle395_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data395 : PartitionData E W := ⟨6,![cycle395_0,cycle395_1,cycle395_2,cycle395_3,cycle395_4,cycle395_5]⟩
lemma valid_data395 : data395.Valid src395 dst395 Finset.univ := by decide +kernel

def src396 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst396 : E → W := ![3,6,8,4,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle396_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle396_1 : CycleData E W := ⟨3,![1,14,15,11,7],![3,6,16,26,14]⟩
def cycle396_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle396_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle396_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle396_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data396 : PartitionData E W := ⟨6,![cycle396_0,cycle396_1,cycle396_2,cycle396_3,cycle396_4,cycle396_5]⟩
lemma valid_data396 : data396.Valid src396 dst396 Finset.univ := by decide +kernel

def src397 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst397 : E → W := ![3,6,8,4,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle397_0 : CycleData E W := ⟨2,![0,7,8,9],![2,3,14,18]⟩
def cycle397_1 : CycleData E W := ⟨1,![1,14,6],![3,6,16]⟩
def cycle397_2 : CycleData E W := ⟨2,![2,18,19,17],![6,8,18,38]⟩
def cycle397_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle397_4 : CycleData E W := ⟨2,![4,10,15,5],![2,4,26,16]⟩
def cycle397_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data397 : PartitionData E W := ⟨6,![cycle397_0,cycle397_1,cycle397_2,cycle397_3,cycle397_4,cycle397_5]⟩
lemma valid_data397 : data397.Valid src397 dst397 Finset.univ := by decide +kernel

def src398 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst398 : E → W := ![3,6,8,4,2,16,3,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle398_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle398_1 : CycleData E W := ⟨3,![1,14,15,11,7],![3,6,16,26,14]⟩
def cycle398_2 : CycleData E W := ⟨1,![2,21,17],![6,8,38]⟩
def cycle398_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle398_4 : CycleData E W := ⟨3,![4,10,16,20,9],![2,4,26,38,18]⟩
def cycle398_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data398 : PartitionData E W := ⟨6,![cycle398_0,cycle398_1,cycle398_2,cycle398_3,cycle398_4,cycle398_5]⟩
lemma valid_data398 : data398.Valid src398 dst398 Finset.univ := by decide +kernel

def src399 : E → W := ![2,3,6,8,4,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst399 : E → W := ![3,6,8,4,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle399_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle399_1 : CycleData E W := ⟨2,![1,17,11,7],![3,6,26,14]⟩
def cycle399_2 : CycleData E W := ⟨2,![2,21,15,14],![6,8,38,16]⟩
def cycle399_3 : CycleData E W := ⟨2,![4,3,18,9],![2,4,8,18]⟩
def cycle399_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle399_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data399 : PartitionData E W := ⟨6,![cycle399_0,cycle399_1,cycle399_2,cycle399_3,cycle399_4,cycle399_5]⟩
lemma valid_data399 : data399.Valid src399 dst399 Finset.univ := by decide +kernel

def lookupB1 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data200 else (if j < 2 then data201 else data202)) else (if j < 4 then data203 else (if j < 5 then data204 else data205))) else (if j < 9 then (if j < 7 then data206 else (if j < 8 then data207 else data208)) else (if j < 10 then data209 else (if j < 11 then data210 else data211)))) else (if j < 18 then (if j < 15 then (if j < 13 then data212 else (if j < 14 then data213 else data214)) else (if j < 16 then data215 else (if j < 17 then data216 else data217))) else (if j < 21 then (if j < 19 then data218 else (if j < 20 then data219 else data220)) else (if j < 23 then (if j < 22 then data221 else data222) else (if j < 24 then data223 else data224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data225 else (if j < 27 then data226 else data227)) else (if j < 29 then data228 else (if j < 30 then data229 else data230))) else (if j < 34 then (if j < 32 then data231 else (if j < 33 then data232 else data233)) else (if j < 35 then data234 else (if j < 36 then data235 else data236)))) else (if j < 43 then (if j < 40 then (if j < 38 then data237 else (if j < 39 then data238 else data239)) else (if j < 41 then data240 else (if j < 42 then data241 else data242))) else (if j < 46 then (if j < 44 then data243 else (if j < 45 then data244 else data245)) else (if j < 48 then (if j < 47 then data246 else data247) else (if j < 49 then data248 else data249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data250 else (if j < 52 then data251 else data252)) else (if j < 54 then data253 else (if j < 55 then data254 else data255))) else (if j < 59 then (if j < 57 then data256 else (if j < 58 then data257 else data258)) else (if j < 60 then data259 else (if j < 61 then data260 else data261)))) else (if j < 68 then (if j < 65 then (if j < 63 then data262 else (if j < 64 then data263 else data264)) else (if j < 66 then data265 else (if j < 67 then data266 else data267))) else (if j < 71 then (if j < 69 then data268 else (if j < 70 then data269 else data270)) else (if j < 73 then (if j < 72 then data271 else data272) else (if j < 74 then data273 else data274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data275 else (if j < 77 then data276 else data277)) else (if j < 79 then data278 else (if j < 80 then data279 else data280))) else (if j < 84 then (if j < 82 then data281 else (if j < 83 then data282 else data283)) else (if j < 85 then data284 else (if j < 86 then data285 else data286)))) else (if j < 93 then (if j < 90 then (if j < 88 then data287 else (if j < 89 then data288 else data289)) else (if j < 91 then data290 else (if j < 92 then data291 else data292))) else (if j < 96 then (if j < 94 then data293 else (if j < 95 then data294 else data295)) else (if j < 98 then (if j < 97 then data296 else data297) else (if j < 99 then data298 else data299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data300 else (if j < 102 then data301 else data302)) else (if j < 104 then data303 else (if j < 105 then data304 else data305))) else (if j < 109 then (if j < 107 then data306 else (if j < 108 then data307 else data308)) else (if j < 110 then data309 else (if j < 111 then data310 else data311)))) else (if j < 118 then (if j < 115 then (if j < 113 then data312 else (if j < 114 then data313 else data314)) else (if j < 116 then data315 else (if j < 117 then data316 else data317))) else (if j < 121 then (if j < 119 then data318 else (if j < 120 then data319 else data320)) else (if j < 123 then (if j < 122 then data321 else data322) else (if j < 124 then data323 else data324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data325 else (if j < 127 then data326 else data327)) else (if j < 129 then data328 else (if j < 130 then data329 else data330))) else (if j < 134 then (if j < 132 then data331 else (if j < 133 then data332 else data333)) else (if j < 135 then data334 else (if j < 136 then data335 else data336)))) else (if j < 143 then (if j < 140 then (if j < 138 then data337 else (if j < 139 then data338 else data339)) else (if j < 141 then data340 else (if j < 142 then data341 else data342))) else (if j < 146 then (if j < 144 then data343 else (if j < 145 then data344 else data345)) else (if j < 148 then (if j < 147 then data346 else data347) else (if j < 149 then data348 else data349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data350 else (if j < 152 then data351 else data352)) else (if j < 154 then data353 else (if j < 155 then data354 else data355))) else (if j < 159 then (if j < 157 then data356 else (if j < 158 then data357 else data358)) else (if j < 160 then data359 else (if j < 161 then data360 else data361)))) else (if j < 168 then (if j < 165 then (if j < 163 then data362 else (if j < 164 then data363 else data364)) else (if j < 166 then data365 else (if j < 167 then data366 else data367))) else (if j < 171 then (if j < 169 then data368 else (if j < 170 then data369 else data370)) else (if j < 173 then (if j < 172 then data371 else data372) else (if j < 174 then data373 else data374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data375 else (if j < 177 then data376 else data377)) else (if j < 179 then data378 else (if j < 180 then data379 else data380))) else (if j < 184 then (if j < 182 then data381 else (if j < 183 then data382 else data383)) else (if j < 185 then data384 else (if j < 186 then data385 else data386)))) else (if j < 193 then (if j < 190 then (if j < 188 then data387 else (if j < 189 then data388 else data389)) else (if j < 191 then data390 else (if j < 192 then data391 else data392))) else (if j < 196 then (if j < 194 then data393 else (if j < 195 then data394 else data395)) else (if j < 198 then (if j < 197 then data396 else data397) else (if j < 199 then data398 else data399))))))))

def srcTableB1 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src200 else (if j < 2 then src201 else src202)) else (if j < 4 then src203 else (if j < 5 then src204 else src205))) else (if j < 9 then (if j < 7 then src206 else (if j < 8 then src207 else src208)) else (if j < 10 then src209 else (if j < 11 then src210 else src211)))) else (if j < 18 then (if j < 15 then (if j < 13 then src212 else (if j < 14 then src213 else src214)) else (if j < 16 then src215 else (if j < 17 then src216 else src217))) else (if j < 21 then (if j < 19 then src218 else (if j < 20 then src219 else src220)) else (if j < 23 then (if j < 22 then src221 else src222) else (if j < 24 then src223 else src224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src225 else (if j < 27 then src226 else src227)) else (if j < 29 then src228 else (if j < 30 then src229 else src230))) else (if j < 34 then (if j < 32 then src231 else (if j < 33 then src232 else src233)) else (if j < 35 then src234 else (if j < 36 then src235 else src236)))) else (if j < 43 then (if j < 40 then (if j < 38 then src237 else (if j < 39 then src238 else src239)) else (if j < 41 then src240 else (if j < 42 then src241 else src242))) else (if j < 46 then (if j < 44 then src243 else (if j < 45 then src244 else src245)) else (if j < 48 then (if j < 47 then src246 else src247) else (if j < 49 then src248 else src249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src250 else (if j < 52 then src251 else src252)) else (if j < 54 then src253 else (if j < 55 then src254 else src255))) else (if j < 59 then (if j < 57 then src256 else (if j < 58 then src257 else src258)) else (if j < 60 then src259 else (if j < 61 then src260 else src261)))) else (if j < 68 then (if j < 65 then (if j < 63 then src262 else (if j < 64 then src263 else src264)) else (if j < 66 then src265 else (if j < 67 then src266 else src267))) else (if j < 71 then (if j < 69 then src268 else (if j < 70 then src269 else src270)) else (if j < 73 then (if j < 72 then src271 else src272) else (if j < 74 then src273 else src274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src275 else (if j < 77 then src276 else src277)) else (if j < 79 then src278 else (if j < 80 then src279 else src280))) else (if j < 84 then (if j < 82 then src281 else (if j < 83 then src282 else src283)) else (if j < 85 then src284 else (if j < 86 then src285 else src286)))) else (if j < 93 then (if j < 90 then (if j < 88 then src287 else (if j < 89 then src288 else src289)) else (if j < 91 then src290 else (if j < 92 then src291 else src292))) else (if j < 96 then (if j < 94 then src293 else (if j < 95 then src294 else src295)) else (if j < 98 then (if j < 97 then src296 else src297) else (if j < 99 then src298 else src299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src300 else (if j < 102 then src301 else src302)) else (if j < 104 then src303 else (if j < 105 then src304 else src305))) else (if j < 109 then (if j < 107 then src306 else (if j < 108 then src307 else src308)) else (if j < 110 then src309 else (if j < 111 then src310 else src311)))) else (if j < 118 then (if j < 115 then (if j < 113 then src312 else (if j < 114 then src313 else src314)) else (if j < 116 then src315 else (if j < 117 then src316 else src317))) else (if j < 121 then (if j < 119 then src318 else (if j < 120 then src319 else src320)) else (if j < 123 then (if j < 122 then src321 else src322) else (if j < 124 then src323 else src324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src325 else (if j < 127 then src326 else src327)) else (if j < 129 then src328 else (if j < 130 then src329 else src330))) else (if j < 134 then (if j < 132 then src331 else (if j < 133 then src332 else src333)) else (if j < 135 then src334 else (if j < 136 then src335 else src336)))) else (if j < 143 then (if j < 140 then (if j < 138 then src337 else (if j < 139 then src338 else src339)) else (if j < 141 then src340 else (if j < 142 then src341 else src342))) else (if j < 146 then (if j < 144 then src343 else (if j < 145 then src344 else src345)) else (if j < 148 then (if j < 147 then src346 else src347) else (if j < 149 then src348 else src349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src350 else (if j < 152 then src351 else src352)) else (if j < 154 then src353 else (if j < 155 then src354 else src355))) else (if j < 159 then (if j < 157 then src356 else (if j < 158 then src357 else src358)) else (if j < 160 then src359 else (if j < 161 then src360 else src361)))) else (if j < 168 then (if j < 165 then (if j < 163 then src362 else (if j < 164 then src363 else src364)) else (if j < 166 then src365 else (if j < 167 then src366 else src367))) else (if j < 171 then (if j < 169 then src368 else (if j < 170 then src369 else src370)) else (if j < 173 then (if j < 172 then src371 else src372) else (if j < 174 then src373 else src374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src375 else (if j < 177 then src376 else src377)) else (if j < 179 then src378 else (if j < 180 then src379 else src380))) else (if j < 184 then (if j < 182 then src381 else (if j < 183 then src382 else src383)) else (if j < 185 then src384 else (if j < 186 then src385 else src386)))) else (if j < 193 then (if j < 190 then (if j < 188 then src387 else (if j < 189 then src388 else src389)) else (if j < 191 then src390 else (if j < 192 then src391 else src392))) else (if j < 196 then (if j < 194 then src393 else (if j < 195 then src394 else src395)) else (if j < 198 then (if j < 197 then src396 else src397) else (if j < 199 then src398 else src399))))))))

def dstTableB1 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst200 else (if j < 2 then dst201 else dst202)) else (if j < 4 then dst203 else (if j < 5 then dst204 else dst205))) else (if j < 9 then (if j < 7 then dst206 else (if j < 8 then dst207 else dst208)) else (if j < 10 then dst209 else (if j < 11 then dst210 else dst211)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst212 else (if j < 14 then dst213 else dst214)) else (if j < 16 then dst215 else (if j < 17 then dst216 else dst217))) else (if j < 21 then (if j < 19 then dst218 else (if j < 20 then dst219 else dst220)) else (if j < 23 then (if j < 22 then dst221 else dst222) else (if j < 24 then dst223 else dst224))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst225 else (if j < 27 then dst226 else dst227)) else (if j < 29 then dst228 else (if j < 30 then dst229 else dst230))) else (if j < 34 then (if j < 32 then dst231 else (if j < 33 then dst232 else dst233)) else (if j < 35 then dst234 else (if j < 36 then dst235 else dst236)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst237 else (if j < 39 then dst238 else dst239)) else (if j < 41 then dst240 else (if j < 42 then dst241 else dst242))) else (if j < 46 then (if j < 44 then dst243 else (if j < 45 then dst244 else dst245)) else (if j < 48 then (if j < 47 then dst246 else dst247) else (if j < 49 then dst248 else dst249)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst250 else (if j < 52 then dst251 else dst252)) else (if j < 54 then dst253 else (if j < 55 then dst254 else dst255))) else (if j < 59 then (if j < 57 then dst256 else (if j < 58 then dst257 else dst258)) else (if j < 60 then dst259 else (if j < 61 then dst260 else dst261)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst262 else (if j < 64 then dst263 else dst264)) else (if j < 66 then dst265 else (if j < 67 then dst266 else dst267))) else (if j < 71 then (if j < 69 then dst268 else (if j < 70 then dst269 else dst270)) else (if j < 73 then (if j < 72 then dst271 else dst272) else (if j < 74 then dst273 else dst274))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst275 else (if j < 77 then dst276 else dst277)) else (if j < 79 then dst278 else (if j < 80 then dst279 else dst280))) else (if j < 84 then (if j < 82 then dst281 else (if j < 83 then dst282 else dst283)) else (if j < 85 then dst284 else (if j < 86 then dst285 else dst286)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst287 else (if j < 89 then dst288 else dst289)) else (if j < 91 then dst290 else (if j < 92 then dst291 else dst292))) else (if j < 96 then (if j < 94 then dst293 else (if j < 95 then dst294 else dst295)) else (if j < 98 then (if j < 97 then dst296 else dst297) else (if j < 99 then dst298 else dst299))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst300 else (if j < 102 then dst301 else dst302)) else (if j < 104 then dst303 else (if j < 105 then dst304 else dst305))) else (if j < 109 then (if j < 107 then dst306 else (if j < 108 then dst307 else dst308)) else (if j < 110 then dst309 else (if j < 111 then dst310 else dst311)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst312 else (if j < 114 then dst313 else dst314)) else (if j < 116 then dst315 else (if j < 117 then dst316 else dst317))) else (if j < 121 then (if j < 119 then dst318 else (if j < 120 then dst319 else dst320)) else (if j < 123 then (if j < 122 then dst321 else dst322) else (if j < 124 then dst323 else dst324))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst325 else (if j < 127 then dst326 else dst327)) else (if j < 129 then dst328 else (if j < 130 then dst329 else dst330))) else (if j < 134 then (if j < 132 then dst331 else (if j < 133 then dst332 else dst333)) else (if j < 135 then dst334 else (if j < 136 then dst335 else dst336)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst337 else (if j < 139 then dst338 else dst339)) else (if j < 141 then dst340 else (if j < 142 then dst341 else dst342))) else (if j < 146 then (if j < 144 then dst343 else (if j < 145 then dst344 else dst345)) else (if j < 148 then (if j < 147 then dst346 else dst347) else (if j < 149 then dst348 else dst349)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst350 else (if j < 152 then dst351 else dst352)) else (if j < 154 then dst353 else (if j < 155 then dst354 else dst355))) else (if j < 159 then (if j < 157 then dst356 else (if j < 158 then dst357 else dst358)) else (if j < 160 then dst359 else (if j < 161 then dst360 else dst361)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst362 else (if j < 164 then dst363 else dst364)) else (if j < 166 then dst365 else (if j < 167 then dst366 else dst367))) else (if j < 171 then (if j < 169 then dst368 else (if j < 170 then dst369 else dst370)) else (if j < 173 then (if j < 172 then dst371 else dst372) else (if j < 174 then dst373 else dst374))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst375 else (if j < 177 then dst376 else dst377)) else (if j < 179 then dst378 else (if j < 180 then dst379 else dst380))) else (if j < 184 then (if j < 182 then dst381 else (if j < 183 then dst382 else dst383)) else (if j < 185 then dst384 else (if j < 186 then dst385 else dst386)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst387 else (if j < 189 then dst388 else dst389)) else (if j < 191 then dst390 else (if j < 192 then dst391 else dst392))) else (if j < 196 then (if j < 194 then dst393 else (if j < 195 then dst394 else dst395)) else (if j < 198 then (if j < 197 then dst396 else dst397) else (if j < 199 then dst398 else dst399))))))))

def caseB1 (i : Fin 200) : Cases := ⟨200 + i.val,by have := i.isLt; omega⟩
lemma tableB1_valid (i : Fin 200) :
    (lookupB1 i.val).Valid (srcTableB1 i.val) (dstTableB1 i.val) Finset.univ := by
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
  · exact valid_data250
  · exact valid_data251
  · exact valid_data252
  · exact valid_data253
  · exact valid_data254
  · exact valid_data255
  · exact valid_data256
  · exact valid_data257
  · exact valid_data258
  · exact valid_data259
  · exact valid_data260
  · exact valid_data261
  · exact valid_data262
  · exact valid_data263
  · exact valid_data264
  · exact valid_data265
  · exact valid_data266
  · exact valid_data267
  · exact valid_data268
  · exact valid_data269
  · exact valid_data270
  · exact valid_data271
  · exact valid_data272
  · exact valid_data273
  · exact valid_data274
  · exact valid_data275
  · exact valid_data276
  · exact valid_data277
  · exact valid_data278
  · exact valid_data279
  · exact valid_data280
  · exact valid_data281
  · exact valid_data282
  · exact valid_data283
  · exact valid_data284
  · exact valid_data285
  · exact valid_data286
  · exact valid_data287
  · exact valid_data288
  · exact valid_data289
  · exact valid_data290
  · exact valid_data291
  · exact valid_data292
  · exact valid_data293
  · exact valid_data294
  · exact valid_data295
  · exact valid_data296
  · exact valid_data297
  · exact valid_data298
  · exact valid_data299
  · exact valid_data300
  · exact valid_data301
  · exact valid_data302
  · exact valid_data303
  · exact valid_data304
  · exact valid_data305
  · exact valid_data306
  · exact valid_data307
  · exact valid_data308
  · exact valid_data309
  · exact valid_data310
  · exact valid_data311
  · exact valid_data312
  · exact valid_data313
  · exact valid_data314
  · exact valid_data315
  · exact valid_data316
  · exact valid_data317
  · exact valid_data318
  · exact valid_data319
  · exact valid_data320
  · exact valid_data321
  · exact valid_data322
  · exact valid_data323
  · exact valid_data324
  · exact valid_data325
  · exact valid_data326
  · exact valid_data327
  · exact valid_data328
  · exact valid_data329
  · exact valid_data330
  · exact valid_data331
  · exact valid_data332
  · exact valid_data333
  · exact valid_data334
  · exact valid_data335
  · exact valid_data336
  · exact valid_data337
  · exact valid_data338
  · exact valid_data339
  · exact valid_data340
  · exact valid_data341
  · exact valid_data342
  · exact valid_data343
  · exact valid_data344
  · exact valid_data345
  · exact valid_data346
  · exact valid_data347
  · exact valid_data348
  · exact valid_data349
  · exact valid_data350
  · exact valid_data351
  · exact valid_data352
  · exact valid_data353
  · exact valid_data354
  · exact valid_data355
  · exact valid_data356
  · exact valid_data357
  · exact valid_data358
  · exact valid_data359
  · exact valid_data360
  · exact valid_data361
  · exact valid_data362
  · exact valid_data363
  · exact valid_data364
  · exact valid_data365
  · exact valid_data366
  · exact valid_data367
  · exact valid_data368
  · exact valid_data369
  · exact valid_data370
  · exact valid_data371
  · exact valid_data372
  · exact valid_data373
  · exact valid_data374
  · exact valid_data375
  · exact valid_data376
  · exact valid_data377
  · exact valid_data378
  · exact valid_data379
  · exact valid_data380
  · exact valid_data381
  · exact valid_data382
  · exact valid_data383
  · exact valid_data384
  · exact valid_data385
  · exact valid_data386
  · exact valid_data387
  · exact valid_data388
  · exact valid_data389
  · exact valid_data390
  · exact valid_data391
  · exact valid_data392
  · exact valid_data393
  · exact valid_data394
  · exact valid_data395
  · exact valid_data396
  · exact valid_data397
  · exact valid_data398
  · exact valid_data399

lemma srcB1_row : ∀ (i : Fin 200) (e : E),
    srcTableB1 i.val e = caseSource (caseB1 i) e := by decide +kernel

lemma dstB1_row : ∀ (i : Fin 200) (e : E),
    dstTableB1 i.val e = caseTarget (caseB1 i) e := by decide +kernel

lemma sizeB1 : ∀ i : Fin 200, (lookupB1 i.val).size ≤ 5 →
    (lookupB1 i.val).size = 2 ∧
      (⟨caseKey (caseB1 i),caseKey_lt (caseB1 i)⟩ : Fin 3888) ∈ good := by decide +kernel
lemma certificateB1 (i : Fin 200) : Certificate (caseB1 i) := by
  refine ⟨lookupB1 i.val,?_,sizeB1 i⟩
  have hv := tableB1_valid i
  rw [funext (srcB1_row i),funext (dstB1_row i)] at hv
  exact hv
lemma certificateInterval1 : FiniteIntervals.Covers CertificateAt 200 400 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 200 200 (fun i _ => certificateB1 i)
#print axioms certificateInterval1
end Erdos184Work.FiveRows1

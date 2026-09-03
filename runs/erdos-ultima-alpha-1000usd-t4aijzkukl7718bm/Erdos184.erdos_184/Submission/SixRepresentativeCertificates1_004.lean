import Submission.SixRepresentativeCertificates1Base
namespace Erdos184Work.SixRepresentativeCertificates1
open PureSixRowModel1 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src200 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,32,58,44,10,34,58,22,46]
def dst200 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle200_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle200_1 : CycleData E W := ⟨4,![1,16,27,4,3,2],![3,4,34,10,8,6]⟩
def cycle200_2 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle200_3 : CycleData E W := ⟨3,![17,14,7,30,21],![6,30,16,22,46]⟩
def cycle200_4 : CycleData E W := ⟨3,![8,29,24,23,9],![3,22,58,32,20]⟩
def cycle200_5 : CycleData E W := ⟨2,![22,10,19,26],![8,20,18,44]⟩
def cycle200_6 : CycleData E W := ⟨2,![15,28,25,18],![30,34,58,44]⟩
def data200 : PartitionData E W := ⟨7,![cycle200_0,cycle200_1,cycle200_2,cycle200_3,cycle200_4,cycle200_5,cycle200_6]⟩
lemma valid200 : data200.Valid src200 dst200 Finset.univ := by decide +kernel
lemma src_eq200 : src200 = src (unkey (representativeKey 200)) := by decide +kernel
lemma dst_eq200 : dst200 = dst (unkey (representativeKey 200)) := by decide +kernel
lemma certificate200 : Certificate 200 := by
  refine ⟨data200,?_,?_⟩
  · rw [← src_eq200,← dst_eq200]
    exact valid200
  · decide +kernel

def src201 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,32,44,10,22,34,58,46]
def dst201 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,32,44,8,22,34,58,46,10]
def cycle201_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle201_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle201_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle201_3 : CycleData E W := ⟨2,![10,23,30,20],![18,20,58,46]⟩
def cycle201_4 : CycleData E W := ⟨2,![12,24,29,16],![4,32,58,34]⟩
def cycle201_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle201_6 : CycleData E W := ⟨4,![17,15,28,27,31,21],![6,30,34,22,10,46]⟩
def data201 : PartitionData E W := ⟨7,![cycle201_0,cycle201_1,cycle201_2,cycle201_3,cycle201_4,cycle201_5,cycle201_6]⟩
lemma valid201 : data201.Valid src201 dst201 Finset.univ := by decide +kernel
lemma src_eq201 : src201 = src (unkey (representativeKey 201)) := by decide +kernel
lemma dst_eq201 : dst201 = dst (unkey (representativeKey 201)) := by decide +kernel
lemma certificate201 : Certificate 201 := by
  refine ⟨data201,?_,?_⟩
  · rw [← src_eq201,← dst_eq201]
    exact valid201
  · decide +kernel

def src202 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,32,44,10,22,58,46,34]
def dst202 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,32,44,8,22,58,46,34,10]
def cycle202_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle202_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle202_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle202_3 : CycleData E W := ⟨2,![10,23,29,20],![18,20,58,46]⟩
def cycle202_4 : CycleData E W := ⟨4,![12,24,28,27,31,16],![4,32,58,22,10,34]⟩
def cycle202_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle202_6 : CycleData E W := ⟨2,![17,15,30,21],![6,30,34,46]⟩
def data202 : PartitionData E W := ⟨7,![cycle202_0,cycle202_1,cycle202_2,cycle202_3,cycle202_4,cycle202_5,cycle202_6]⟩
lemma valid202 : data202.Valid src202 dst202 Finset.univ := by decide +kernel
lemma src_eq202 : src202 = src (unkey (representativeKey 202)) := by decide +kernel
lemma dst_eq202 : dst202 = dst (unkey (representativeKey 202)) := by decide +kernel
lemma certificate202 : Certificate 202 := by
  refine ⟨data202,?_,?_⟩
  · rw [← src_eq202,← dst_eq202]
    exact valid202
  · decide +kernel

def src203 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,32,44,10,34,22,58,46]
def dst203 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,32,44,8,34,22,58,46,10]
def cycle203_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle203_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle203_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle203_3 : CycleData E W := ⟨2,![10,23,30,20],![18,20,58,46]⟩
def cycle203_4 : CycleData E W := ⟨3,![12,24,29,28,16],![4,32,58,22,34]⟩
def cycle203_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle203_6 : CycleData E W := ⟨3,![17,15,27,31,21],![6,30,34,10,46]⟩
def data203 : PartitionData E W := ⟨7,![cycle203_0,cycle203_1,cycle203_2,cycle203_3,cycle203_4,cycle203_5,cycle203_6]⟩
lemma valid203 : data203.Valid src203 dst203 Finset.univ := by decide +kernel
lemma src_eq203 : src203 = src (unkey (representativeKey 203)) := by decide +kernel
lemma dst_eq203 : dst203 = dst (unkey (representativeKey 203)) := by decide +kernel
lemma certificate203 : Certificate 203 := by
  refine ⟨data203,?_,?_⟩
  · rw [← src_eq203,← dst_eq203]
    exact valid203
  · decide +kernel

def src204 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,32,44,10,46,22,34,58]
def dst204 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,32,44,8,46,22,34,58,10]
def cycle204_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle204_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle204_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle204_3 : CycleData E W := ⟨3,![27,20,10,23,31],![10,46,18,20,58]⟩
def cycle204_4 : CycleData E W := ⟨2,![12,24,30,16],![4,32,58,34]⟩
def cycle204_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle204_6 : CycleData E W := ⟨3,![17,15,29,28,21],![6,30,34,22,46]⟩
def data204 : PartitionData E W := ⟨7,![cycle204_0,cycle204_1,cycle204_2,cycle204_3,cycle204_4,cycle204_5,cycle204_6]⟩
lemma valid204 : data204.Valid src204 dst204 Finset.univ := by decide +kernel
lemma src_eq204 : src204 = src (unkey (representativeKey 204)) := by decide +kernel
lemma dst_eq204 : dst204 = dst (unkey (representativeKey 204)) := by decide +kernel
lemma certificate204 : Certificate 204 := by
  refine ⟨data204,?_,?_⟩
  · rw [← src_eq204,← dst_eq204]
    exact valid204
  · decide +kernel

def src205 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,32,44,10,46,34,22,58]
def dst205 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,32,44,8,46,34,22,58,10]
def cycle205_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle205_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle205_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle205_3 : CycleData E W := ⟨3,![27,20,10,23,31],![10,46,18,20,58]⟩
def cycle205_4 : CycleData E W := ⟨3,![12,24,30,29,16],![4,32,58,22,34]⟩
def cycle205_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle205_6 : CycleData E W := ⟨2,![17,15,28,21],![6,30,34,46]⟩
def data205 : PartitionData E W := ⟨7,![cycle205_0,cycle205_1,cycle205_2,cycle205_3,cycle205_4,cycle205_5,cycle205_6]⟩
lemma valid205 : data205.Valid src205 dst205 Finset.univ := by decide +kernel
lemma src_eq205 : src205 = src (unkey (representativeKey 205)) := by decide +kernel
lemma dst_eq205 : dst205 = dst (unkey (representativeKey 205)) := by decide +kernel
lemma certificate205 : Certificate 205 := by
  refine ⟨data205,?_,?_⟩
  · rw [← src_eq205,← dst_eq205]
    exact valid205
  · decide +kernel

def src206 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,22,34,58,46]
def dst206 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,22,34,58,46,10]
def cycle206_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle206_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle206_2 : CycleData E W := ⟨4,![12,26,4,27,28,16],![4,32,8,10,22,34]⟩
def cycle206_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle206_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle206_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle206_6 : CycleData E W := ⟨3,![17,15,29,30,21],![6,30,34,58,46]⟩
def data206 : PartitionData E W := ⟨7,![cycle206_0,cycle206_1,cycle206_2,cycle206_3,cycle206_4,cycle206_5,cycle206_6]⟩
lemma valid206 : data206.Valid src206 dst206 Finset.univ := by decide +kernel
lemma src_eq206 : src206 = src (unkey (representativeKey 206)) := by decide +kernel
lemma dst_eq206 : dst206 = dst (unkey (representativeKey 206)) := by decide +kernel
lemma certificate206 : Certificate 206 := by
  refine ⟨data206,?_,?_⟩
  · rw [← src_eq206,← dst_eq206]
    exact valid206
  · decide +kernel

def src207 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,22,58,34,46]
def dst207 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle207_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle207_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle207_2 : CycleData E W := ⟨5,![12,26,4,27,28,29,16],![4,32,8,10,22,58,34]⟩
def cycle207_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle207_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle207_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle207_6 : CycleData E W := ⟨2,![17,15,30,21],![6,30,34,46]⟩
def data207 : PartitionData E W := ⟨7,![cycle207_0,cycle207_1,cycle207_2,cycle207_3,cycle207_4,cycle207_5,cycle207_6]⟩
lemma valid207 : data207.Valid src207 dst207 Finset.univ := by decide +kernel
lemma src_eq207 : src207 = src (unkey (representativeKey 207)) := by decide +kernel
lemma dst_eq207 : dst207 = dst (unkey (representativeKey 207)) := by decide +kernel
lemma certificate207 : Certificate 207 := by
  refine ⟨data207,?_,?_⟩
  · rw [← src_eq207,← dst_eq207]
    exact valid207
  · decide +kernel

def src208 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,34,22,58,46]
def dst208 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle208_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle208_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle208_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle208_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle208_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle208_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle208_6 : CycleData E W := ⟨4,![17,15,28,29,30,21],![6,30,34,22,58,46]⟩
def data208 : PartitionData E W := ⟨7,![cycle208_0,cycle208_1,cycle208_2,cycle208_3,cycle208_4,cycle208_5,cycle208_6]⟩
lemma valid208 : data208.Valid src208 dst208 Finset.univ := by decide +kernel
lemma src_eq208 : src208 = src (unkey (representativeKey 208)) := by decide +kernel
lemma dst_eq208 : dst208 = dst (unkey (representativeKey 208)) := by decide +kernel
lemma certificate208 : Certificate 208 := by
  refine ⟨data208,?_,?_⟩
  · rw [← src_eq208,← dst_eq208]
    exact valid208
  · decide +kernel

def src209 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,34,58,22,46]
def dst209 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle209_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle209_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle209_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle209_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle209_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle209_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle209_6 : CycleData E W := ⟨4,![17,15,28,29,30,21],![6,30,34,58,22,46]⟩
def data209 : PartitionData E W := ⟨7,![cycle209_0,cycle209_1,cycle209_2,cycle209_3,cycle209_4,cycle209_5,cycle209_6]⟩
lemma valid209 : data209.Valid src209 dst209 Finset.univ := by decide +kernel
lemma src_eq209 : src209 = src (unkey (representativeKey 209)) := by decide +kernel
lemma dst_eq209 : dst209 = dst (unkey (representativeKey 209)) := by decide +kernel
lemma certificate209 : Certificate 209 := by
  refine ⟨data209,?_,?_⟩
  · rw [← src_eq209,← dst_eq209]
    exact valid209
  · decide +kernel

def src210 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,46,22,34,58]
def dst210 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle210_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle210_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle210_2 : CycleData E W := ⟨4,![12,26,4,31,30,16],![4,32,8,10,58,34]⟩
def cycle210_3 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle210_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle210_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle210_6 : CycleData E W := ⟨3,![17,15,29,28,21],![6,30,34,22,46]⟩
def data210 : PartitionData E W := ⟨7,![cycle210_0,cycle210_1,cycle210_2,cycle210_3,cycle210_4,cycle210_5,cycle210_6]⟩
lemma valid210 : data210.Valid src210 dst210 Finset.univ := by decide +kernel
lemma src_eq210 : src210 = src (unkey (representativeKey 210)) := by decide +kernel
lemma dst_eq210 : dst210 = dst (unkey (representativeKey 210)) := by decide +kernel
lemma certificate210 : Certificate 210 := by
  refine ⟨data210,?_,?_⟩
  · rw [← src_eq210,← dst_eq210]
    exact valid210
  · decide +kernel

def src211 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,58,44,32,10,46,34,22,58]
def dst211 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,58,44,32,8,46,34,22,58,10]
def cycle211_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle211_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle211_2 : CycleData E W := ⟨5,![12,26,4,31,30,29,16],![4,32,8,10,58,22,34]⟩
def cycle211_3 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle211_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle211_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle211_6 : CycleData E W := ⟨2,![17,15,28,21],![6,30,34,46]⟩
def data211 : PartitionData E W := ⟨7,![cycle211_0,cycle211_1,cycle211_2,cycle211_3,cycle211_4,cycle211_5,cycle211_6]⟩
lemma valid211 : data211.Valid src211 dst211 Finset.univ := by decide +kernel
lemma src_eq211 : src211 = src (unkey (representativeKey 211)) := by decide +kernel
lemma dst_eq211 : dst211 = dst (unkey (representativeKey 211)) := by decide +kernel
lemma certificate211 : Certificate 211 := by
  refine ⟨data211,?_,?_⟩
  · rw [← src_eq211,← dst_eq211]
    exact valid211
  · decide +kernel

def src212 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,32,20,58,44,10,22,34,58,46]
def dst212 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,32,20,58,44,8,22,34,58,46,10]
def cycle212_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle212_1 : CycleData E W := ⟨3,![2,17,15,28,8],![3,6,30,34,22]⟩
def cycle212_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle212_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle212_4 : CycleData E W := ⟨3,![12,23,24,29,16],![4,32,20,58,34]⟩
def cycle212_5 : CycleData E W := ⟨3,![22,13,14,18,26],![8,32,16,30,44]⟩
def cycle212_6 : CycleData E W := ⟨2,![19,25,30,20],![18,44,58,46]⟩
def data212 : PartitionData E W := ⟨7,![cycle212_0,cycle212_1,cycle212_2,cycle212_3,cycle212_4,cycle212_5,cycle212_6]⟩
lemma valid212 : data212.Valid src212 dst212 Finset.univ := by decide +kernel
lemma src_eq212 : src212 = src (unkey (representativeKey 212)) := by decide +kernel
lemma dst_eq212 : dst212 = dst (unkey (representativeKey 212)) := by decide +kernel
lemma certificate212 : Certificate 212 := by
  refine ⟨data212,?_,?_⟩
  · rw [← src_eq212,← dst_eq212]
    exact valid212
  · decide +kernel

def src213 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,32,20,58,44,10,22,58,34,46]
def dst213 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle213_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle213_1 : CycleData E W := ⟨3,![1,16,29,24,9],![3,4,34,58,20]⟩
def cycle213_2 : CycleData E W := ⟨3,![2,3,4,27,8],![3,6,8,10,22]⟩
def cycle213_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle213_4 : CycleData E W := ⟨3,![7,28,25,18,14],![16,22,58,44,30]⟩
def cycle213_5 : CycleData E W := ⟨3,![22,23,10,19,26],![8,32,20,18,44]⟩
def cycle213_6 : CycleData E W := ⟨2,![17,15,30,21],![6,30,34,46]⟩
def data213 : PartitionData E W := ⟨7,![cycle213_0,cycle213_1,cycle213_2,cycle213_3,cycle213_4,cycle213_5,cycle213_6]⟩
lemma valid213 : data213.Valid src213 dst213 Finset.univ := by decide +kernel
lemma src_eq213 : src213 = src (unkey (representativeKey 213)) := by decide +kernel
lemma dst_eq213 : dst213 = dst (unkey (representativeKey 213)) := by decide +kernel
lemma certificate213 : Certificate 213 := by
  refine ⟨data213,?_,?_⟩
  · rw [← src_eq213,← dst_eq213]
    exact valid213
  · decide +kernel

def src214 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,32,20,58,44,10,22,58,46,34]
def dst214 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle214_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle214_1 : CycleData E W := ⟨3,![1,16,30,21,2],![3,4,34,46,6]⟩
def cycle214_2 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle214_3 : CycleData E W := ⟨4,![5,4,22,23,10,11],![2,10,8,32,20,18]⟩
def cycle214_4 : CycleData E W := ⟨3,![27,7,14,15,31],![10,22,16,30,34]⟩
def cycle214_5 : CycleData E W := ⟨2,![8,28,24,9],![3,22,58,20]⟩
def cycle214_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data214 : PartitionData E W := ⟨7,![cycle214_0,cycle214_1,cycle214_2,cycle214_3,cycle214_4,cycle214_5,cycle214_6]⟩
lemma valid214 : data214.Valid src214 dst214 Finset.univ := by decide +kernel
lemma src_eq214 : src214 = src (unkey (representativeKey 214)) := by decide +kernel
lemma dst_eq214 : dst214 = dst (unkey (representativeKey 214)) := by decide +kernel
lemma certificate214 : Certificate 214 := by
  refine ⟨data214,?_,?_⟩
  · rw [← src_eq214,← dst_eq214]
    exact valid214
  · decide +kernel

def src215 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,32,20,58,44,10,34,58,22,46]
def dst215 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,32,20,58,44,8,34,58,22,46,10]
def cycle215_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle215_1 : CycleData E W := ⟨4,![1,16,27,4,3,2],![3,4,34,10,8,6]⟩
def cycle215_2 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle215_3 : CycleData E W := ⟨3,![17,14,7,30,21],![6,30,16,22,46]⟩
def cycle215_4 : CycleData E W := ⟨2,![8,29,24,9],![3,22,58,20]⟩
def cycle215_5 : CycleData E W := ⟨3,![22,23,10,19,26],![8,32,20,18,44]⟩
def cycle215_6 : CycleData E W := ⟨2,![15,28,25,18],![30,34,58,44]⟩
def data215 : PartitionData E W := ⟨7,![cycle215_0,cycle215_1,cycle215_2,cycle215_3,cycle215_4,cycle215_5,cycle215_6]⟩
lemma valid215 : data215.Valid src215 dst215 Finset.univ := by decide +kernel
lemma src_eq215 : src215 = src (unkey (representativeKey 215)) := by decide +kernel
lemma dst_eq215 : dst215 = dst (unkey (representativeKey 215)) := by decide +kernel
lemma certificate215 : Certificate 215 := by
  refine ⟨data215,?_,?_⟩
  · rw [← src_eq215,← dst_eq215]
    exact valid215
  · decide +kernel

def src216 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,32,20,58,44,10,46,22,34,58]
def dst216 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,32,20,58,44,8,46,22,34,58,10]
def cycle216_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle216_1 : CycleData E W := ⟨2,![2,21,28,8],![3,6,46,22]⟩
def cycle216_2 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle216_3 : CycleData E W := ⟨3,![5,4,22,13,6],![2,10,8,32,16]⟩
def cycle216_4 : CycleData E W := ⟨2,![7,29,15,14],![16,22,34,30]⟩
def cycle216_5 : CycleData E W := ⟨3,![12,23,24,30,16],![4,32,20,58,34]⟩
def cycle216_6 : CycleData E W := ⟨3,![27,20,19,25,31],![10,46,18,44,58]⟩
def data216 : PartitionData E W := ⟨7,![cycle216_0,cycle216_1,cycle216_2,cycle216_3,cycle216_4,cycle216_5,cycle216_6]⟩
lemma valid216 : data216.Valid src216 dst216 Finset.univ := by decide +kernel
lemma src_eq216 : src216 = src (unkey (representativeKey 216)) := by decide +kernel
lemma dst_eq216 : dst216 = dst (unkey (representativeKey 216)) := by decide +kernel
lemma certificate216 : Certificate 216 := by
  refine ⟨data216,?_,?_⟩
  · rw [← src_eq216,← dst_eq216]
    exact valid216
  · decide +kernel

def src217 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,32,58,44,10,22,58,34,46]
def dst217 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,32,58,44,8,22,58,34,46,10]
def cycle217_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle217_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle217_2 : CycleData E W := ⟨3,![4,27,28,25,26],![8,10,22,58,44]⟩
def cycle217_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle217_4 : CycleData E W := ⟨3,![13,23,10,19,14],![16,32,20,18,30]⟩
def cycle217_5 : CycleData E W := ⟨2,![12,24,29,16],![4,32,58,34]⟩
def cycle217_6 : CycleData E W := ⟨3,![17,18,15,30,21],![6,44,30,34,46]⟩
def data217 : PartitionData E W := ⟨7,![cycle217_0,cycle217_1,cycle217_2,cycle217_3,cycle217_4,cycle217_5,cycle217_6]⟩
lemma valid217 : data217.Valid src217 dst217 Finset.univ := by decide +kernel
lemma src_eq217 : src217 = src (unkey (representativeKey 217)) := by decide +kernel
lemma dst_eq217 : dst217 = dst (unkey (representativeKey 217)) := by decide +kernel
lemma certificate217 : Certificate 217 := by
  refine ⟨data217,?_,?_⟩
  · rw [← src_eq217,← dst_eq217]
    exact valid217
  · decide +kernel

def src218 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,32,58,44,10,22,58,46,34]
def dst218 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle218_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle218_1 : CycleData E W := ⟨3,![2,21,29,28,8],![3,6,46,58,22]⟩
def cycle218_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle218_3 : CycleData E W := ⟨4,![12,23,22,4,31,16],![4,32,20,8,10,34]⟩
def cycle218_4 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle218_5 : CycleData E W := ⟨3,![13,24,25,18,14],![16,32,58,44,30]⟩
def cycle218_6 : CycleData E W := ⟨2,![19,15,30,20],![18,30,34,46]⟩
def data218 : PartitionData E W := ⟨7,![cycle218_0,cycle218_1,cycle218_2,cycle218_3,cycle218_4,cycle218_5,cycle218_6]⟩
lemma valid218 : data218.Valid src218 dst218 Finset.univ := by decide +kernel
lemma src_eq218 : src218 = src (unkey (representativeKey 218)) := by decide +kernel
lemma dst_eq218 : dst218 = dst (unkey (representativeKey 218)) := by decide +kernel
lemma certificate218 : Certificate 218 := by
  refine ⟨data218,?_,?_⟩
  · rw [← src_eq218,← dst_eq218]
    exact valid218
  · decide +kernel

def src219 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,32,58,44,10,34,58,22,46]
def dst219 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle219_0 : CycleData E W := ⟨2,![0,16,27,5],![2,4,34,10]⟩
def cycle219_1 : CycleData E W := ⟨2,![1,12,23,9],![3,4,32,20]⟩
def cycle219_2 : CycleData E W := ⟨2,![2,21,30,8],![3,6,46,22]⟩
def cycle219_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle219_4 : CycleData E W := ⟨3,![4,31,20,10,22],![8,10,46,18,20]⟩
def cycle219_5 : CycleData E W := ⟨2,![6,14,19,11],![2,16,30,18]⟩
def cycle219_6 : CycleData E W := ⟨2,![7,29,24,13],![16,22,58,32]⟩
def cycle219_7 : CycleData E W := ⟨2,![15,28,25,18],![30,34,58,44]⟩
def data219 : PartitionData E W := ⟨8,![cycle219_0,cycle219_1,cycle219_2,cycle219_3,cycle219_4,cycle219_5,cycle219_6,cycle219_7]⟩
lemma valid219 : data219.Valid src219 dst219 Finset.univ := by decide +kernel
lemma src_eq219 : src219 = src (unkey (representativeKey 219)) := by decide +kernel
lemma dst_eq219 : dst219 = dst (unkey (representativeKey 219)) := by decide +kernel
lemma certificate219 : Certificate 219 := by
  refine ⟨data219,?_,?_⟩
  · rw [← src_eq219,← dst_eq219]
    exact valid219
  · decide +kernel

def src220 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,32,44,10,22,34,58,46]
def dst220 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,32,44,8,22,34,58,46,10]
def cycle220_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle220_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,46,18,20]⟩
def cycle220_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle220_3 : CycleData E W := ⟨3,![4,31,30,23,22],![8,10,46,58,20]⟩
def cycle220_4 : CycleData E W := ⟨4,![5,27,28,15,19,11],![2,10,22,34,30,18]⟩
def cycle220_5 : CycleData E W := ⟨2,![12,24,29,16],![4,32,58,34]⟩
def cycle220_6 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def data220 : PartitionData E W := ⟨7,![cycle220_0,cycle220_1,cycle220_2,cycle220_3,cycle220_4,cycle220_5,cycle220_6]⟩
lemma valid220 : data220.Valid src220 dst220 Finset.univ := by decide +kernel
lemma src_eq220 : src220 = src (unkey (representativeKey 220)) := by decide +kernel
lemma dst_eq220 : dst220 = dst (unkey (representativeKey 220)) := by decide +kernel
lemma certificate220 : Certificate 220 := by
  refine ⟨data220,?_,?_⟩
  · rw [← src_eq220,← dst_eq220]
    exact valid220
  · decide +kernel

def src221 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,32,44,10,34,22,58,46]
def dst221 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,32,44,8,34,22,58,46,10]
def cycle221_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle221_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,46,18,20]⟩
def cycle221_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle221_3 : CycleData E W := ⟨3,![4,31,30,23,22],![8,10,46,58,20]⟩
def cycle221_4 : CycleData E W := ⟨3,![5,27,15,19,11],![2,10,34,30,18]⟩
def cycle221_5 : CycleData E W := ⟨3,![12,24,29,28,16],![4,32,58,22,34]⟩
def cycle221_6 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def data221 : PartitionData E W := ⟨7,![cycle221_0,cycle221_1,cycle221_2,cycle221_3,cycle221_4,cycle221_5,cycle221_6]⟩
lemma valid221 : data221.Valid src221 dst221 Finset.univ := by decide +kernel
lemma src_eq221 : src221 = src (unkey (representativeKey 221)) := by decide +kernel
lemma dst_eq221 : dst221 = dst (unkey (representativeKey 221)) := by decide +kernel
lemma certificate221 : Certificate 221 := by
  refine ⟨data221,?_,?_⟩
  · rw [← src_eq221,← dst_eq221]
    exact valid221
  · decide +kernel

def src222 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,32,44,10,34,58,22,46]
def dst222 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,32,44,8,34,58,22,46,10]
def cycle222_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle222_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,46,18,20]⟩
def cycle222_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle222_3 : CycleData E W := ⟨4,![4,31,30,29,23,22],![8,10,46,22,58,20]⟩
def cycle222_4 : CycleData E W := ⟨3,![5,27,15,19,11],![2,10,34,30,18]⟩
def cycle222_5 : CycleData E W := ⟨2,![12,24,28,16],![4,32,58,34]⟩
def cycle222_6 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def data222 : PartitionData E W := ⟨7,![cycle222_0,cycle222_1,cycle222_2,cycle222_3,cycle222_4,cycle222_5,cycle222_6]⟩
lemma valid222 : data222.Valid src222 dst222 Finset.univ := by decide +kernel
lemma src_eq222 : src222 = src (unkey (representativeKey 222)) := by decide +kernel
lemma dst_eq222 : dst222 = dst (unkey (representativeKey 222)) := by decide +kernel
lemma certificate222 : Certificate 222 := by
  refine ⟨data222,?_,?_⟩
  · rw [← src_eq222,← dst_eq222]
    exact valid222
  · decide +kernel

def src223 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,22,34,58,46]
def dst223 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,22,34,58,46,10]
def cycle223_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle223_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle223_2 : CycleData E W := ⟨4,![12,26,4,27,28,16],![4,32,8,10,22,34]⟩
def cycle223_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle223_4 : CycleData E W := ⟨3,![10,23,29,15,19],![18,20,58,34,30]⟩
def cycle223_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle223_6 : CycleData E W := ⟨2,![17,24,30,21],![6,44,58,46]⟩
def data223 : PartitionData E W := ⟨7,![cycle223_0,cycle223_1,cycle223_2,cycle223_3,cycle223_4,cycle223_5,cycle223_6]⟩
lemma valid223 : data223.Valid src223 dst223 Finset.univ := by decide +kernel
lemma src_eq223 : src223 = src (unkey (representativeKey 223)) := by decide +kernel
lemma dst_eq223 : dst223 = dst (unkey (representativeKey 223)) := by decide +kernel
lemma certificate223 : Certificate 223 := by
  refine ⟨data223,?_,?_⟩
  · rw [← src_eq223,← dst_eq223]
    exact valid223
  · decide +kernel

def src224 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,22,58,34,46]
def dst224 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle224_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle224_1 : CycleData E W := ⟨3,![2,17,24,28,8],![3,6,44,58,22]⟩
def cycle224_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle224_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle224_4 : CycleData E W := ⟨4,![12,26,22,23,29,16],![4,32,8,20,58,34]⟩
def cycle224_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle224_6 : CycleData E W := ⟨2,![19,15,30,20],![18,30,34,46]⟩
def data224 : PartitionData E W := ⟨7,![cycle224_0,cycle224_1,cycle224_2,cycle224_3,cycle224_4,cycle224_5,cycle224_6]⟩
lemma valid224 : data224.Valid src224 dst224 Finset.univ := by decide +kernel
lemma src_eq224 : src224 = src (unkey (representativeKey 224)) := by decide +kernel
lemma dst_eq224 : dst224 = dst (unkey (representativeKey 224)) := by decide +kernel
lemma certificate224 : Certificate 224 := by
  refine ⟨data224,?_,?_⟩
  · rw [← src_eq224,← dst_eq224]
    exact valid224
  · decide +kernel

def src225 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,34,22,58,46]
def dst225 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle225_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle225_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle225_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle225_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle225_4 : CycleData E W := ⟨4,![10,23,29,28,15,19],![18,20,58,22,34,30]⟩
def cycle225_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle225_6 : CycleData E W := ⟨2,![17,24,30,21],![6,44,58,46]⟩
def data225 : PartitionData E W := ⟨7,![cycle225_0,cycle225_1,cycle225_2,cycle225_3,cycle225_4,cycle225_5,cycle225_6]⟩
lemma valid225 : data225.Valid src225 dst225 Finset.univ := by decide +kernel
lemma src_eq225 : src225 = src (unkey (representativeKey 225)) := by decide +kernel
lemma dst_eq225 : dst225 = dst (unkey (representativeKey 225)) := by decide +kernel
lemma certificate225 : Certificate 225 := by
  refine ⟨data225,?_,?_⟩
  · rw [← src_eq225,← dst_eq225]
    exact valid225
  · decide +kernel

def src226 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,34,58,22,46]
def dst226 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle226_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle226_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle226_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle226_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle226_4 : CycleData E W := ⟨3,![10,23,28,15,19],![18,20,58,34,30]⟩
def cycle226_5 : CycleData E W := ⟨2,![13,25,18,14],![16,32,44,30]⟩
def cycle226_6 : CycleData E W := ⟨3,![17,24,29,30,21],![6,44,58,22,46]⟩
def data226 : PartitionData E W := ⟨7,![cycle226_0,cycle226_1,cycle226_2,cycle226_3,cycle226_4,cycle226_5,cycle226_6]⟩
lemma valid226 : data226.Valid src226 dst226 Finset.univ := by decide +kernel
lemma src_eq226 : src226 = src (unkey (representativeKey 226)) := by decide +kernel
lemma dst_eq226 : dst226 = dst (unkey (representativeKey 226)) := by decide +kernel
lemma certificate226 : Certificate 226 := by
  refine ⟨data226,?_,?_⟩
  · rw [← src_eq226,← dst_eq226]
    exact valid226
  · decide +kernel

def src227 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,46,22,34,58]
def dst227 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle227_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle227_1 : CycleData E W := ⟨2,![2,21,28,8],![3,6,46,22]⟩
def cycle227_2 : CycleData E W := ⟨2,![3,26,25,17],![6,8,32,44]⟩
def cycle227_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle227_4 : CycleData E W := ⟨4,![5,27,20,19,14,6],![2,10,46,18,30,16]⟩
def cycle227_5 : CycleData E W := ⟨3,![12,13,7,29,16],![4,32,16,22,34]⟩
def cycle227_6 : CycleData E W := ⟨2,![15,30,24,18],![30,34,58,44]⟩
def data227 : PartitionData E W := ⟨7,![cycle227_0,cycle227_1,cycle227_2,cycle227_3,cycle227_4,cycle227_5,cycle227_6]⟩
lemma valid227 : data227.Valid src227 dst227 Finset.univ := by decide +kernel
lemma src_eq227 : src227 = src (unkey (representativeKey 227)) := by decide +kernel
lemma dst_eq227 : dst227 = dst (unkey (representativeKey 227)) := by decide +kernel
lemma certificate227 : Certificate 227 := by
  refine ⟨data227,?_,?_⟩
  · rw [← src_eq227,← dst_eq227]
    exact valid227
  · decide +kernel

def src228 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,20,58,44,32,10,46,34,22,58]
def dst228 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,20,58,44,32,8,46,34,22,58,10]
def cycle228_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle228_1 : CycleData E W := ⟨4,![1,16,15,19,10,9],![3,4,34,30,18,20]⟩
def cycle228_2 : CycleData E W := ⟨3,![2,21,28,29,8],![3,6,46,34,22]⟩
def cycle228_3 : CycleData E W := ⟨2,![3,26,25,17],![6,8,32,44]⟩
def cycle228_4 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle228_5 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle228_6 : CycleData E W := ⟨3,![7,30,24,18,14],![16,22,58,44,30]⟩
def data228 : PartitionData E W := ⟨7,![cycle228_0,cycle228_1,cycle228_2,cycle228_3,cycle228_4,cycle228_5,cycle228_6]⟩
lemma valid228 : data228.Valid src228 dst228 Finset.univ := by decide +kernel
lemma src_eq228 : src228 = src (unkey (representativeKey 228)) := by decide +kernel
lemma dst_eq228 : dst228 = dst (unkey (representativeKey 228)) := by decide +kernel
lemma certificate228 : Certificate 228 := by
  refine ⟨data228,?_,?_⟩
  · rw [← src_eq228,← dst_eq228]
    exact valid228
  · decide +kernel

def src229 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,22,34,58,46]
def dst229 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,22,34,58,46,10]
def cycle229_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle229_1 : CycleData E W := ⟨3,![2,21,30,24,9],![3,6,46,58,20]⟩
def cycle229_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle229_3 : CycleData E W := ⟨4,![12,22,4,27,28,16],![4,32,8,10,22,34]⟩
def cycle229_4 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle229_5 : CycleData E W := ⟨3,![13,23,10,19,14],![16,32,20,18,30]⟩
def cycle229_6 : CycleData E W := ⟨2,![15,29,25,18],![30,34,58,44]⟩
def data229 : PartitionData E W := ⟨7,![cycle229_0,cycle229_1,cycle229_2,cycle229_3,cycle229_4,cycle229_5,cycle229_6]⟩
lemma valid229 : data229.Valid src229 dst229 Finset.univ := by decide +kernel
lemma src_eq229 : src229 = src (unkey (representativeKey 229)) := by decide +kernel
lemma dst_eq229 : dst229 = dst (unkey (representativeKey 229)) := by decide +kernel
lemma certificate229 : Certificate 229 := by
  refine ⟨data229,?_,?_⟩
  · rw [← src_eq229,← dst_eq229]
    exact valid229
  · decide +kernel

def src230 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,22,58,34,46]
def dst230 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle230_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle230_1 : CycleData E W := ⟨3,![2,17,25,28,8],![3,6,44,58,22]⟩
def cycle230_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle230_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle230_4 : CycleData E W := ⟨3,![12,23,24,29,16],![4,32,20,58,34]⟩
def cycle230_5 : CycleData E W := ⟨3,![22,13,14,18,26],![8,32,16,30,44]⟩
def cycle230_6 : CycleData E W := ⟨2,![19,15,30,20],![18,30,34,46]⟩
def data230 : PartitionData E W := ⟨7,![cycle230_0,cycle230_1,cycle230_2,cycle230_3,cycle230_4,cycle230_5,cycle230_6]⟩
lemma valid230 : data230.Valid src230 dst230 Finset.univ := by decide +kernel
lemma src_eq230 : src230 = src (unkey (representativeKey 230)) := by decide +kernel
lemma dst_eq230 : dst230 = dst (unkey (representativeKey 230)) := by decide +kernel
lemma certificate230 : Certificate 230 := by
  refine ⟨data230,?_,?_⟩
  · rw [← src_eq230,← dst_eq230]
    exact valid230
  · decide +kernel

def src231 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,22,58,46,34]
def dst231 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle231_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle231_1 : CycleData E W := ⟨3,![2,21,29,28,8],![3,6,46,58,22]⟩
def cycle231_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle231_3 : CycleData E W := ⟨3,![12,22,4,31,16],![4,32,8,10,34]⟩
def cycle231_4 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle231_5 : CycleData E W := ⟨4,![13,23,24,25,18,14],![16,32,20,58,44,30]⟩
def cycle231_6 : CycleData E W := ⟨2,![19,15,30,20],![18,30,34,46]⟩
def data231 : PartitionData E W := ⟨7,![cycle231_0,cycle231_1,cycle231_2,cycle231_3,cycle231_4,cycle231_5,cycle231_6]⟩
lemma valid231 : data231.Valid src231 dst231 Finset.univ := by decide +kernel
lemma src_eq231 : src231 = src (unkey (representativeKey 231)) := by decide +kernel
lemma dst_eq231 : dst231 = dst (unkey (representativeKey 231)) := by decide +kernel
lemma certificate231 : Certificate 231 := by
  refine ⟨data231,?_,?_⟩
  · rw [← src_eq231,← dst_eq231]
    exact valid231
  · decide +kernel

def src232 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,34,58,22,46]
def dst232 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,34,58,22,46,10]
def cycle232_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle232_1 : CycleData E W := ⟨4,![2,21,30,29,24,9],![3,6,46,22,58,20]⟩
def cycle232_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle232_3 : CycleData E W := ⟨3,![12,22,4,27,16],![4,32,8,10,34]⟩
def cycle232_4 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle232_5 : CycleData E W := ⟨3,![13,23,10,19,14],![16,32,20,18,30]⟩
def cycle232_6 : CycleData E W := ⟨2,![15,28,25,18],![30,34,58,44]⟩
def data232 : PartitionData E W := ⟨7,![cycle232_0,cycle232_1,cycle232_2,cycle232_3,cycle232_4,cycle232_5,cycle232_6]⟩
lemma valid232 : data232.Valid src232 dst232 Finset.univ := by decide +kernel
lemma src_eq232 : src232 = src (unkey (representativeKey 232)) := by decide +kernel
lemma dst_eq232 : dst232 = dst (unkey (representativeKey 232)) := by decide +kernel
lemma certificate232 : Certificate 232 := by
  refine ⟨data232,?_,?_⟩
  · rw [← src_eq232,← dst_eq232]
    exact valid232
  · decide +kernel

def src233 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,46,22,34,58]
def dst233 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,46,22,34,58,10]
def cycle233_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle233_1 : CycleData E W := ⟨2,![2,21,28,8],![3,6,46,22]⟩
def cycle233_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle233_3 : CycleData E W := ⟨3,![5,4,22,13,6],![2,10,8,32,16]⟩
def cycle233_4 : CycleData E W := ⟨2,![7,29,15,14],![16,22,34,30]⟩
def cycle233_5 : CycleData E W := ⟨3,![12,23,24,30,16],![4,32,20,58,34]⟩
def cycle233_6 : CycleData E W := ⟨4,![27,20,19,18,25,31],![10,46,18,30,44,58]⟩
def data233 : PartitionData E W := ⟨7,![cycle233_0,cycle233_1,cycle233_2,cycle233_3,cycle233_4,cycle233_5,cycle233_6]⟩
lemma valid233 : data233.Valid src233 dst233 Finset.univ := by decide +kernel
lemma src_eq233 : src233 = src (unkey (representativeKey 233)) := by decide +kernel
lemma dst_eq233 : dst233 = dst (unkey (representativeKey 233)) := by decide +kernel
lemma certificate233 : Certificate 233 := by
  refine ⟨data233,?_,?_⟩
  · rw [← src_eq233,← dst_eq233]
    exact valid233
  · decide +kernel

def src234 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,30,32,34,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst234 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,30,32,34,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle234_0 : CycleData E W := ⟨2,![0,12,7,6],![2,4,16,18]⟩
def cycle234_1 : CycleData E W := ⟨3,![1,16,15,23,10],![3,4,34,32,20]⟩
def cycle234_2 : CycleData E W := ⟨4,![2,17,18,25,29,9],![3,6,18,44,58,22]⟩
def cycle234_3 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle234_4 : CycleData E W := ⟨2,![4,27,28,26],![8,10,34,58]⟩
def cycle234_5 : CycleData E W := ⟨3,![5,31,19,24,11],![2,10,46,44,20]⟩
def cycle234_6 : CycleData E W := ⟨2,![8,30,20,13],![16,22,46,30]⟩
def data234 : PartitionData E W := ⟨7,![cycle234_0,cycle234_1,cycle234_2,cycle234_3,cycle234_4,cycle234_5,cycle234_6]⟩
lemma valid234 : data234.Valid src234 dst234 Finset.univ := by decide +kernel
lemma src_eq234 : src234 = src (unkey (representativeKey 234)) := by decide +kernel
lemma dst_eq234 : dst234 = dst (unkey (representativeKey 234)) := by decide +kernel
lemma certificate234 : Certificate 234 := by
  refine ⟨data234,?_,?_⟩
  · rw [← src_eq234,← dst_eq234]
    exact valid234
  · decide +kernel

def src235 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,30,32,34,6,18,44,46,30,8,32,20,58,44,10,46,22,34,58]
def dst235 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,30,32,34,4,18,44,46,30,6,32,20,58,44,8,46,22,34,58,10]
def cycle235_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle235_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle235_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle235_3 : CycleData E W := ⟨3,![5,4,26,18,6],![2,10,8,44,18]⟩
def cycle235_4 : CycleData E W := ⟨4,![12,13,20,28,29,16],![4,16,30,46,22,34]⟩
def cycle235_5 : CycleData E W := ⟨2,![23,15,30,24],![20,32,34,58]⟩
def cycle235_6 : CycleData E W := ⟨2,![27,19,25,31],![10,46,44,58]⟩
def data235 : PartitionData E W := ⟨7,![cycle235_0,cycle235_1,cycle235_2,cycle235_3,cycle235_4,cycle235_5,cycle235_6]⟩
lemma valid235 : data235.Valid src235 dst235 Finset.univ := by decide +kernel
lemma src_eq235 : src235 = src (unkey (representativeKey 235)) := by decide +kernel
lemma dst_eq235 : dst235 = dst (unkey (representativeKey 235)) := by decide +kernel
lemma certificate235 : Certificate 235 := by
  refine ⟨data235,?_,?_⟩
  · rw [← src_eq235,← dst_eq235]
    exact valid235
  · decide +kernel

def src236 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,30,32,34,6,30,44,18,46,8,32,20,58,44,10,22,58,46,34]
def dst236 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,30,32,34,4,30,44,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle236_0 : CycleData E W := ⟨2,![0,12,7,6],![2,4,16,18]⟩
def cycle236_1 : CycleData E W := ⟨3,![1,16,15,23,10],![3,4,34,32,20]⟩
def cycle236_2 : CycleData E W := ⟨3,![2,17,13,8,9],![3,6,30,16,22]⟩
def cycle236_3 : CycleData E W := ⟨3,![3,4,31,30,21],![6,8,10,34,46]⟩
def cycle236_4 : CycleData E W := ⟨3,![5,27,28,24,11],![2,10,22,58,20]⟩
def cycle236_5 : CycleData E W := ⟨2,![22,14,18,26],![8,32,30,44]⟩
def cycle236_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data236 : PartitionData E W := ⟨7,![cycle236_0,cycle236_1,cycle236_2,cycle236_3,cycle236_4,cycle236_5,cycle236_6]⟩
lemma valid236 : data236.Valid src236 dst236 Finset.univ := by decide +kernel
lemma src_eq236 : src236 = src (unkey (representativeKey 236)) := by decide +kernel
lemma dst_eq236 : dst236 = dst (unkey (representativeKey 236)) := by decide +kernel
lemma certificate236 : Certificate 236 := by
  refine ⟨data236,?_,?_⟩
  · rw [← src_eq236,← dst_eq236]
    exact valid236
  · decide +kernel

def src237 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,30,34,32,6,30,44,18,46,8,32,20,44,58,10,22,58,46,34]
def dst237 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,30,34,32,4,30,44,18,46,6,32,20,44,58,8,22,58,46,34,10]
def cycle237_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle237_1 : CycleData E W := ⟨3,![2,3,26,28,9],![3,6,8,58,22]⟩
def cycle237_2 : CycleData E W := ⟨2,![4,31,15,22],![8,10,34,32]⟩
def cycle237_3 : CycleData E W := ⟨3,![5,27,8,7,6],![2,10,22,16,18]⟩
def cycle237_4 : CycleData E W := ⟨4,![12,13,18,24,23,16],![4,16,30,44,20,32]⟩
def cycle237_5 : CycleData E W := ⟨2,![17,14,30,21],![6,30,34,46]⟩
def cycle237_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data237 : PartitionData E W := ⟨7,![cycle237_0,cycle237_1,cycle237_2,cycle237_3,cycle237_4,cycle237_5,cycle237_6]⟩
lemma valid237 : data237.Valid src237 dst237 Finset.univ := by decide +kernel
lemma src_eq237 : src237 = src (unkey (representativeKey 237)) := by decide +kernel
lemma dst_eq237 : dst237 = dst (unkey (representativeKey 237)) := by decide +kernel
lemma certificate237 : Certificate 237 := by
  refine ⟨data237,?_,?_⟩
  · rw [← src_eq237,← dst_eq237]
    exact valid237
  · decide +kernel

def src238 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,30,34,32,6,30,44,18,46,8,32,20,58,44,10,22,58,46,34]
def dst238 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,30,34,32,4,30,44,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle238_0 : CycleData E W := ⟨2,![0,12,7,6],![2,4,16,18]⟩
def cycle238_1 : CycleData E W := ⟨3,![1,16,22,3,2],![3,4,32,8,6]⟩
def cycle238_2 : CycleData E W := ⟨4,![4,27,8,13,18,26],![8,10,22,16,30,44]⟩
def cycle238_3 : CycleData E W := ⟨3,![5,31,15,23,11],![2,10,34,32,20]⟩
def cycle238_4 : CycleData E W := ⟨2,![9,28,24,10],![3,22,58,20]⟩
def cycle238_5 : CycleData E W := ⟨2,![17,14,30,21],![6,30,34,46]⟩
def cycle238_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data238 : PartitionData E W := ⟨7,![cycle238_0,cycle238_1,cycle238_2,cycle238_3,cycle238_4,cycle238_5,cycle238_6]⟩
lemma valid238 : data238.Valid src238 dst238 Finset.univ := by decide +kernel
lemma src_eq238 : src238 = src (unkey (representativeKey 238)) := by decide +kernel
lemma dst_eq238 : dst238 = dst (unkey (representativeKey 238)) := by decide +kernel
lemma certificate238 : Certificate 238 := by
  refine ⟨data238,?_,?_⟩
  · rw [← src_eq238,← dst_eq238]
    exact valid238
  · decide +kernel

def src239 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,20,44,58,32,10,34,58,22,46]
def dst239 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,20,44,58,32,8,34,58,22,46,10]
def cycle239_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,16,18]⟩
def cycle239_1 : CycleData E W := ⟨3,![2,17,18,23,10],![3,6,18,44,20]⟩
def cycle239_2 : CycleData E W := ⟨2,![3,26,14,21],![6,8,32,30]⟩
def cycle239_3 : CycleData E W := ⟨2,![5,4,22,11],![2,10,8,20]⟩
def cycle239_4 : CycleData E W := ⟨3,![12,13,25,28,16],![4,16,32,58,34]⟩
def cycle239_5 : CycleData E W := ⟨2,![27,15,20,31],![10,34,30,46]⟩
def cycle239_6 : CycleData E W := ⟨2,![29,24,19,30],![22,58,44,46]⟩
def data239 : PartitionData E W := ⟨7,![cycle239_0,cycle239_1,cycle239_2,cycle239_3,cycle239_4,cycle239_5,cycle239_6]⟩
lemma valid239 : data239.Valid src239 dst239 Finset.univ := by decide +kernel
lemma src_eq239 : src239 = src (unkey (representativeKey 239)) := by decide +kernel
lemma dst_eq239 : dst239 = dst (unkey (representativeKey 239)) := by decide +kernel
lemma certificate239 : Certificate 239 := by
  refine ⟨data239,?_,?_⟩
  · rw [← src_eq239,← dst_eq239]
    exact valid239
  · decide +kernel

def src240 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,20,58,44,32,10,34,58,22,46]
def dst240 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,20,58,44,32,8,34,58,22,46,10]
def cycle240_0 : CycleData E W := ⟨2,![0,12,7,6],![2,4,16,18]⟩
def cycle240_1 : CycleData E W := ⟨3,![1,16,15,21,2],![3,4,34,30,6]⟩
def cycle240_2 : CycleData E W := ⟨3,![3,26,25,18,17],![6,8,32,44,18]⟩
def cycle240_3 : CycleData E W := ⟨2,![5,4,22,11],![2,10,8,20]⟩
def cycle240_4 : CycleData E W := ⟨3,![8,30,20,14,13],![16,22,46,30,32]⟩
def cycle240_5 : CycleData E W := ⟨2,![9,29,23,10],![3,22,58,20]⟩
def cycle240_6 : CycleData E W := ⟨3,![27,28,24,19,31],![10,34,58,44,46]⟩
def data240 : PartitionData E W := ⟨7,![cycle240_0,cycle240_1,cycle240_2,cycle240_3,cycle240_4,cycle240_5,cycle240_6]⟩
lemma valid240 : data240.Valid src240 dst240 Finset.univ := by decide +kernel
lemma src_eq240 : src240 = src (unkey (representativeKey 240)) := by decide +kernel
lemma dst_eq240 : dst240 = dst (unkey (representativeKey 240)) := by decide +kernel
lemma certificate240 : Certificate 240 := by
  refine ⟨data240,?_,?_⟩
  · rw [← src_eq240,← dst_eq240]
    exact valid240
  · decide +kernel

def src241 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst241 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle241_0 : CycleData E W := ⟨2,![0,16,27,5],![2,4,34,10]⟩
def cycle241_1 : CycleData E W := ⟨2,![1,12,8,9],![3,4,16,22]⟩
def cycle241_2 : CycleData E W := ⟨3,![6,17,2,10,11],![2,18,6,3,20]⟩
def cycle241_3 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle241_4 : CycleData E W := ⟨3,![4,31,19,25,26],![8,10,46,44,58]⟩
def cycle241_5 : CycleData E W := ⟨3,![7,18,24,23,13],![16,18,44,20,32]⟩
def cycle241_6 : CycleData E W := ⟨3,![29,28,15,20,30],![22,58,34,30,46]⟩
def data241 : PartitionData E W := ⟨7,![cycle241_0,cycle241_1,cycle241_2,cycle241_3,cycle241_4,cycle241_5,cycle241_6]⟩
lemma valid241 : data241.Valid src241 dst241 Finset.univ := by decide +kernel
lemma src_eq241 : src241 = src (unkey (representativeKey 241)) := by decide +kernel
lemma dst_eq241 : dst241 = dst (unkey (representativeKey 241)) := by decide +kernel
lemma certificate241 : Certificate 241 := by
  refine ⟨data241,?_,?_⟩
  · rw [← src_eq241,← dst_eq241]
    exact valid241
  · decide +kernel

def src242 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,20,44,58,10,46,22,34,58]
def dst242 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,20,44,58,8,46,22,34,58,10]
def cycle242_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle242_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle242_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle242_3 : CycleData E W := ⟨1,![4,31,26],![8,10,58]⟩
def cycle242_4 : CycleData E W := ⟨3,![5,27,19,18,6],![2,10,46,44,18]⟩
def cycle242_5 : CycleData E W := ⟨5,![12,13,23,24,25,30,16],![4,16,32,20,44,58,34]⟩
def cycle242_6 : CycleData E W := ⟨2,![28,20,15,29],![22,46,30,34]⟩
def data242 : PartitionData E W := ⟨7,![cycle242_0,cycle242_1,cycle242_2,cycle242_3,cycle242_4,cycle242_5,cycle242_6]⟩
lemma valid242 : data242.Valid src242 dst242 Finset.univ := by decide +kernel
lemma src_eq242 : src242 = src (unkey (representativeKey 242)) := by decide +kernel
lemma dst_eq242 : dst242 = dst (unkey (representativeKey 242)) := by decide +kernel
lemma certificate242 : Certificate 242 := by
  refine ⟨data242,?_,?_⟩
  · rw [← src_eq242,← dst_eq242]
    exact valid242
  · decide +kernel

def src243 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,20,58,44,10,34,58,22,46]
def dst243 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,20,58,44,8,34,58,22,46,10]
def cycle243_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle243_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle243_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle243_3 : CycleData E W := ⟨3,![5,4,26,18,6],![2,10,8,44,18]⟩
def cycle243_4 : CycleData E W := ⟨4,![12,13,23,24,28,16],![4,16,32,20,58,34]⟩
def cycle243_5 : CycleData E W := ⟨2,![27,15,20,31],![10,34,30,46]⟩
def cycle243_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data243 : PartitionData E W := ⟨7,![cycle243_0,cycle243_1,cycle243_2,cycle243_3,cycle243_4,cycle243_5,cycle243_6]⟩
lemma valid243 : data243.Valid src243 dst243 Finset.univ := by decide +kernel
lemma src_eq243 : src243 = src (unkey (representativeKey 243)) := by decide +kernel
lemma dst_eq243 : dst243 = dst (unkey (representativeKey 243)) := by decide +kernel
lemma certificate243 : Certificate 243 := by
  refine ⟨data243,?_,?_⟩
  · rw [← src_eq243,← dst_eq243]
    exact valid243
  · decide +kernel

def src244 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,20,58,44,10,46,22,34,58]
def dst244 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,20,58,44,8,46,22,34,58,10]
def cycle244_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle244_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle244_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle244_3 : CycleData E W := ⟨3,![5,4,26,18,6],![2,10,8,44,18]⟩
def cycle244_4 : CycleData E W := ⟨4,![12,13,23,24,30,16],![4,16,32,20,58,34]⟩
def cycle244_5 : CycleData E W := ⟨2,![28,20,15,29],![22,46,30,34]⟩
def cycle244_6 : CycleData E W := ⟨2,![27,19,25,31],![10,46,44,58]⟩
def data244 : PartitionData E W := ⟨7,![cycle244_0,cycle244_1,cycle244_2,cycle244_3,cycle244_4,cycle244_5,cycle244_6]⟩
lemma valid244 : data244.Valid src244 dst244 Finset.univ := by decide +kernel
lemma src_eq244 : src244 = src (unkey (representativeKey 244)) := by decide +kernel
lemma dst_eq244 : dst244 = dst (unkey (representativeKey 244)) := by decide +kernel
lemma certificate244 : Certificate 244 := by
  refine ⟨data244,?_,?_⟩
  · rw [← src_eq244,← dst_eq244]
    exact valid244
  · decide +kernel

def src245 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,44,20,58,10,34,58,22,46]
def dst245 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,44,20,58,8,34,58,22,46,10]
def cycle245_0 : CycleData E W := ⟨2,![0,12,7,6],![2,4,16,18]⟩
def cycle245_1 : CycleData E W := ⟨3,![1,16,15,21,2],![3,4,34,30,6]⟩
def cycle245_2 : CycleData E W := ⟨3,![3,22,23,18,17],![6,8,32,44,18]⟩
def cycle245_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,34,58]⟩
def cycle245_4 : CycleData E W := ⟨3,![5,31,19,24,11],![2,10,46,44,20]⟩
def cycle245_5 : CycleData E W := ⟨3,![8,30,20,14,13],![16,22,46,30,32]⟩
def cycle245_6 : CycleData E W := ⟨2,![9,29,25,10],![3,22,58,20]⟩
def data245 : PartitionData E W := ⟨7,![cycle245_0,cycle245_1,cycle245_2,cycle245_3,cycle245_4,cycle245_5,cycle245_6]⟩
lemma valid245 : data245.Valid src245 dst245 Finset.univ := by decide +kernel
lemma src_eq245 : src245 = src (unkey (representativeKey 245)) := by decide +kernel
lemma dst_eq245 : dst245 = dst (unkey (representativeKey 245)) := by decide +kernel
lemma certificate245 : Certificate 245 := by
  refine ⟨data245,?_,?_⟩
  · rw [← src_eq245,← dst_eq245]
    exact valid245
  · decide +kernel

def src246 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,44,20,58,10,46,22,34,58]
def dst246 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,44,20,58,8,46,22,34,58,10]
def cycle246_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle246_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle246_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle246_3 : CycleData E W := ⟨1,![4,31,26],![8,10,58]⟩
def cycle246_4 : CycleData E W := ⟨3,![5,27,19,18,6],![2,10,46,44,18]⟩
def cycle246_5 : CycleData E W := ⟨5,![12,13,23,24,25,30,16],![4,16,32,44,20,58,34]⟩
def cycle246_6 : CycleData E W := ⟨2,![28,20,15,29],![22,46,30,34]⟩
def data246 : PartitionData E W := ⟨7,![cycle246_0,cycle246_1,cycle246_2,cycle246_3,cycle246_4,cycle246_5,cycle246_6]⟩
lemma valid246 : data246.Valid src246 dst246 Finset.univ := by decide +kernel
lemma src_eq246 : src246 = src (unkey (representativeKey 246)) := by decide +kernel
lemma dst_eq246 : dst246 = dst (unkey (representativeKey 246)) := by decide +kernel
lemma certificate246 : Certificate 246 := by
  refine ⟨data246,?_,?_⟩
  · rw [← src_eq246,← dst_eq246]
    exact valid246
  · decide +kernel

def src247 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,18,44,46,30,8,32,58,20,44,10,34,58,22,46]
def dst247 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,18,44,46,30,6,32,58,20,44,8,34,58,22,46,10]
def cycle247_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle247_1 : CycleData E W := ⟨3,![2,17,7,8,9],![3,6,18,16,22]⟩
def cycle247_2 : CycleData E W := ⟨2,![3,22,14,21],![6,8,32,30]⟩
def cycle247_3 : CycleData E W := ⟨3,![5,4,26,18,6],![2,10,8,44,18]⟩
def cycle247_4 : CycleData E W := ⟨3,![12,13,23,28,16],![4,16,32,58,34]⟩
def cycle247_5 : CycleData E W := ⟨2,![27,15,20,31],![10,34,30,46]⟩
def cycle247_6 : CycleData E W := ⟨3,![24,29,30,19,25],![20,58,22,46,44]⟩
def data247 : PartitionData E W := ⟨7,![cycle247_0,cycle247_1,cycle247_2,cycle247_3,cycle247_4,cycle247_5,cycle247_6]⟩
lemma valid247 : data247.Valid src247 dst247 Finset.univ := by decide +kernel
lemma src_eq247 : src247 = src (unkey (representativeKey 247)) := by decide +kernel
lemma dst_eq247 : dst247 = dst (unkey (representativeKey 247)) := by decide +kernel
lemma certificate247 : Certificate 247 := by
  refine ⟨data247,?_,?_⟩
  · rw [← src_eq247,← dst_eq247]
    exact valid247
  · decide +kernel

def src248 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,30,18,44,46,8,32,20,58,44,10,34,46,22,58]
def dst248 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,30,18,44,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle248_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle248_1 : CycleData E W := ⟨2,![2,21,29,9],![3,6,46,22]⟩
def cycle248_2 : CycleData E W := ⟨2,![3,22,14,17],![6,8,32,30]⟩
def cycle248_3 : CycleData E W := ⟨3,![5,4,26,19,6],![2,10,8,44,18]⟩
def cycle248_4 : CycleData E W := ⟨3,![12,7,18,15,16],![4,16,18,30,34]⟩
def cycle248_5 : CycleData E W := ⟨3,![8,30,24,23,13],![16,22,58,20,32]⟩
def cycle248_6 : CycleData E W := ⟨3,![27,28,20,25,31],![10,34,46,44,58]⟩
def data248 : PartitionData E W := ⟨7,![cycle248_0,cycle248_1,cycle248_2,cycle248_3,cycle248_4,cycle248_5,cycle248_6]⟩
lemma valid248 : data248.Valid src248 dst248 Finset.univ := by decide +kernel
lemma src_eq248 : src248 = src (unkey (representativeKey 248)) := by decide +kernel
lemma dst_eq248 : dst248 = dst (unkey (representativeKey 248)) := by decide +kernel
lemma certificate248 : Certificate 248 := by
  refine ⟨data248,?_,?_⟩
  · rw [← src_eq248,← dst_eq248]
    exact valid248
  · decide +kernel

def src249 : E → W := ![2,4,3,6,8,10,2,18,16,22,3,20,4,16,32,30,34,6,30,46,18,44,8,32,20,44,58,10,34,22,58,46]
def dst249 : E → W := ![4,3,6,8,10,2,18,16,22,3,20,2,16,32,30,34,4,30,46,18,44,6,32,20,44,58,8,34,22,58,46,10]
def cycle249_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle249_1 : CycleData E W := ⟨3,![2,21,25,29,9],![3,6,44,58,22]⟩
def cycle249_2 : CycleData E W := ⟨2,![3,22,14,17],![6,8,32,30]⟩
def cycle249_3 : CycleData E W := ⟨4,![5,4,26,30,19,6],![2,10,8,58,46,18]⟩
def cycle249_4 : CycleData E W := ⟨3,![7,20,24,23,13],![16,18,44,20,32]⟩
def cycle249_5 : CycleData E W := ⟨2,![12,8,28,16],![4,16,22,34]⟩
def cycle249_6 : CycleData E W := ⟨2,![27,15,18,31],![10,34,30,46]⟩
def data249 : PartitionData E W := ⟨7,![cycle249_0,cycle249_1,cycle249_2,cycle249_3,cycle249_4,cycle249_5,cycle249_6]⟩
lemma valid249 : data249.Valid src249 dst249 Finset.univ := by decide +kernel
lemma src_eq249 : src249 = src (unkey (representativeKey 249)) := by decide +kernel
lemma dst_eq249 : dst249 = dst (unkey (representativeKey 249)) := by decide +kernel
lemma certificate249 : Certificate 249 := by
  refine ⟨data249,?_,?_⟩
  · rw [← src_eq249,← dst_eq249]
    exact valid249
  · decide +kernel
#print axioms certificate249
end Erdos184Work.SixRepresentativeCertificates1

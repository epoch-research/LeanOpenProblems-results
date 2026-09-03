import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src150 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,16,38,26,39,8,38,18,28,39]
def dst150 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle150_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle150_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle150_2 : CycleData E W := ⟨3,![2,20,24,23,9],![3,6,39,28,18]⟩
def cycle150_3 : CycleData E W := ⟨2,![3,12,13,8],![3,5,26,14]⟩
def cycle150_4 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle150_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data150 : PartitionData E W := ⟨6,![cycle150_0,cycle150_1,cycle150_2,cycle150_3,cycle150_4,cycle150_5]⟩
lemma valid_data150 : data150.Valid src150 dst150 Finset.univ := by decide +kernel

def src151 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,16,38,26,39,8,38,28,18,39]
def dst151 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle151_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle151_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle151_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle151_3 : CycleData E W := ⟨2,![3,12,13,8],![3,5,26,14]⟩
def cycle151_4 : CycleData E W := ⟨3,![6,17,22,23,10],![2,16,38,28,18]⟩
def cycle151_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data151 : PartitionData E W := ⟨6,![cycle151_0,cycle151_1,cycle151_2,cycle151_3,cycle151_4,cycle151_5]⟩
lemma valid_data151 : data151.Valid src151 dst151 Finset.univ := by decide +kernel

def src152 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,16,39,26,38,8,38,18,28,39]
def dst152 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle152_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle152_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle152_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle152_3 : CycleData E W := ⟨2,![3,12,13,8],![3,5,26,14]⟩
def cycle152_4 : CycleData E W := ⟨3,![6,17,24,23,10],![2,16,39,28,18]⟩
def cycle152_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data152 : PartitionData E W := ⟨6,![cycle152_0,cycle152_1,cycle152_2,cycle152_3,cycle152_4,cycle152_5]⟩
lemma valid_data152 : data152.Valid src152 dst152 Finset.univ := by decide +kernel

def src153 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,16,39,26,38,8,38,28,18,39]
def dst153 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle153_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle153_1 : CycleData E W := ⟨3,![1,16,7,14,15],![4,6,16,14,28]⟩
def cycle153_2 : CycleData E W := ⟨3,![2,20,22,23,9],![3,6,38,28,18]⟩
def cycle153_3 : CycleData E W := ⟨2,![3,12,13,8],![3,5,26,14]⟩
def cycle153_4 : CycleData E W := ⟨2,![6,17,24,10],![2,16,39,18]⟩
def cycle153_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data153 : PartitionData E W := ⟨6,![cycle153_0,cycle153_1,cycle153_2,cycle153_3,cycle153_4,cycle153_5]⟩
lemma valid_data153 : data153.Valid src153 dst153 Finset.univ := by decide +kernel

def src154 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,16,26,39,8,18,38,28,39]
def dst154 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle154_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle154_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle154_2 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle154_3 : CycleData E W := ⟨3,![5,21,22,17,6],![2,8,18,38,16]⟩
def cycle154_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle154_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data154 : PartitionData E W := ⟨6,![cycle154_0,cycle154_1,cycle154_2,cycle154_3,cycle154_4,cycle154_5]⟩
lemma valid_data154 : data154.Valid src154 dst154 Finset.univ := by decide +kernel

def src155 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,16,26,39,8,18,39,28,38]
def dst155 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle155_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle155_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle155_2 : CycleData E W := ⟨3,![4,21,22,19,12],![5,8,18,39,26]⟩
def cycle155_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,38,16]⟩
def cycle155_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle155_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data155 : PartitionData E W := ⟨6,![cycle155_0,cycle155_1,cycle155_2,cycle155_3,cycle155_4,cycle155_5]⟩
lemma valid_data155 : data155.Valid src155 dst155 Finset.univ := by decide +kernel

def src156 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst156 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle156_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle156_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle156_2 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle156_3 : CycleData E W := ⟨2,![5,21,17,6],![2,8,38,16]⟩
def cycle156_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle156_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data156 : PartitionData E W := ⟨6,![cycle156_0,cycle156_1,cycle156_2,cycle156_3,cycle156_4,cycle156_5]⟩
lemma valid_data156 : data156.Valid src156 dst156 Finset.univ := by decide +kernel

def src157 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,26,16,39,8,18,38,28,39]
def dst157 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle157_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle157_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle157_2 : CycleData E W := ⟨3,![4,21,22,17,12],![5,8,18,38,26]⟩
def cycle157_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle157_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle157_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data157 : PartitionData E W := ⟨6,![cycle157_0,cycle157_1,cycle157_2,cycle157_3,cycle157_4,cycle157_5]⟩
lemma valid_data157 : data157.Valid src157 dst157 Finset.univ := by decide +kernel

def src158 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,26,16,39,8,18,39,28,38]
def dst158 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle158_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle158_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle158_2 : CycleData E W := ⟨2,![4,25,17,12],![5,8,38,26]⟩
def cycle158_3 : CycleData E W := ⟨3,![5,21,22,19,6],![2,8,18,39,16]⟩
def cycle158_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle158_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data158 : PartitionData E W := ⟨6,![cycle158_0,cycle158_1,cycle158_2,cycle158_3,cycle158_4,cycle158_5]⟩
lemma valid_data158 : data158.Valid src158 dst158 Finset.univ := by decide +kernel

def src159 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst159 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle159_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle159_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,28,14]⟩
def cycle159_2 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle159_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle159_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle159_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data159 : PartitionData E W := ⟨6,![cycle159_0,cycle159_1,cycle159_2,cycle159_3,cycle159_4,cycle159_5]⟩
lemma valid_data159 : data159.Valid src159 dst159 Finset.univ := by decide +kernel

def src160 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,26,38,39,8,38,18,28,39]
def dst160 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle160_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle160_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle160_2 : CycleData E W := ⟨3,![5,4,12,17,6],![2,8,5,26,16]⟩
def cycle160_3 : CycleData E W := ⟨3,![16,7,14,24,20],![6,16,14,28,39]⟩
def cycle160_4 : CycleData E W := ⟨3,![11,18,22,23,15],![4,26,38,18,28]⟩
def cycle160_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data160 : PartitionData E W := ⟨6,![cycle160_0,cycle160_1,cycle160_2,cycle160_3,cycle160_4,cycle160_5]⟩
lemma valid_data160 : data160.Valid src160 dst160 Finset.univ := by decide +kernel

def src161 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,26,39,38,8,38,28,18,39]
def dst161 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle161_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle161_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle161_2 : CycleData E W := ⟨3,![5,4,12,17,6],![2,8,5,26,16]⟩
def cycle161_3 : CycleData E W := ⟨3,![16,7,14,22,20],![6,16,14,28,38]⟩
def cycle161_4 : CycleData E W := ⟨3,![11,18,24,23,15],![4,26,39,18,28]⟩
def cycle161_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data161 : PartitionData E W := ⟨6,![cycle161_0,cycle161_1,cycle161_2,cycle161_3,cycle161_4,cycle161_5]⟩
lemma valid_data161 : data161.Valid src161 dst161 Finset.univ := by decide +kernel

def src162 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,28,38,18,39]
def dst162 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle162_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle162_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle162_2 : CycleData E W := ⟨3,![11,12,4,21,15],![4,26,5,8,28]⟩
def cycle162_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle162_4 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle162_5 : CycleData E W := ⟨2,![23,18,19,24],![18,38,26,39]⟩
def data162 : PartitionData E W := ⟨6,![cycle162_0,cycle162_1,cycle162_2,cycle162_3,cycle162_4,cycle162_5]⟩
lemma valid_data162 : data162.Valid src162 dst162 Finset.univ := by decide +kernel

def src163 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,28,39,18,38]
def dst163 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle163_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle163_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle163_2 : CycleData E W := ⟨3,![11,12,4,21,15],![4,26,5,8,28]⟩
def cycle163_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,38,16]⟩
def cycle163_4 : CycleData E W := ⟨3,![16,7,14,22,20],![6,16,14,28,39]⟩
def cycle163_5 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data163 : PartitionData E W := ⟨6,![cycle163_0,cycle163_1,cycle163_2,cycle163_3,cycle163_4,cycle163_5]⟩
lemma valid_data163 : data163.Valid src163 dst163 Finset.univ := by decide +kernel

def src164 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,38,18,28,39]
def dst164 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle164_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle164_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle164_2 : CycleData E W := ⟨2,![4,21,18,12],![5,8,38,26]⟩
def cycle164_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle164_4 : CycleData E W := ⟨3,![7,17,22,23,14],![14,16,38,18,28]⟩
def cycle164_5 : CycleData E W := ⟨2,![11,19,24,15],![4,26,39,28]⟩
def data164 : PartitionData E W := ⟨6,![cycle164_0,cycle164_1,cycle164_2,cycle164_3,cycle164_4,cycle164_5]⟩
lemma valid_data164 : data164.Valid src164 dst164 Finset.univ := by decide +kernel

def src165 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,38,26,39,8,38,28,18,39]
def dst165 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle165_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle165_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle165_2 : CycleData E W := ⟨2,![4,21,18,12],![5,8,38,26]⟩
def cycle165_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,39,6,16]⟩
def cycle165_4 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle165_5 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def data165 : PartitionData E W := ⟨6,![cycle165_0,cycle165_1,cycle165_2,cycle165_3,cycle165_4,cycle165_5]⟩
lemma valid_data165 : data165.Valid src165 dst165 Finset.univ := by decide +kernel

def src166 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,38,39,26,8,38,28,18,39]
def dst166 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle166_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle166_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle166_2 : CycleData E W := ⟨4,![5,4,12,20,16,6],![2,8,5,26,6,16]⟩
def cycle166_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle166_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle166_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data166 : PartitionData E W := ⟨6,![cycle166_0,cycle166_1,cycle166_2,cycle166_3,cycle166_4,cycle166_5]⟩
lemma valid_data166 : data166.Valid src166 dst166 Finset.univ := by decide +kernel

def src167 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,28,38,18,39]
def dst167 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle167_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle167_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle167_2 : CycleData E W := ⟨3,![11,12,4,21,15],![4,26,5,8,28]⟩
def cycle167_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle167_4 : CycleData E W := ⟨3,![16,7,14,22,20],![6,16,14,28,38]⟩
def cycle167_5 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data167 : PartitionData E W := ⟨6,![cycle167_0,cycle167_1,cycle167_2,cycle167_3,cycle167_4,cycle167_5]⟩
lemma valid_data167 : data167.Valid src167 dst167 Finset.univ := by decide +kernel

def src168 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,28,39,18,38]
def dst168 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle168_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle168_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle168_2 : CycleData E W := ⟨3,![11,12,4,21,15],![4,26,5,8,28]⟩
def cycle168_3 : CycleData E W := ⟨3,![5,25,20,16,6],![2,8,38,6,16]⟩
def cycle168_4 : CycleData E W := ⟨2,![7,17,22,14],![14,16,39,28]⟩
def cycle168_5 : CycleData E W := ⟨2,![23,18,19,24],![18,39,26,38]⟩
def data168 : PartitionData E W := ⟨6,![cycle168_0,cycle168_1,cycle168_2,cycle168_3,cycle168_4,cycle168_5]⟩
lemma valid_data168 : data168.Valid src168 dst168 Finset.univ := by decide +kernel

def src169 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,38,18,28,39]
def dst169 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle169_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle169_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle169_2 : CycleData E W := ⟨2,![4,21,19,12],![5,8,38,26]⟩
def cycle169_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle169_4 : CycleData E W := ⟨4,![16,7,14,23,22,20],![6,16,14,28,18,38]⟩
def cycle169_5 : CycleData E W := ⟨2,![11,18,24,15],![4,26,39,28]⟩
def data169 : PartitionData E W := ⟨6,![cycle169_0,cycle169_1,cycle169_2,cycle169_3,cycle169_4,cycle169_5]⟩
lemma valid_data169 : data169.Valid src169 dst169 Finset.univ := by decide +kernel

def src170 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,39,26,38,8,38,28,18,39]
def dst170 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle170_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle170_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle170_2 : CycleData E W := ⟨2,![4,21,19,12],![5,8,38,26]⟩
def cycle170_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle170_4 : CycleData E W := ⟨3,![16,7,14,22,20],![6,16,14,28,38]⟩
def cycle170_5 : CycleData E W := ⟨3,![11,18,24,23,15],![4,26,39,18,28]⟩
def data170 : PartitionData E W := ⟨6,![cycle170_0,cycle170_1,cycle170_2,cycle170_3,cycle170_4,cycle170_5]⟩
lemma valid_data170 : data170.Valid src170 dst170 Finset.univ := by decide +kernel

def src171 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,16,39,38,26,8,38,18,28,39]
def dst171 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle171_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle171_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle171_2 : CycleData E W := ⟨4,![5,4,12,20,16,6],![2,8,5,26,6,16]⟩
def cycle171_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,39,28]⟩
def cycle171_4 : CycleData E W := ⟨3,![11,19,22,23,15],![4,26,38,18,28]⟩
def cycle171_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data171 : PartitionData E W := ⟨6,![cycle171_0,cycle171_1,cycle171_2,cycle171_3,cycle171_4,cycle171_5]⟩
lemma valid_data171 : data171.Valid src171 dst171 Finset.univ := by decide +kernel

def src172 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,16,38,39,8,38,28,18,39]
def dst172 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle172_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle172_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle172_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle172_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle172_4 : CycleData E W := ⟨3,![5,4,12,17,6],![2,8,5,26,16]⟩
def cycle172_5 : CycleData E W := ⟨2,![7,18,22,14],![14,16,38,28]⟩
def cycle172_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data172 : PartitionData E W := ⟨7,![cycle172_0,cycle172_1,cycle172_2,cycle172_3,cycle172_4,cycle172_5,cycle172_6]⟩
lemma valid_data172 : data172.Valid src172 dst172 Finset.univ := by decide +kernel

def src173 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,16,39,38,8,38,18,28,39]
def dst173 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle173_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle173_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle173_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle173_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle173_4 : CycleData E W := ⟨3,![5,4,12,17,6],![2,8,5,26,16]⟩
def cycle173_5 : CycleData E W := ⟨2,![7,18,24,14],![14,16,39,28]⟩
def cycle173_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data173 : PartitionData E W := ⟨7,![cycle173_0,cycle173_1,cycle173_2,cycle173_3,cycle173_4,cycle173_5,cycle173_6]⟩
lemma valid_data173 : data173.Valid src173 dst173 Finset.univ := by decide +kernel

def src174 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,18,38,28,39]
def dst174 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle174_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle174_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle174_2 : CycleData E W := ⟨3,![4,21,22,17,12],![5,8,18,38,26]⟩
def cycle174_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle174_4 : CycleData E W := ⟨2,![7,18,23,14],![14,16,38,28]⟩
def cycle174_5 : CycleData E W := ⟨3,![11,16,20,24,15],![4,26,6,39,28]⟩
def data174 : PartitionData E W := ⟨6,![cycle174_0,cycle174_1,cycle174_2,cycle174_3,cycle174_4,cycle174_5]⟩
lemma valid_data174 : data174.Valid src174 dst174 Finset.univ := by decide +kernel

def src175 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,18,39,28,38]
def dst175 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle175_0 : CycleData E W := ⟨3,![0,15,14,7,6],![2,4,28,14,16]⟩
def cycle175_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle175_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,39,18]⟩
def cycle175_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle175_4 : CycleData E W := ⟨2,![4,25,17,12],![5,8,38,26]⟩
def cycle175_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle175_6 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data175 : PartitionData E W := ⟨7,![cycle175_0,cycle175_1,cycle175_2,cycle175_3,cycle175_4,cycle175_5,cycle175_6]⟩
lemma valid_data175 : data175.Valid src175 dst175 Finset.univ := by decide +kernel

def src176 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst176 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle176_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle176_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle176_2 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle176_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle176_4 : CycleData E W := ⟨3,![7,18,22,23,14],![14,16,38,18,28]⟩
def cycle176_5 : CycleData E W := ⟨3,![11,16,20,24,15],![4,26,6,39,28]⟩
def data176 : PartitionData E W := ⟨6,![cycle176_0,cycle176_1,cycle176_2,cycle176_3,cycle176_4,cycle176_5]⟩
lemma valid_data176 : data176.Valid src176 dst176 Finset.univ := by decide +kernel

def src177 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst177 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle177_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle177_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle177_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle177_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle177_4 : CycleData E W := ⟨2,![4,21,17,12],![5,8,38,26]⟩
def cycle177_5 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle177_6 : CycleData E W := ⟨2,![7,18,22,14],![14,16,38,28]⟩
def data177 : PartitionData E W := ⟨7,![cycle177_0,cycle177_1,cycle177_2,cycle177_3,cycle177_4,cycle177_5,cycle177_6]⟩
lemma valid_data177 : data177.Valid src177 dst177 Finset.univ := by decide +kernel

def src178 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,18,38,28,39]
def dst178 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle178_0 : CycleData E W := ⟨3,![0,15,14,7,6],![2,4,28,14,16]⟩
def cycle178_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle178_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle178_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle178_4 : CycleData E W := ⟨2,![4,25,17,12],![5,8,39,26]⟩
def cycle178_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle178_6 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data178 : PartitionData E W := ⟨7,![cycle178_0,cycle178_1,cycle178_2,cycle178_3,cycle178_4,cycle178_5,cycle178_6]⟩
lemma valid_data178 : data178.Valid src178 dst178 Finset.univ := by decide +kernel

def src179 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,18,39,28,38]
def dst179 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle179_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle179_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle179_2 : CycleData E W := ⟨3,![4,21,22,17,12],![5,8,18,39,26]⟩
def cycle179_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,38,16]⟩
def cycle179_4 : CycleData E W := ⟨2,![7,18,23,14],![14,16,39,28]⟩
def cycle179_5 : CycleData E W := ⟨3,![11,16,20,24,15],![4,26,6,38,28]⟩
def data179 : PartitionData E W := ⟨6,![cycle179_0,cycle179_1,cycle179_2,cycle179_3,cycle179_4,cycle179_5]⟩
lemma valid_data179 : data179.Valid src179 dst179 Finset.univ := by decide +kernel

def src180 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst180 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle180_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle180_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle180_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle180_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle180_4 : CycleData E W := ⟨2,![4,25,17,12],![5,8,39,26]⟩
def cycle180_5 : CycleData E W := ⟨2,![5,21,19,6],![2,8,38,16]⟩
def cycle180_6 : CycleData E W := ⟨2,![7,18,24,14],![14,16,39,28]⟩
def data180 : PartitionData E W := ⟨7,![cycle180_0,cycle180_1,cycle180_2,cycle180_3,cycle180_4,cycle180_5,cycle180_6]⟩
lemma valid_data180 : data180.Valid src180 dst180 Finset.univ := by decide +kernel

def src181 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst181 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle181_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle181_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle181_2 : CycleData E W := ⟨3,![4,21,20,16,12],![5,8,38,6,26]⟩
def cycle181_3 : CycleData E W := ⟨2,![5,25,18,6],![2,8,39,16]⟩
def cycle181_4 : CycleData E W := ⟨2,![7,19,22,14],![14,16,38,28]⟩
def cycle181_5 : CycleData E W := ⟨3,![11,17,24,23,15],![4,26,39,18,28]⟩
def data181 : PartitionData E W := ⟨6,![cycle181_0,cycle181_1,cycle181_2,cycle181_3,cycle181_4,cycle181_5]⟩
lemma valid_data181 : data181.Valid src181 dst181 Finset.univ := by decide +kernel

def src182 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,28,38,39]
def dst182 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle182_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle182_1 : CycleData E W := ⟨3,![2,1,15,22,9],![3,6,4,28,18]⟩
def cycle182_2 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle182_3 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle182_4 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle182_5 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def cycle182_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data182 : PartitionData E W := ⟨7,![cycle182_0,cycle182_1,cycle182_2,cycle182_3,cycle182_4,cycle182_5,cycle182_6]⟩
lemma valid_data182 : data182.Valid src182 dst182 Finset.univ := by decide +kernel

def src183 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,38,28,39]
def dst183 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle183_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle183_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle183_2 : CycleData E W := ⟨2,![2,16,22,9],![3,6,38,18]⟩
def cycle183_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle183_4 : CycleData E W := ⟨2,![4,25,19,12],![5,8,39,26]⟩
def cycle183_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle183_6 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def data183 : PartitionData E W := ⟨7,![cycle183_0,cycle183_1,cycle183_2,cycle183_3,cycle183_4,cycle183_5,cycle183_6]⟩
lemma valid_data183 : data183.Valid src183 dst183 Finset.univ := by decide +kernel

def src184 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,28,38]
def dst184 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle184_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle184_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle184_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle184_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,38,28]⟩
def cycle184_4 : CycleData E W := ⟨2,![11,19,23,15],![4,26,39,28]⟩
def cycle184_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data184 : PartitionData E W := ⟨6,![cycle184_0,cycle184_1,cycle184_2,cycle184_3,cycle184_4,cycle184_5]⟩
lemma valid_data184 : data184.Valid src184 dst184 Finset.univ := by decide +kernel

def src185 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,38,28]
def dst185 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle185_0 : CycleData E W := ⟨4,![0,1,2,8,7,6],![2,4,6,3,14,16]⟩
def cycle185_1 : CycleData E W := ⟨3,![3,12,19,22,9],![3,5,26,39,18]⟩
def cycle185_2 : CycleData E W := ⟨2,![4,25,14,13],![5,8,28,14]⟩
def cycle185_3 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle185_4 : CycleData E W := ⟨3,![11,18,17,24,15],![4,26,16,38,28]⟩
def cycle185_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data185 : PartitionData E W := ⟨6,![cycle185_0,cycle185_1,cycle185_2,cycle185_3,cycle185_4,cycle185_5]⟩
lemma valid_data185 : data185.Valid src185 dst185 Finset.univ := by decide +kernel

def src186 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,28,18,39,38]
def dst186 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle186_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle186_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle186_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle186_3 : CycleData E W := ⟨3,![21,14,7,17,25],![8,28,14,16,38]⟩
def cycle186_4 : CycleData E W := ⟨3,![11,19,23,22,15],![4,26,39,18,28]⟩
def cycle186_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data186 : PartitionData E W := ⟨6,![cycle186_0,cycle186_1,cycle186_2,cycle186_3,cycle186_4,cycle186_5]⟩
lemma valid_data186 : data186.Valid src186 dst186 Finset.univ := by decide +kernel

def src187 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst187 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle187_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle187_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle187_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle187_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle187_4 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def cycle187_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data187 : PartitionData E W := ⟨6,![cycle187_0,cycle187_1,cycle187_2,cycle187_3,cycle187_4,cycle187_5]⟩
lemma valid_data187 : data187.Valid src187 dst187 Finset.univ := by decide +kernel

def src188 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst188 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle188_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle188_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle188_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle188_3 : CycleData E W := ⟨3,![21,14,7,17,25],![8,28,14,16,38]⟩
def cycle188_4 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def cycle188_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data188 : PartitionData E W := ⟨6,![cycle188_0,cycle188_1,cycle188_2,cycle188_3,cycle188_4,cycle188_5]⟩
lemma valid_data188 : data188.Valid src188 dst188 Finset.univ := by decide +kernel

def src189 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst189 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle189_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle189_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle189_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle189_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle189_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle189_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data189 : PartitionData E W := ⟨6,![cycle189_0,cycle189_1,cycle189_2,cycle189_3,cycle189_4,cycle189_5]⟩
lemma valid_data189 : data189.Valid src189 dst189 Finset.univ := by decide +kernel

def src190 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,28,39,38]
def dst190 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle190_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle190_1 : CycleData E W := ⟨3,![2,1,15,22,9],![3,6,4,28,18]⟩
def cycle190_2 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle190_3 : CycleData E W := ⟨2,![4,25,17,12],![5,8,38,26]⟩
def cycle190_4 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle190_5 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def cycle190_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data190 : PartitionData E W := ⟨7,![cycle190_0,cycle190_1,cycle190_2,cycle190_3,cycle190_4,cycle190_5,cycle190_6]⟩
lemma valid_data190 : data190.Valid src190 dst190 Finset.univ := by decide +kernel

def src191 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,28,39]
def dst191 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle191_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle191_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle191_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle191_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle191_4 : CycleData E W := ⟨2,![11,17,23,15],![4,26,38,28]⟩
def cycle191_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data191 : PartitionData E W := ⟨6,![cycle191_0,cycle191_1,cycle191_2,cycle191_3,cycle191_4,cycle191_5]⟩
lemma valid_data191 : data191.Valid src191 dst191 Finset.univ := by decide +kernel

def src192 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,39,28]
def dst192 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle192_0 : CycleData E W := ⟨4,![0,1,2,8,7,6],![2,4,6,3,14,16]⟩
def cycle192_1 : CycleData E W := ⟨3,![3,12,17,22,9],![3,5,26,38,18]⟩
def cycle192_2 : CycleData E W := ⟨2,![4,25,14,13],![5,8,28,14]⟩
def cycle192_3 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle192_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle192_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data192 : PartitionData E W := ⟨6,![cycle192_0,cycle192_1,cycle192_2,cycle192_3,cycle192_4,cycle192_5]⟩
lemma valid_data192 : data192.Valid src192 dst192 Finset.univ := by decide +kernel

def src193 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,18,39,28,38]
def dst193 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle193_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle193_1 : CycleData E W := ⟨2,![1,16,24,15],![4,6,38,28]⟩
def cycle193_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,39,18]⟩
def cycle193_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle193_4 : CycleData E W := ⟨2,![4,25,17,12],![5,8,38,26]⟩
def cycle193_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle193_6 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def data193 : PartitionData E W := ⟨7,![cycle193_0,cycle193_1,cycle193_2,cycle193_3,cycle193_4,cycle193_5,cycle193_6]⟩
lemma valid_data193 : data193.Valid src193 dst193 Finset.univ := by decide +kernel

def src194 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,28,18,38,39]
def dst194 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle194_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle194_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle194_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle194_3 : CycleData E W := ⟨3,![21,14,7,19,25],![8,28,14,16,39]⟩
def cycle194_4 : CycleData E W := ⟨3,![11,17,23,22,15],![4,26,38,18,28]⟩
def cycle194_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data194 : PartitionData E W := ⟨6,![cycle194_0,cycle194_1,cycle194_2,cycle194_3,cycle194_4,cycle194_5]⟩
lemma valid_data194 : data194.Valid src194 dst194 Finset.univ := by decide +kernel

def src195 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst195 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle195_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle195_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle195_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle195_3 : CycleData E W := ⟨3,![21,14,7,19,25],![8,28,14,16,39]⟩
def cycle195_4 : CycleData E W := ⟨2,![11,17,22,15],![4,26,38,28]⟩
def cycle195_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data195 : PartitionData E W := ⟨6,![cycle195_0,cycle195_1,cycle195_2,cycle195_3,cycle195_4,cycle195_5]⟩
lemma valid_data195 : data195.Valid src195 dst195 Finset.univ := by decide +kernel

def src196 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst196 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle196_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle196_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle196_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle196_3 : CycleData E W := ⟨2,![7,19,22,14],![14,16,39,28]⟩
def cycle196_4 : CycleData E W := ⟨3,![11,17,25,21,15],![4,26,38,8,28]⟩
def cycle196_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data196 : PartitionData E W := ⟨6,![cycle196_0,cycle196_1,cycle196_2,cycle196_3,cycle196_4,cycle196_5]⟩
lemma valid_data196 : data196.Valid src196 dst196 Finset.univ := by decide +kernel

def src197 : E → W := ![2,4,6,3,5,8,2,16,14,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst197 : E → W := ![4,6,3,5,8,2,16,14,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle197_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,18]⟩
def cycle197_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle197_2 : CycleData E W := ⟨3,![5,4,12,18,6],![2,8,5,26,16]⟩
def cycle197_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle197_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle197_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data197 : PartitionData E W := ⟨6,![cycle197_0,cycle197_1,cycle197_2,cycle197_3,cycle197_4,cycle197_5]⟩
lemma valid_data197 : data197.Valid src197 dst197 Finset.univ := by decide +kernel

def src198 : E → W := ![2,4,6,3,8,5,2,3,14,16,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst198 : E → W := ![4,6,3,8,5,2,3,14,16,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle198_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle198_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,8,5,26,14]⟩
def cycle198_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle198_3 : CycleData E W := ⟨3,![11,8,17,22,15],![4,14,16,38,28]⟩
def cycle198_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle198_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data198 : PartitionData E W := ⟨6,![cycle198_0,cycle198_1,cycle198_2,cycle198_3,cycle198_4,cycle198_5]⟩
lemma valid_data198 : data198.Valid src198 dst198 Finset.univ := by decide +kernel

def src199 : E → W := ![2,4,6,3,8,5,2,3,14,16,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst199 : E → W := ![4,6,3,8,5,2,3,14,16,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle199_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,6,3]⟩
def cycle199_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,8,5,26,14]⟩
def cycle199_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle199_3 : CycleData E W := ⟨3,![11,8,19,24,15],![4,14,16,39,28]⟩
def cycle199_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle199_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data199 : PartitionData E W := ⟨6,![cycle199_0,cycle199_1,cycle199_2,cycle199_3,cycle199_4,cycle199_5]⟩
lemma valid_data199 : data199.Valid src199 dst199 Finset.univ := by decide +kernel

def lookupB3 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data150 else (if j < 2 then data151 else data152)) else (if j < 4 then data153 else (if j < 5 then data154 else data155))) else (if j < 9 then (if j < 7 then data156 else (if j < 8 then data157 else data158)) else (if j < 10 then data159 else (if j < 11 then data160 else data161)))) else (if j < 18 then (if j < 15 then (if j < 13 then data162 else (if j < 14 then data163 else data164)) else (if j < 16 then data165 else (if j < 17 then data166 else data167))) else (if j < 21 then (if j < 19 then data168 else (if j < 20 then data169 else data170)) else (if j < 23 then (if j < 22 then data171 else data172) else (if j < 24 then data173 else data174))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data175 else (if j < 27 then data176 else data177)) else (if j < 29 then data178 else (if j < 30 then data179 else data180))) else (if j < 34 then (if j < 32 then data181 else (if j < 33 then data182 else data183)) else (if j < 35 then data184 else (if j < 36 then data185 else data186)))) else (if j < 43 then (if j < 40 then (if j < 38 then data187 else (if j < 39 then data188 else data189)) else (if j < 41 then data190 else (if j < 42 then data191 else data192))) else (if j < 46 then (if j < 44 then data193 else (if j < 45 then data194 else data195)) else (if j < 48 then (if j < 47 then data196 else data197) else (if j < 49 then data198 else data199))))))

def srcTableB3 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src150 else (if j < 2 then src151 else src152)) else (if j < 4 then src153 else (if j < 5 then src154 else src155))) else (if j < 9 then (if j < 7 then src156 else (if j < 8 then src157 else src158)) else (if j < 10 then src159 else (if j < 11 then src160 else src161)))) else (if j < 18 then (if j < 15 then (if j < 13 then src162 else (if j < 14 then src163 else src164)) else (if j < 16 then src165 else (if j < 17 then src166 else src167))) else (if j < 21 then (if j < 19 then src168 else (if j < 20 then src169 else src170)) else (if j < 23 then (if j < 22 then src171 else src172) else (if j < 24 then src173 else src174))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src175 else (if j < 27 then src176 else src177)) else (if j < 29 then src178 else (if j < 30 then src179 else src180))) else (if j < 34 then (if j < 32 then src181 else (if j < 33 then src182 else src183)) else (if j < 35 then src184 else (if j < 36 then src185 else src186)))) else (if j < 43 then (if j < 40 then (if j < 38 then src187 else (if j < 39 then src188 else src189)) else (if j < 41 then src190 else (if j < 42 then src191 else src192))) else (if j < 46 then (if j < 44 then src193 else (if j < 45 then src194 else src195)) else (if j < 48 then (if j < 47 then src196 else src197) else (if j < 49 then src198 else src199))))))

def dstTableB3 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst150 else (if j < 2 then dst151 else dst152)) else (if j < 4 then dst153 else (if j < 5 then dst154 else dst155))) else (if j < 9 then (if j < 7 then dst156 else (if j < 8 then dst157 else dst158)) else (if j < 10 then dst159 else (if j < 11 then dst160 else dst161)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst162 else (if j < 14 then dst163 else dst164)) else (if j < 16 then dst165 else (if j < 17 then dst166 else dst167))) else (if j < 21 then (if j < 19 then dst168 else (if j < 20 then dst169 else dst170)) else (if j < 23 then (if j < 22 then dst171 else dst172) else (if j < 24 then dst173 else dst174))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst175 else (if j < 27 then dst176 else dst177)) else (if j < 29 then dst178 else (if j < 30 then dst179 else dst180))) else (if j < 34 then (if j < 32 then dst181 else (if j < 33 then dst182 else dst183)) else (if j < 35 then dst184 else (if j < 36 then dst185 else dst186)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst187 else (if j < 39 then dst188 else dst189)) else (if j < 41 then dst190 else (if j < 42 then dst191 else dst192))) else (if j < 46 then (if j < 44 then dst193 else (if j < 45 then dst194 else dst195)) else (if j < 48 then (if j < 47 then dst196 else dst197) else (if j < 49 then dst198 else dst199))))))

def caseB3 (i : Fin 50) : Cases := ⟨150 + i.val,by have := i.isLt; omega⟩
lemma tableB3_valid (i : Fin 50) :
    (lookupB3 i.val).Valid (srcTableB3 i.val) (dstTableB3 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data150
  · exact valid_data151
  · exact valid_data152
  · exact valid_data153
  · exact valid_data154
  · exact valid_data155
  · exact valid_data156
  · exact valid_data157
  · exact valid_data158
  · exact valid_data159
  · exact valid_data160
  · exact valid_data161
  · exact valid_data162
  · exact valid_data163
  · exact valid_data164
  · exact valid_data165
  · exact valid_data166
  · exact valid_data167
  · exact valid_data168
  · exact valid_data169
  · exact valid_data170
  · exact valid_data171
  · exact valid_data172
  · exact valid_data173
  · exact valid_data174
  · exact valid_data175
  · exact valid_data176
  · exact valid_data177
  · exact valid_data178
  · exact valid_data179
  · exact valid_data180
  · exact valid_data181
  · exact valid_data182
  · exact valid_data183
  · exact valid_data184
  · exact valid_data185
  · exact valid_data186
  · exact valid_data187
  · exact valid_data188
  · exact valid_data189
  · exact valid_data190
  · exact valid_data191
  · exact valid_data192
  · exact valid_data193
  · exact valid_data194
  · exact valid_data195
  · exact valid_data196
  · exact valid_data197
  · exact valid_data198
  · exact valid_data199

lemma srcB3_row : ∀ (i : Fin 50) (e : E),
    srcTableB3 i.val e = caseSource (caseB3 i) e := by decide +kernel

lemma dstB3_row : ∀ (i : Fin 50) (e : E),
    dstTableB3 i.val e = caseTarget (caseB3 i) e := by decide +kernel

lemma sizeB3 : ∀ i : Fin 50, (lookupB3 i.val).size ≤ 5 →
    (lookupB3 i.val).size = 2 ∧
      (⟨caseKey (caseB3 i),caseKey_lt (caseB3 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB3 (i : Fin 50) : Certificate (caseB3 i) := by
  refine ⟨lookupB3 i.val,?_,sizeB3 i⟩
  have hv := tableB3_valid i
  rw [funext (srcB3_row i),funext (dstB3_row i)] at hv
  exact hv
lemma certificateInterval3 : FiniteIntervals.Covers CertificateAt 150 200 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 150 50 (fun i _ => certificateB3 i)
#print axioms certificateInterval3
end Erdos184Work.FiveRows4

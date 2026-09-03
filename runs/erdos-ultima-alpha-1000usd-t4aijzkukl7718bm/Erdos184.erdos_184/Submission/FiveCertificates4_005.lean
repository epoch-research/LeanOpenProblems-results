import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src250 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst250 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle250_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle250_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle250_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle250_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle250_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle250_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def data250 : PartitionData E W := ⟨6,![cycle250_0,cycle250_1,cycle250_2,cycle250_3,cycle250_4,cycle250_5]⟩
lemma valid_data250 : data250.Valid src250 dst250 Finset.univ := by decide +kernel

def src251 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst251 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle251_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle251_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle251_2 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle251_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle251_4 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle251_5 : CycleData E W := ⟨4,![11,18,17,25,21,15],![4,26,16,38,8,28]⟩
def data251 : PartitionData E W := ⟨6,![cycle251_0,cycle251_1,cycle251_2,cycle251_3,cycle251_4,cycle251_5]⟩
lemma valid_data251 : data251.Valid src251 dst251 Finset.univ := by decide +kernel

def src252 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst252 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle252_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle252_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle252_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle252_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle252_4 : CycleData E W := ⟨3,![11,12,9,23,15],![4,26,14,18,28]⟩
def cycle252_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data252 : PartitionData E W := ⟨6,![cycle252_0,cycle252_1,cycle252_2,cycle252_3,cycle252_4,cycle252_5]⟩
lemma valid_data252 : data252.Valid src252 dst252 Finset.univ := by decide +kernel

def src253 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst253 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle253_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle253_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle253_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle253_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle253_4 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle253_5 : CycleData E W := ⟨4,![11,18,19,25,21,15],![4,26,16,39,8,28]⟩
def data253 : PartitionData E W := ⟨6,![cycle253_0,cycle253_1,cycle253_2,cycle253_3,cycle253_4,cycle253_5]⟩
lemma valid_data253 : data253.Valid src253 dst253 Finset.univ := by decide +kernel

def src254 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst254 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle254_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle254_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle254_2 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle254_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle254_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle254_5 : CycleData E W := ⟨3,![11,17,25,21,15],![4,26,38,8,28]⟩
def data254 : PartitionData E W := ⟨6,![cycle254_0,cycle254_1,cycle254_2,cycle254_3,cycle254_4,cycle254_5]⟩
lemma valid_data254 : data254.Valid src254 dst254 Finset.univ := by decide +kernel

def src255 : E → W := ![2,4,8,3,5,6,2,3,16,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst255 : E → W := ![4,8,3,5,6,2,3,16,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle255_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle255_1 : CycleData E W := ⟨2,![3,13,8,7],![3,5,14,16]⟩
def cycle255_2 : CycleData E W := ⟨3,![5,4,14,23,10],![2,6,5,28,18]⟩
def cycle255_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle255_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle255_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data255 : PartitionData E W := ⟨6,![cycle255_0,cycle255_1,cycle255_2,cycle255_3,cycle255_4,cycle255_5]⟩
lemma valid_data255 : data255.Valid src255 dst255 Finset.univ := by decide +kernel

def src256 : E → W := ![2,4,8,3,5,6,2,14,3,16,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst256 : E → W := ![4,8,3,5,6,2,14,3,16,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle256_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle256_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,8,4,26,14]⟩
def cycle256_2 : CycleData E W := ⟨3,![3,12,22,17,8],![3,5,28,38,16]⟩
def cycle256_3 : CycleData E W := ⟨2,![6,13,23,10],![2,14,28,18]⟩
def cycle256_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle256_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data256 : PartitionData E W := ⟨6,![cycle256_0,cycle256_1,cycle256_2,cycle256_3,cycle256_4,cycle256_5]⟩
lemma valid_data256 : data256.Valid src256 dst256 Finset.univ := by decide +kernel

def src257 : E → W := ![2,4,8,3,5,6,2,14,3,16,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst257 : E → W := ![4,8,3,5,6,2,14,3,16,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle257_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle257_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,8,4,26,14]⟩
def cycle257_2 : CycleData E W := ⟨3,![3,12,24,19,8],![3,5,28,39,16]⟩
def cycle257_3 : CycleData E W := ⟨2,![6,13,23,10],![2,14,28,18]⟩
def cycle257_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle257_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data257 : PartitionData E W := ⟨6,![cycle257_0,cycle257_1,cycle257_2,cycle257_3,cycle257_4,cycle257_5]⟩
lemma valid_data257 : data257.Valid src257 dst257 Finset.univ := by decide +kernel

def src258 : E → W := ![2,4,8,3,5,6,2,14,3,18,16,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst258 : E → W := ![4,8,3,5,6,2,14,3,18,16,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle258_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle258_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,8,4,26,14]⟩
def cycle258_2 : CycleData E W := ⟨2,![3,12,23,8],![3,5,28,18]⟩
def cycle258_3 : CycleData E W := ⟨3,![6,13,22,17,10],![2,14,28,38,16]⟩
def cycle258_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle258_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data258 : PartitionData E W := ⟨6,![cycle258_0,cycle258_1,cycle258_2,cycle258_3,cycle258_4,cycle258_5]⟩
lemma valid_data258 : data258.Valid src258 dst258 Finset.univ := by decide +kernel

def src259 : E → W := ![2,4,8,3,5,6,2,14,3,18,16,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst259 : E → W := ![4,8,3,5,6,2,14,3,18,16,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle259_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle259_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,8,4,26,14]⟩
def cycle259_2 : CycleData E W := ⟨2,![3,12,23,8],![3,5,28,18]⟩
def cycle259_3 : CycleData E W := ⟨3,![6,13,24,19,10],![2,14,28,39,16]⟩
def cycle259_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle259_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data259 : PartitionData E W := ⟨6,![cycle259_0,cycle259_1,cycle259_2,cycle259_3,cycle259_4,cycle259_5]⟩
lemma valid_data259 : data259.Valid src259 dst259 Finset.univ := by decide +kernel

def src260 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,16,38,26,39,8,38,18,28,39]
def dst260 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle260_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle260_1 : CycleData E W := ⟨2,![1,21,18,15],![4,8,38,26]⟩
def cycle260_2 : CycleData E W := ⟨3,![2,25,20,16,8],![3,8,39,6,16]⟩
def cycle260_3 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle260_4 : CycleData E W := ⟨3,![6,7,17,22,10],![2,14,16,38,18]⟩
def cycle260_5 : CycleData E W := ⟨2,![13,24,19,14],![14,28,39,26]⟩
def data260 : PartitionData E W := ⟨6,![cycle260_0,cycle260_1,cycle260_2,cycle260_3,cycle260_4,cycle260_5]⟩
lemma valid_data260 : data260.Valid src260 dst260 Finset.univ := by decide +kernel

def src261 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,16,38,26,39,8,38,28,18,39]
def dst261 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle261_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle261_1 : CycleData E W := ⟨2,![1,21,18,15],![4,8,38,26]⟩
def cycle261_2 : CycleData E W := ⟨3,![2,25,20,16,8],![3,8,39,6,16]⟩
def cycle261_3 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle261_4 : CycleData E W := ⟨3,![6,14,19,24,10],![2,14,26,39,18]⟩
def cycle261_5 : CycleData E W := ⟨2,![7,17,22,13],![14,16,38,28]⟩
def data261 : PartitionData E W := ⟨6,![cycle261_0,cycle261_1,cycle261_2,cycle261_3,cycle261_4,cycle261_5]⟩
lemma valid_data261 : data261.Valid src261 dst261 Finset.univ := by decide +kernel

def src262 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,16,39,26,38,8,38,18,28,39]
def dst262 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle262_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle262_1 : CycleData E W := ⟨2,![1,21,19,15],![4,8,38,26]⟩
def cycle262_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,39,16]⟩
def cycle262_3 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle262_4 : CycleData E W := ⟨4,![6,7,16,20,22,10],![2,14,16,6,38,18]⟩
def cycle262_5 : CycleData E W := ⟨2,![13,24,18,14],![14,28,39,26]⟩
def data262 : PartitionData E W := ⟨6,![cycle262_0,cycle262_1,cycle262_2,cycle262_3,cycle262_4,cycle262_5]⟩
lemma valid_data262 : data262.Valid src262 dst262 Finset.univ := by decide +kernel

def src263 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,16,39,26,38,8,38,28,18,39]
def dst263 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle263_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle263_1 : CycleData E W := ⟨2,![1,21,19,15],![4,8,38,26]⟩
def cycle263_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,39,16]⟩
def cycle263_3 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle263_4 : CycleData E W := ⟨3,![6,14,18,24,10],![2,14,26,39,18]⟩
def cycle263_5 : CycleData E W := ⟨3,![16,7,13,22,20],![6,16,14,28,38]⟩
def data263 : PartitionData E W := ⟨6,![cycle263_0,cycle263_1,cycle263_2,cycle263_3,cycle263_4,cycle263_5]⟩
lemma valid_data263 : data263.Valid src263 dst263 Finset.univ := by decide +kernel

def src264 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,16,26,39,8,18,38,28,39]
def dst264 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle264_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle264_1 : CycleData E W := ⟨2,![1,25,19,15],![4,8,39,26]⟩
def cycle264_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle264_3 : CycleData E W := ⟨3,![3,12,13,7,8],![3,5,28,14,16]⟩
def cycle264_4 : CycleData E W := ⟨4,![6,14,18,17,22,10],![2,14,26,16,38,18]⟩
def cycle264_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data264 : PartitionData E W := ⟨6,![cycle264_0,cycle264_1,cycle264_2,cycle264_3,cycle264_4,cycle264_5]⟩
lemma valid_data264 : data264.Valid src264 dst264 Finset.univ := by decide +kernel

def src265 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,16,26,39,8,18,39,28,38]
def dst265 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle265_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle265_1 : CycleData E W := ⟨3,![1,21,22,19,15],![4,8,18,39,26]⟩
def cycle265_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,38,16]⟩
def cycle265_3 : CycleData E W := ⟨4,![6,13,12,3,9,10],![2,14,28,5,3,18]⟩
def cycle265_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle265_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data265 : PartitionData E W := ⟨6,![cycle265_0,cycle265_1,cycle265_2,cycle265_3,cycle265_4,cycle265_5]⟩
lemma valid_data265 : data265.Valid src265 dst265 Finset.univ := by decide +kernel

def src266 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst266 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle266_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle266_1 : CycleData E W := ⟨3,![2,1,15,18,8],![3,8,4,26,16]⟩
def cycle266_2 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle266_3 : CycleData E W := ⟨3,![6,14,19,24,10],![2,14,26,39,18]⟩
def cycle266_4 : CycleData E W := ⟨2,![7,17,22,13],![14,16,38,28]⟩
def cycle266_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data266 : PartitionData E W := ⟨6,![cycle266_0,cycle266_1,cycle266_2,cycle266_3,cycle266_4,cycle266_5]⟩
lemma valid_data266 : data266.Valid src266 dst266 Finset.univ := by decide +kernel

def src267 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,26,16,39,8,18,38,28,39]
def dst267 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle267_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle267_1 : CycleData E W := ⟨3,![1,21,22,17,15],![4,8,18,38,26]⟩
def cycle267_2 : CycleData E W := ⟨2,![2,25,19,8],![3,8,39,16]⟩
def cycle267_3 : CycleData E W := ⟨4,![6,13,12,3,9,10],![2,14,28,5,3,18]⟩
def cycle267_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle267_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data267 : PartitionData E W := ⟨6,![cycle267_0,cycle267_1,cycle267_2,cycle267_3,cycle267_4,cycle267_5]⟩
lemma valid_data267 : data267.Valid src267 dst267 Finset.univ := by decide +kernel

def src268 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,26,16,39,8,18,39,28,38]
def dst268 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle268_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle268_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,38,26]⟩
def cycle268_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle268_3 : CycleData E W := ⟨3,![3,12,13,7,8],![3,5,28,14,16]⟩
def cycle268_4 : CycleData E W := ⟨4,![6,14,18,19,22,10],![2,14,26,16,39,18]⟩
def cycle268_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data268 : PartitionData E W := ⟨6,![cycle268_0,cycle268_1,cycle268_2,cycle268_3,cycle268_4,cycle268_5]⟩
lemma valid_data268 : data268.Valid src268 dst268 Finset.univ := by decide +kernel

def src269 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst269 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle269_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle269_1 : CycleData E W := ⟨3,![2,1,15,18,8],![3,8,4,26,16]⟩
def cycle269_2 : CycleData E W := ⟨2,![3,12,23,9],![3,5,28,18]⟩
def cycle269_3 : CycleData E W := ⟨3,![6,14,17,22,10],![2,14,26,38,18]⟩
def cycle269_4 : CycleData E W := ⟨2,![7,19,24,13],![14,16,39,28]⟩
def cycle269_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data269 : PartitionData E W := ⟨6,![cycle269_0,cycle269_1,cycle269_2,cycle269_3,cycle269_4,cycle269_5]⟩
lemma valid_data269 : data269.Valid src269 dst269 Finset.univ := by decide +kernel

def src270 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,26,38,39,8,38,18,28,39]
def dst270 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,26,38,39,6,38,18,28,39,8]
def cycle270_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,8,3,18]⟩
def cycle270_1 : CycleData E W := ⟨2,![3,4,16,8],![3,5,6,16]⟩
def cycle270_2 : CycleData E W := ⟨3,![5,20,24,12,6],![2,6,39,28,14]⟩
def cycle270_3 : CycleData E W := ⟨2,![11,7,17,15],![4,14,16,26]⟩
def cycle270_4 : CycleData E W := ⟨3,![13,23,22,18,14],![5,28,18,38,26]⟩
def cycle270_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data270 : PartitionData E W := ⟨6,![cycle270_0,cycle270_1,cycle270_2,cycle270_3,cycle270_4,cycle270_5]⟩
lemma valid_data270 : data270.Valid src270 dst270 Finset.univ := by decide +kernel

def src271 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,26,39,38,8,38,28,18,39]
def dst271 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,26,39,38,6,38,28,18,39,8]
def cycle271_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,8,3,18]⟩
def cycle271_1 : CycleData E W := ⟨2,![3,4,16,8],![3,5,6,16]⟩
def cycle271_2 : CycleData E W := ⟨3,![5,20,22,12,6],![2,6,38,28,14]⟩
def cycle271_3 : CycleData E W := ⟨2,![11,7,17,15],![4,14,16,26]⟩
def cycle271_4 : CycleData E W := ⟨3,![13,23,24,18,14],![5,28,18,39,26]⟩
def cycle271_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data271 : PartitionData E W := ⟨6,![cycle271_0,cycle271_1,cycle271_2,cycle271_3,cycle271_4,cycle271_5]⟩
lemma valid_data271 : data271.Valid src271 dst271 Finset.univ := by decide +kernel

def src272 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,28,38,18,39]
def dst272 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,28,38,18,39,8]
def cycle272_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle272_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle272_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle272_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle272_4 : CycleData E W := ⟨2,![8,17,23,9],![3,16,38,18]⟩
def cycle272_5 : CycleData E W := ⟨3,![21,22,18,19,25],![8,28,38,26,39]⟩
def data272 : PartitionData E W := ⟨6,![cycle272_0,cycle272_1,cycle272_2,cycle272_3,cycle272_4,cycle272_5]⟩
lemma valid_data272 : data272.Valid src272 dst272 Finset.univ := by decide +kernel

def src273 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,28,39,18,38]
def dst273 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,28,39,18,38,8]
def cycle273_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle273_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle273_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle273_3 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle273_4 : CycleData E W := ⟨2,![8,17,24,9],![3,16,38,18]⟩
def cycle273_5 : CycleData E W := ⟨3,![21,22,19,18,25],![8,28,39,26,38]⟩
def data273 : PartitionData E W := ⟨6,![cycle273_0,cycle273_1,cycle273_2,cycle273_3,cycle273_4,cycle273_5]⟩
lemma valid_data273 : data273.Valid src273 dst273 Finset.univ := by decide +kernel

def src274 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,38,18,28,39]
def dst274 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle274_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle274_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle274_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle274_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle274_4 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def cycle274_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data274 : PartitionData E W := ⟨6,![cycle274_0,cycle274_1,cycle274_2,cycle274_3,cycle274_4,cycle274_5]⟩
lemma valid_data274 : data274.Valid src274 dst274 Finset.univ := by decide +kernel

def src275 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,38,28,18,39]
def dst275 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle275_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle275_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle275_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle275_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle275_4 : CycleData E W := ⟨3,![8,17,22,23,9],![3,16,38,28,18]⟩
def cycle275_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data275 : PartitionData E W := ⟨6,![cycle275_0,cycle275_1,cycle275_2,cycle275_3,cycle275_4,cycle275_5]⟩
lemma valid_data275 : data275.Valid src275 dst275 Finset.univ := by decide +kernel

def src276 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,38,39,26,8,38,28,18,39]
def dst276 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,38,39,26,6,38,28,18,39,8]
def cycle276_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,8,3,18]⟩
def cycle276_1 : CycleData E W := ⟨2,![3,4,16,8],![3,5,6,16]⟩
def cycle276_2 : CycleData E W := ⟨3,![5,20,15,11,6],![2,6,26,4,14]⟩
def cycle276_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle276_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle276_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data276 : PartitionData E W := ⟨6,![cycle276_0,cycle276_1,cycle276_2,cycle276_3,cycle276_4,cycle276_5]⟩
lemma valid_data276 : data276.Valid src276 dst276 Finset.univ := by decide +kernel

def src277 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,28,38,18,39]
def dst277 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,28,38,18,39,8]
def cycle277_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle277_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle277_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle277_3 : CycleData E W := ⟨2,![5,20,23,10],![2,6,38,18]⟩
def cycle277_4 : CycleData E W := ⟨2,![8,17,24,9],![3,16,39,18]⟩
def cycle277_5 : CycleData E W := ⟨3,![21,22,19,18,25],![8,28,38,26,39]⟩
def data277 : PartitionData E W := ⟨6,![cycle277_0,cycle277_1,cycle277_2,cycle277_3,cycle277_4,cycle277_5]⟩
lemma valid_data277 : data277.Valid src277 dst277 Finset.univ := by decide +kernel

def src278 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,28,39,18,38]
def dst278 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,28,39,18,38,8]
def cycle278_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle278_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle278_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle278_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,38,18]⟩
def cycle278_4 : CycleData E W := ⟨2,![8,17,23,9],![3,16,39,18]⟩
def cycle278_5 : CycleData E W := ⟨3,![21,22,18,19,25],![8,28,39,26,38]⟩
def data278 : PartitionData E W := ⟨6,![cycle278_0,cycle278_1,cycle278_2,cycle278_3,cycle278_4,cycle278_5]⟩
lemma valid_data278 : data278.Valid src278 dst278 Finset.univ := by decide +kernel

def src279 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,38,18,28,39]
def dst279 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle279_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle279_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle279_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle279_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle279_4 : CycleData E W := ⟨3,![8,17,24,23,9],![3,16,39,28,18]⟩
def cycle279_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data279 : PartitionData E W := ⟨6,![cycle279_0,cycle279_1,cycle279_2,cycle279_3,cycle279_4,cycle279_5]⟩
lemma valid_data279 : data279.Valid src279 dst279 Finset.univ := by decide +kernel

def src280 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,38,28,18,39]
def dst280 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle280_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle280_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle280_2 : CycleData E W := ⟨3,![4,16,7,12,13],![5,6,16,14,28]⟩
def cycle280_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle280_4 : CycleData E W := ⟨2,![8,17,24,9],![3,16,39,18]⟩
def cycle280_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data280 : PartitionData E W := ⟨6,![cycle280_0,cycle280_1,cycle280_2,cycle280_3,cycle280_4,cycle280_5]⟩
lemma valid_data280 : data280.Valid src280 dst280 Finset.univ := by decide +kernel

def src281 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,16,39,38,26,8,38,18,28,39]
def dst281 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,16,39,38,26,6,38,18,28,39,8]
def cycle281_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,8,3,18]⟩
def cycle281_1 : CycleData E W := ⟨2,![3,4,16,8],![3,5,6,16]⟩
def cycle281_2 : CycleData E W := ⟨3,![5,20,15,11,6],![2,6,26,4,14]⟩
def cycle281_3 : CycleData E W := ⟨2,![7,17,24,12],![14,16,39,28]⟩
def cycle281_4 : CycleData E W := ⟨3,![13,23,22,19,14],![5,28,18,38,26]⟩
def cycle281_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data281 : PartitionData E W := ⟨6,![cycle281_0,cycle281_1,cycle281_2,cycle281_3,cycle281_4,cycle281_5]⟩
lemma valid_data281 : data281.Valid src281 dst281 Finset.univ := by decide +kernel

def src282 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,16,38,39,8,38,28,18,39]
def dst282 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,16,38,39,6,38,28,18,39,8]
def cycle282_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle282_1 : CycleData E W := ⟨3,![2,1,15,17,8],![3,8,4,26,16]⟩
def cycle282_2 : CycleData E W := ⟨2,![3,13,23,9],![3,5,28,18]⟩
def cycle282_3 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle282_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle282_5 : CycleData E W := ⟨2,![7,18,22,12],![14,16,38,28]⟩
def cycle282_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data282 : PartitionData E W := ⟨7,![cycle282_0,cycle282_1,cycle282_2,cycle282_3,cycle282_4,cycle282_5,cycle282_6]⟩
lemma valid_data282 : data282.Valid src282 dst282 Finset.univ := by decide +kernel

def src283 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,16,39,38,8,38,18,28,39]
def dst283 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,16,39,38,6,38,18,28,39,8]
def cycle283_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle283_1 : CycleData E W := ⟨3,![2,1,15,17,8],![3,8,4,26,16]⟩
def cycle283_2 : CycleData E W := ⟨2,![3,13,23,9],![3,5,28,18]⟩
def cycle283_3 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle283_4 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle283_5 : CycleData E W := ⟨2,![7,18,24,12],![14,16,39,28]⟩
def cycle283_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data283 : PartitionData E W := ⟨7,![cycle283_0,cycle283_1,cycle283_2,cycle283_3,cycle283_4,cycle283_5,cycle283_6]⟩
lemma valid_data283 : data283.Valid src283 dst283 Finset.univ := by decide +kernel

def src284 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,18,38,28,39]
def dst284 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,18,38,28,39,8]
def cycle284_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle284_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle284_2 : CycleData E W := ⟨3,![4,16,17,23,13],![5,6,26,38,28]⟩
def cycle284_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle284_4 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle284_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def data284 : PartitionData E W := ⟨6,![cycle284_0,cycle284_1,cycle284_2,cycle284_3,cycle284_4,cycle284_5]⟩
lemma valid_data284 : data284.Valid src284 dst284 Finset.univ := by decide +kernel

def src285 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,18,39,28,38]
def dst285 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,18,39,28,38,8]
def cycle285_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle285_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,38,26]⟩
def cycle285_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle285_3 : CycleData E W := ⟨3,![3,13,12,7,8],![3,5,28,14,16]⟩
def cycle285_4 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle285_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle285_6 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data285 : PartitionData E W := ⟨7,![cycle285_0,cycle285_1,cycle285_2,cycle285_3,cycle285_4,cycle285_5,cycle285_6]⟩
lemma valid_data285 : data285.Valid src285 dst285 Finset.univ := by decide +kernel

def src286 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst286 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle286_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle286_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle286_2 : CycleData E W := ⟨3,![5,4,13,23,10],![2,6,5,28,18]⟩
def cycle286_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle286_4 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def cycle286_5 : CycleData E W := ⟨3,![16,17,21,25,20],![6,26,38,8,39]⟩
def data286 : PartitionData E W := ⟨6,![cycle286_0,cycle286_1,cycle286_2,cycle286_3,cycle286_4,cycle286_5]⟩
lemma valid_data286 : data286.Valid src286 dst286 Finset.univ := by decide +kernel

def src287 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst287 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle287_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle287_1 : CycleData E W := ⟨2,![1,21,17,15],![4,8,38,26]⟩
def cycle287_2 : CycleData E W := ⟨2,![2,25,19,8],![3,8,39,16]⟩
def cycle287_3 : CycleData E W := ⟨2,![3,13,23,9],![3,5,28,18]⟩
def cycle287_4 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle287_5 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle287_6 : CycleData E W := ⟨2,![7,18,22,12],![14,16,38,28]⟩
def data287 : PartitionData E W := ⟨7,![cycle287_0,cycle287_1,cycle287_2,cycle287_3,cycle287_4,cycle287_5,cycle287_6]⟩
lemma valid_data287 : data287.Valid src287 dst287 Finset.univ := by decide +kernel

def src288 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,18,38,28,39]
def dst288 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,18,38,28,39,8]
def cycle288_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle288_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,39,26]⟩
def cycle288_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle288_3 : CycleData E W := ⟨3,![3,13,12,7,8],![3,5,28,14,16]⟩
def cycle288_4 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle288_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle288_6 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data288 : PartitionData E W := ⟨7,![cycle288_0,cycle288_1,cycle288_2,cycle288_3,cycle288_4,cycle288_5,cycle288_6]⟩
lemma valid_data288 : data288.Valid src288 dst288 Finset.univ := by decide +kernel

def src289 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,18,39,28,38]
def dst289 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,18,39,28,38,8]
def cycle289_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle289_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle289_2 : CycleData E W := ⟨3,![4,16,17,23,13],![5,6,26,39,28]⟩
def cycle289_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,38,8,18]⟩
def cycle289_4 : CycleData E W := ⟨2,![7,19,24,12],![14,16,38,28]⟩
def cycle289_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,39,18]⟩
def data289 : PartitionData E W := ⟨6,![cycle289_0,cycle289_1,cycle289_2,cycle289_3,cycle289_4,cycle289_5]⟩
lemma valid_data289 : data289.Valid src289 dst289 Finset.univ := by decide +kernel

def src290 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst290 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle290_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle290_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,39,26]⟩
def cycle290_2 : CycleData E W := ⟨2,![2,21,19,8],![3,8,38,16]⟩
def cycle290_3 : CycleData E W := ⟨2,![3,13,23,9],![3,5,28,18]⟩
def cycle290_4 : CycleData E W := ⟨1,![4,16,14],![5,6,26]⟩
def cycle290_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle290_6 : CycleData E W := ⟨2,![7,18,24,12],![14,16,39,28]⟩
def data290 : PartitionData E W := ⟨7,![cycle290_0,cycle290_1,cycle290_2,cycle290_3,cycle290_4,cycle290_5,cycle290_6]⟩
lemma valid_data290 : data290.Valid src290 dst290 Finset.univ := by decide +kernel

def src291 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst291 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle291_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle291_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle291_2 : CycleData E W := ⟨2,![4,20,22,13],![5,6,38,28]⟩
def cycle291_3 : CycleData E W := ⟨3,![5,16,17,24,10],![2,6,26,39,18]⟩
def cycle291_4 : CycleData E W := ⟨3,![8,7,12,23,9],![3,16,14,28,18]⟩
def cycle291_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data291 : PartitionData E W := ⟨6,![cycle291_0,cycle291_1,cycle291_2,cycle291_3,cycle291_4,cycle291_5]⟩
lemma valid_data291 : data291.Valid src291 dst291 Finset.univ := by decide +kernel

def src292 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,28,38,39]
def dst292 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,28,38,39,8]
def cycle292_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle292_1 : CycleData E W := ⟨2,![1,25,19,15],![4,8,39,26]⟩
def cycle292_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle292_3 : CycleData E W := ⟨2,![3,14,18,8],![3,5,26,16]⟩
def cycle292_4 : CycleData E W := ⟨3,![5,4,13,22,10],![2,6,5,28,18]⟩
def cycle292_5 : CycleData E W := ⟨2,![7,17,23,12],![14,16,38,28]⟩
def cycle292_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data292 : PartitionData E W := ⟨7,![cycle292_0,cycle292_1,cycle292_2,cycle292_3,cycle292_4,cycle292_5,cycle292_6]⟩
lemma valid_data292 : data292.Valid src292 dst292 Finset.univ := by decide +kernel

def src293 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,38,28,39]
def dst293 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle293_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle293_1 : CycleData E W := ⟨2,![1,25,19,15],![4,8,39,26]⟩
def cycle293_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle293_3 : CycleData E W := ⟨2,![3,14,18,8],![3,5,26,16]⟩
def cycle293_4 : CycleData E W := ⟨2,![4,20,24,13],![5,6,39,28]⟩
def cycle293_5 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle293_6 : CycleData E W := ⟨2,![7,17,23,12],![14,16,38,28]⟩
def data293 : PartitionData E W := ⟨7,![cycle293_0,cycle293_1,cycle293_2,cycle293_3,cycle293_4,cycle293_5,cycle293_6]⟩
lemma valid_data293 : data293.Valid src293 dst293 Finset.univ := by decide +kernel

def src294 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,28,38]
def dst294 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle294_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle294_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle294_2 : CycleData E W := ⟨2,![4,20,23,13],![5,6,39,28]⟩
def cycle294_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle294_4 : CycleData E W := ⟨2,![7,17,24,12],![14,16,38,28]⟩
def cycle294_5 : CycleData E W := ⟨3,![8,18,19,22,9],![3,16,26,39,18]⟩
def data294 : PartitionData E W := ⟨6,![cycle294_0,cycle294_1,cycle294_2,cycle294_3,cycle294_4,cycle294_5]⟩
lemma valid_data294 : data294.Valid src294 dst294 Finset.univ := by decide +kernel

def src295 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,38,28]
def dst295 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,38,28,8]
def cycle295_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle295_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle295_2 : CycleData E W := ⟨2,![4,16,24,13],![5,6,38,28]⟩
def cycle295_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle295_4 : CycleData E W := ⟨4,![8,7,12,25,21,9],![3,16,14,28,8,18]⟩
def cycle295_5 : CycleData E W := ⟨2,![17,23,19,18],![16,38,39,26]⟩
def data295 : PartitionData E W := ⟨6,![cycle295_0,cycle295_1,cycle295_2,cycle295_3,cycle295_4,cycle295_5]⟩
lemma valid_data295 : data295.Valid src295 dst295 Finset.univ := by decide +kernel

def src296 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,28,18,39,38]
def dst296 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,28,18,39,38,8]
def cycle296_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle296_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle296_2 : CycleData E W := ⟨3,![5,4,13,22,10],![2,6,5,28,18]⟩
def cycle296_3 : CycleData E W := ⟨3,![21,12,7,17,25],![8,28,14,16,38]⟩
def cycle296_4 : CycleData E W := ⟨3,![8,18,19,23,9],![3,16,26,39,18]⟩
def cycle296_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data296 : PartitionData E W := ⟨6,![cycle296_0,cycle296_1,cycle296_2,cycle296_3,cycle296_4,cycle296_5]⟩
lemma valid_data296 : data296.Valid src296 dst296 Finset.univ := by decide +kernel

def src297 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst297 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle297_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle297_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle297_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle297_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle297_4 : CycleData E W := ⟨4,![21,12,7,18,19,25],![8,28,14,16,26,39]⟩
def cycle297_5 : CycleData E W := ⟨2,![8,17,23,9],![3,16,38,18]⟩
def data297 : PartitionData E W := ⟨6,![cycle297_0,cycle297_1,cycle297_2,cycle297_3,cycle297_4,cycle297_5]⟩
lemma valid_data297 : data297.Valid src297 dst297 Finset.univ := by decide +kernel

def src298 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst298 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle298_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle298_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle298_2 : CycleData E W := ⟨2,![4,20,22,13],![5,6,39,28]⟩
def cycle298_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle298_4 : CycleData E W := ⟨3,![21,12,7,17,25],![8,28,14,16,38]⟩
def cycle298_5 : CycleData E W := ⟨3,![8,18,19,23,9],![3,16,26,39,18]⟩
def data298 : PartitionData E W := ⟨6,![cycle298_0,cycle298_1,cycle298_2,cycle298_3,cycle298_4,cycle298_5]⟩
lemma valid_data298 : data298.Valid src298 dst298 Finset.univ := by decide +kernel

def src299 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst299 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle299_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle299_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle299_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle299_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle299_4 : CycleData E W := ⟨3,![8,7,12,23,9],![3,16,14,28,18]⟩
def cycle299_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data299 : PartitionData E W := ⟨6,![cycle299_0,cycle299_1,cycle299_2,cycle299_3,cycle299_4,cycle299_5]⟩
lemma valid_data299 : data299.Valid src299 dst299 Finset.univ := by decide +kernel

def lookupB5 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data250 else (if j < 2 then data251 else data252)) else (if j < 4 then data253 else (if j < 5 then data254 else data255))) else (if j < 9 then (if j < 7 then data256 else (if j < 8 then data257 else data258)) else (if j < 10 then data259 else (if j < 11 then data260 else data261)))) else (if j < 18 then (if j < 15 then (if j < 13 then data262 else (if j < 14 then data263 else data264)) else (if j < 16 then data265 else (if j < 17 then data266 else data267))) else (if j < 21 then (if j < 19 then data268 else (if j < 20 then data269 else data270)) else (if j < 23 then (if j < 22 then data271 else data272) else (if j < 24 then data273 else data274))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data275 else (if j < 27 then data276 else data277)) else (if j < 29 then data278 else (if j < 30 then data279 else data280))) else (if j < 34 then (if j < 32 then data281 else (if j < 33 then data282 else data283)) else (if j < 35 then data284 else (if j < 36 then data285 else data286)))) else (if j < 43 then (if j < 40 then (if j < 38 then data287 else (if j < 39 then data288 else data289)) else (if j < 41 then data290 else (if j < 42 then data291 else data292))) else (if j < 46 then (if j < 44 then data293 else (if j < 45 then data294 else data295)) else (if j < 48 then (if j < 47 then data296 else data297) else (if j < 49 then data298 else data299))))))

def srcTableB5 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src250 else (if j < 2 then src251 else src252)) else (if j < 4 then src253 else (if j < 5 then src254 else src255))) else (if j < 9 then (if j < 7 then src256 else (if j < 8 then src257 else src258)) else (if j < 10 then src259 else (if j < 11 then src260 else src261)))) else (if j < 18 then (if j < 15 then (if j < 13 then src262 else (if j < 14 then src263 else src264)) else (if j < 16 then src265 else (if j < 17 then src266 else src267))) else (if j < 21 then (if j < 19 then src268 else (if j < 20 then src269 else src270)) else (if j < 23 then (if j < 22 then src271 else src272) else (if j < 24 then src273 else src274))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src275 else (if j < 27 then src276 else src277)) else (if j < 29 then src278 else (if j < 30 then src279 else src280))) else (if j < 34 then (if j < 32 then src281 else (if j < 33 then src282 else src283)) else (if j < 35 then src284 else (if j < 36 then src285 else src286)))) else (if j < 43 then (if j < 40 then (if j < 38 then src287 else (if j < 39 then src288 else src289)) else (if j < 41 then src290 else (if j < 42 then src291 else src292))) else (if j < 46 then (if j < 44 then src293 else (if j < 45 then src294 else src295)) else (if j < 48 then (if j < 47 then src296 else src297) else (if j < 49 then src298 else src299))))))

def dstTableB5 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst250 else (if j < 2 then dst251 else dst252)) else (if j < 4 then dst253 else (if j < 5 then dst254 else dst255))) else (if j < 9 then (if j < 7 then dst256 else (if j < 8 then dst257 else dst258)) else (if j < 10 then dst259 else (if j < 11 then dst260 else dst261)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst262 else (if j < 14 then dst263 else dst264)) else (if j < 16 then dst265 else (if j < 17 then dst266 else dst267))) else (if j < 21 then (if j < 19 then dst268 else (if j < 20 then dst269 else dst270)) else (if j < 23 then (if j < 22 then dst271 else dst272) else (if j < 24 then dst273 else dst274))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst275 else (if j < 27 then dst276 else dst277)) else (if j < 29 then dst278 else (if j < 30 then dst279 else dst280))) else (if j < 34 then (if j < 32 then dst281 else (if j < 33 then dst282 else dst283)) else (if j < 35 then dst284 else (if j < 36 then dst285 else dst286)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst287 else (if j < 39 then dst288 else dst289)) else (if j < 41 then dst290 else (if j < 42 then dst291 else dst292))) else (if j < 46 then (if j < 44 then dst293 else (if j < 45 then dst294 else dst295)) else (if j < 48 then (if j < 47 then dst296 else dst297) else (if j < 49 then dst298 else dst299))))))

def caseB5 (i : Fin 50) : Cases := ⟨250 + i.val,by have := i.isLt; omega⟩
lemma tableB5_valid (i : Fin 50) :
    (lookupB5 i.val).Valid (srcTableB5 i.val) (dstTableB5 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB5_row : ∀ (i : Fin 50) (e : E),
    srcTableB5 i.val e = caseSource (caseB5 i) e := by decide +kernel

lemma dstB5_row : ∀ (i : Fin 50) (e : E),
    dstTableB5 i.val e = caseTarget (caseB5 i) e := by decide +kernel

lemma sizeB5 : ∀ i : Fin 50, (lookupB5 i.val).size ≤ 5 →
    (lookupB5 i.val).size = 2 ∧
      (⟨caseKey (caseB5 i),caseKey_lt (caseB5 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB5 (i : Fin 50) : Certificate (caseB5 i) := by
  refine ⟨lookupB5 i.val,?_,sizeB5 i⟩
  have hv := tableB5_valid i
  rw [funext (srcB5_row i),funext (dstB5_row i)] at hv
  exact hv
lemma certificateInterval5 : FiniteIntervals.Covers CertificateAt 250 300 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 250 50 (fun i _ => certificateB5 i)
#print axioms certificateInterval5
end Erdos184Work.FiveRows4

import Submission.SixRepresentativeCertificates0Base
namespace Erdos184Work.SixRepresentativeCertificates0
open PureSixRowModel0 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src250 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,20,32,44,58,10,34,58,22,46]
def dst250 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,20,32,44,58,8,34,58,22,46,10]
def cycle250_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle250_1 : CycleData E W := ⟨3,![1,15,6,11,10],![4,6,18,16,30]⟩
def cycle250_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle250_3 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle250_4 : CycleData E W := ⟨3,![7,28,18,17,16],![18,22,46,30,44]⟩
def cycle250_5 : CycleData E W := ⟨2,![20,8,27,24],![8,20,22,58]⟩
def cycle250_6 : CycleData E W := ⟨2,![13,26,23,22],![32,34,58,44]⟩
def data250 : PartitionData E W := ⟨7,![cycle250_0,cycle250_1,cycle250_2,cycle250_3,cycle250_4,cycle250_5,cycle250_6]⟩
lemma valid250 : data250.Valid src250 dst250 Finset.univ := by decide +kernel
lemma src_eq250 : src250 = src (unkey (representativeKey 250)) := by decide +kernel
lemma dst_eq250 : dst250 = dst (unkey (representativeKey 250)) := by decide +kernel
lemma certificate250 : Certificate 250 := by
  refine ⟨data250,?_,?_⟩
  · rw [← src_eq250,← dst_eq250]
    exact valid250
  · decide +kernel

def src251 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,20,32,58,44,10,22,46,58,34]
def dst251 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,20,32,58,44,8,22,46,58,34,10]
def cycle251_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle251_1 : CycleData E W := ⟨3,![1,2,20,21,14],![4,6,8,20,32]⟩
def cycle251_2 : CycleData E W := ⟨4,![3,29,12,6,16,24],![8,10,34,16,18,44]⟩
def cycle251_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle251_4 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle251_5 : CycleData E W := ⟨1,![13,28,22],![32,34,58]⟩
def cycle251_6 : CycleData E W := ⟨2,![17,23,27,18],![30,44,58,46]⟩
def data251 : PartitionData E W := ⟨7,![cycle251_0,cycle251_1,cycle251_2,cycle251_3,cycle251_4,cycle251_5,cycle251_6]⟩
lemma valid251 : data251.Valid src251 dst251 Finset.univ := by decide +kernel
lemma src_eq251 : src251 = src (unkey (representativeKey 251)) := by decide +kernel
lemma dst_eq251 : dst251 = dst (unkey (representativeKey 251)) := by decide +kernel
lemma certificate251 : Certificate 251 := by
  refine ⟨data251,?_,?_⟩
  · rw [← src_eq251,← dst_eq251]
    exact valid251
  · decide +kernel

def src252 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,20,32,58,44,10,34,22,58,46]
def dst252 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,20,32,58,44,8,34,22,58,46,10]
def cycle252_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle252_1 : CycleData E W := ⟨4,![1,19,29,25,13,14],![4,6,46,10,34,32]⟩
def cycle252_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle252_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle252_4 : CycleData E W := ⟨2,![6,7,26,12],![16,18,22,34]⟩
def cycle252_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,32]⟩
def cycle252_6 : CycleData E W := ⟨2,![17,23,28,18],![30,44,58,46]⟩
def data252 : PartitionData E W := ⟨7,![cycle252_0,cycle252_1,cycle252_2,cycle252_3,cycle252_4,cycle252_5,cycle252_6]⟩
lemma valid252 : data252.Valid src252 dst252 Finset.univ := by decide +kernel
lemma src_eq252 : src252 = src (unkey (representativeKey 252)) := by decide +kernel
lemma dst_eq252 : dst252 = dst (unkey (representativeKey 252)) := by decide +kernel
lemma certificate252 : Certificate 252 := by
  refine ⟨data252,?_,?_⟩
  · rw [← src_eq252,← dst_eq252]
    exact valid252
  · decide +kernel

def src253 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,20,32,58,44,10,34,58,22,46]
def dst253 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle253_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle253_1 : CycleData E W := ⟨3,![1,15,6,11,10],![4,6,18,16,30]⟩
def cycle253_2 : CycleData E W := ⟨3,![2,24,17,18,19],![6,8,44,30,46]⟩
def cycle253_3 : CycleData E W := ⟨3,![3,29,28,8,20],![8,10,46,22,20]⟩
def cycle253_4 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle253_5 : CycleData E W := ⟨2,![7,27,23,16],![18,22,58,44]⟩
def cycle253_6 : CycleData E W := ⟨1,![13,26,22],![32,34,58]⟩
def data253 : PartitionData E W := ⟨7,![cycle253_0,cycle253_1,cycle253_2,cycle253_3,cycle253_4,cycle253_5,cycle253_6]⟩
lemma valid253 : data253.Valid src253 dst253 Finset.univ := by decide +kernel
lemma src_eq253 : src253 = src (unkey (representativeKey 253)) := by decide +kernel
lemma dst_eq253 : dst253 = dst (unkey (representativeKey 253)) := by decide +kernel
lemma certificate253 : Certificate 253 := by
  refine ⟨data253,?_,?_⟩
  · rw [← src_eq253,← dst_eq253]
    exact valid253
  · decide +kernel

def src254 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,20,32,58,44,10,46,34,22,58]
def dst254 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,20,32,58,44,8,46,34,22,58,10]
def cycle254_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle254_1 : CycleData E W := ⟨3,![1,19,26,13,14],![4,6,46,34,32]⟩
def cycle254_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle254_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle254_4 : CycleData E W := ⟨2,![6,7,27,12],![16,18,22,34]⟩
def cycle254_5 : CycleData E W := ⟨2,![8,28,22,21],![20,22,58,32]⟩
def cycle254_6 : CycleData E W := ⟨3,![25,18,17,23,29],![10,46,30,44,58]⟩
def data254 : PartitionData E W := ⟨7,![cycle254_0,cycle254_1,cycle254_2,cycle254_3,cycle254_4,cycle254_5,cycle254_6]⟩
lemma valid254 : data254.Valid src254 dst254 Finset.univ := by decide +kernel
lemma src_eq254 : src254 = src (unkey (representativeKey 254)) := by decide +kernel
lemma dst_eq254 : dst254 = dst (unkey (representativeKey 254)) := by decide +kernel
lemma certificate254 : Certificate 254 := by
  refine ⟨data254,?_,?_⟩
  · rw [← src_eq254,← dst_eq254]
    exact valid254
  · decide +kernel

def src255 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,32,20,44,58,10,34,58,22,46]
def dst255 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,32,20,44,58,8,34,58,22,46,10]
def cycle255_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle255_1 : CycleData E W := ⟨3,![1,15,6,11,10],![4,6,18,16,30]⟩
def cycle255_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle255_3 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle255_4 : CycleData E W := ⟨2,![7,8,22,16],![18,22,20,44]⟩
def cycle255_5 : CycleData E W := ⟨2,![20,13,26,24],![8,32,34,58]⟩
def cycle255_6 : CycleData E W := ⟨3,![27,23,17,18,28],![22,58,44,30,46]⟩
def data255 : PartitionData E W := ⟨7,![cycle255_0,cycle255_1,cycle255_2,cycle255_3,cycle255_4,cycle255_5,cycle255_6]⟩
lemma valid255 : data255.Valid src255 dst255 Finset.univ := by decide +kernel
lemma src_eq255 : src255 = src (unkey (representativeKey 255)) := by decide +kernel
lemma dst_eq255 : dst255 = dst (unkey (representativeKey 255)) := by decide +kernel
lemma certificate255 : Certificate 255 := by
  refine ⟨data255,?_,?_⟩
  · rw [← src_eq255,← dst_eq255]
    exact valid255
  · decide +kernel

def src256 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,44,30,46,8,44,20,32,58,10,34,58,22,46]
def dst256 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,44,30,46,6,44,20,32,58,8,34,58,22,46,10]
def cycle256_0 : CycleData E W := ⟨2,![0,14,22,9],![2,4,32,20]⟩
def cycle256_1 : CycleData E W := ⟨3,![1,15,6,11,10],![4,6,18,16,30]⟩
def cycle256_2 : CycleData E W := ⟨3,![2,20,17,18,19],![6,8,44,30,46]⟩
def cycle256_3 : CycleData E W := ⟨3,![3,29,28,27,24],![8,10,46,22,58]⟩
def cycle256_4 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle256_5 : CycleData E W := ⟨2,![7,8,21,16],![18,22,20,44]⟩
def cycle256_6 : CycleData E W := ⟨1,![13,26,23],![32,34,58]⟩
def data256 : PartitionData E W := ⟨7,![cycle256_0,cycle256_1,cycle256_2,cycle256_3,cycle256_4,cycle256_5,cycle256_6]⟩
lemma valid256 : data256.Valid src256 dst256 Finset.univ := by decide +kernel
lemma src_eq256 : src256 = src (unkey (representativeKey 256)) := by decide +kernel
lemma dst_eq256 : dst256 = dst (unkey (representativeKey 256)) := by decide +kernel
lemma certificate256 : Certificate 256 := by
  refine ⟨data256,?_,?_⟩
  · rw [← src_eq256,← dst_eq256]
    exact valid256
  · decide +kernel

def src257 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,46,30,44,8,20,32,44,58,10,22,58,34,46]
def dst257 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,46,30,44,6,20,32,44,58,8,22,58,34,46,10]
def cycle257_0 : CycleData E W := ⟨3,![0,1,15,6,5],![2,4,6,18,16]⟩
def cycle257_1 : CycleData E W := ⟨2,![2,24,23,19],![6,8,58,44]⟩
def cycle257_2 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle257_3 : CycleData E W := ⟨2,![25,7,16,29],![10,22,18,46]⟩
def cycle257_4 : CycleData E W := ⟨3,![8,26,27,13,21],![20,22,58,34,32]⟩
def cycle257_5 : CycleData E W := ⟨2,![10,18,22,14],![4,30,44,32]⟩
def cycle257_6 : CycleData E W := ⟨2,![11,17,28,12],![16,30,46,34]⟩
def data257 : PartitionData E W := ⟨7,![cycle257_0,cycle257_1,cycle257_2,cycle257_3,cycle257_4,cycle257_5,cycle257_6]⟩
lemma valid257 : data257.Valid src257 dst257 Finset.univ := by decide +kernel
lemma src_eq257 : src257 = src (unkey (representativeKey 257)) := by decide +kernel
lemma dst_eq257 : dst257 = dst (unkey (representativeKey 257)) := by decide +kernel
lemma certificate257 : Certificate 257 := by
  refine ⟨data257,?_,?_⟩
  · rw [← src_eq257,← dst_eq257]
    exact valid257
  · decide +kernel

def src258 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,46,30,44,8,20,32,44,58,10,34,22,58,46]
def dst258 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,46,30,44,6,20,32,44,58,8,34,22,58,46,10]
def cycle258_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle258_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,44,32]⟩
def cycle258_2 : CycleData E W := ⟨3,![2,24,27,7,15],![6,8,58,22,18]⟩
def cycle258_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle258_4 : CycleData E W := ⟨3,![25,12,6,16,29],![10,34,16,18,46]⟩
def cycle258_5 : CycleData E W := ⟨2,![8,26,13,21],![20,22,34,32]⟩
def cycle258_6 : CycleData E W := ⟨2,![17,28,23,18],![30,46,58,44]⟩
def data258 : PartitionData E W := ⟨7,![cycle258_0,cycle258_1,cycle258_2,cycle258_3,cycle258_4,cycle258_5,cycle258_6]⟩
lemma valid258 : data258.Valid src258 dst258 Finset.univ := by decide +kernel
lemma src_eq258 : src258 = src (unkey (representativeKey 258)) := by decide +kernel
lemma dst_eq258 : dst258 = dst (unkey (representativeKey 258)) := by decide +kernel
lemma certificate258 : Certificate 258 := by
  refine ⟨data258,?_,?_⟩
  · rw [← src_eq258,← dst_eq258]
    exact valid258
  · decide +kernel

def src259 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,46,30,44,8,20,32,44,58,10,34,58,22,46]
def dst259 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,46,30,44,6,20,32,44,58,8,34,58,22,46,10]
def cycle259_0 : CycleData E W := ⟨3,![0,1,15,6,5],![2,4,6,18,16]⟩
def cycle259_1 : CycleData E W := ⟨2,![2,24,23,19],![6,8,58,44]⟩
def cycle259_2 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle259_3 : CycleData E W := ⟨1,![7,28,16],![18,22,46]⟩
def cycle259_4 : CycleData E W := ⟨3,![8,27,26,13,21],![20,22,58,34,32]⟩
def cycle259_5 : CycleData E W := ⟨2,![10,18,22,14],![4,30,44,32]⟩
def cycle259_6 : CycleData E W := ⟨3,![25,12,11,17,29],![10,34,16,30,46]⟩
def data259 : PartitionData E W := ⟨7,![cycle259_0,cycle259_1,cycle259_2,cycle259_3,cycle259_4,cycle259_5,cycle259_6]⟩
lemma valid259 : data259.Valid src259 dst259 Finset.univ := by decide +kernel
lemma src_eq259 : src259 = src (unkey (representativeKey 259)) := by decide +kernel
lemma dst_eq259 : dst259 = dst (unkey (representativeKey 259)) := by decide +kernel
lemma certificate259 : Certificate 259 := by
  refine ⟨data259,?_,?_⟩
  · rw [← src_eq259,← dst_eq259]
    exact valid259
  · decide +kernel

def src260 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,46,30,44,8,20,44,32,58,10,34,22,58,46]
def dst260 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,46,30,44,6,20,44,32,58,8,34,22,58,46,10]
def cycle260_0 : CycleData E W := ⟨4,![0,1,15,7,8,9],![2,4,6,18,22,20]⟩
def cycle260_1 : CycleData E W := ⟨2,![2,20,21,19],![6,8,20,44]⟩
def cycle260_2 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle260_3 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle260_4 : CycleData E W := ⟨2,![6,16,17,11],![16,18,46,30]⟩
def cycle260_5 : CycleData E W := ⟨2,![10,18,22,14],![4,30,44,32]⟩
def cycle260_6 : CycleData E W := ⟨2,![26,13,23,27],![22,34,32,58]⟩
def data260 : PartitionData E W := ⟨7,![cycle260_0,cycle260_1,cycle260_2,cycle260_3,cycle260_4,cycle260_5,cycle260_6]⟩
lemma valid260 : data260.Valid src260 dst260 Finset.univ := by decide +kernel
lemma src_eq260 : src260 = src (unkey (representativeKey 260)) := by decide +kernel
lemma dst_eq260 : dst260 = dst (unkey (representativeKey 260)) := by decide +kernel
lemma certificate260 : Certificate 260 := by
  refine ⟨data260,?_,?_⟩
  · rw [← src_eq260,← dst_eq260]
    exact valid260
  · decide +kernel

def src261 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,16,34,32,6,18,46,30,44,8,32,20,44,58,10,34,58,22,46]
def dst261 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,16,34,32,4,18,46,30,44,6,32,20,44,58,8,34,58,22,46,10]
def cycle261_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle261_1 : CycleData E W := ⟨3,![1,15,6,11,10],![4,6,18,16,30]⟩
def cycle261_2 : CycleData E W := ⟨4,![2,3,29,17,18,19],![6,8,10,46,30,44]⟩
def cycle261_3 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle261_4 : CycleData E W := ⟨1,![7,28,16],![18,22,46]⟩
def cycle261_5 : CycleData E W := ⟨2,![8,27,23,22],![20,22,58,44]⟩
def cycle261_6 : CycleData E W := ⟨2,![20,13,26,24],![8,32,34,58]⟩
def data261 : PartitionData E W := ⟨7,![cycle261_0,cycle261_1,cycle261_2,cycle261_3,cycle261_4,cycle261_5,cycle261_6]⟩
lemma valid261 : data261.Valid src261 dst261 Finset.univ := by decide +kernel
lemma src_eq261 : src261 = src (unkey (representativeKey 261)) := by decide +kernel
lemma dst_eq261 : dst261 = dst (unkey (representativeKey 261)) := by decide +kernel
lemma certificate261 : Certificate 261 := by
  refine ⟨data261,?_,?_⟩
  · rw [← src_eq261,← dst_eq261]
    exact valid261
  · decide +kernel

def src262 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,22,46,34,58]
def dst262 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,22,46,34,58,10]
def cycle262_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle262_1 : CycleData E W := ⟨4,![1,2,20,21,17,10],![4,6,8,20,44,30]⟩
def cycle262_2 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle262_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle262_4 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,32]⟩
def cycle262_5 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle262_6 : CycleData E W := ⟨2,![27,18,22,28],![34,46,44,58]⟩
def data262 : PartitionData E W := ⟨7,![cycle262_0,cycle262_1,cycle262_2,cycle262_3,cycle262_4,cycle262_5,cycle262_6]⟩
lemma valid262 : data262.Valid src262 dst262 Finset.univ := by decide +kernel
lemma src_eq262 : src262 = src (unkey (representativeKey 262)) := by decide +kernel
lemma dst_eq262 : dst262 = dst (unkey (representativeKey 262)) := by decide +kernel
lemma certificate262 : Certificate 262 := by
  refine ⟨data262,?_,?_⟩
  · rw [← src_eq262,← dst_eq262]
    exact valid262
  · decide +kernel

def src263 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,22,58,34,46]
def dst263 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,22,58,34,46,10]
def cycle263_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle263_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle263_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle263_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle263_4 : CycleData E W := ⟨3,![6,7,26,23,12],![16,18,22,58,32]⟩
def cycle263_5 : CycleData E W := ⟨3,![20,21,17,11,24],![8,20,44,30,32]⟩
def cycle263_6 : CycleData E W := ⟨2,![27,22,18,28],![34,58,44,46]⟩
def data263 : PartitionData E W := ⟨7,![cycle263_0,cycle263_1,cycle263_2,cycle263_3,cycle263_4,cycle263_5,cycle263_6]⟩
lemma valid263 : data263.Valid src263 dst263 Finset.univ := by decide +kernel
lemma src_eq263 : src263 = src (unkey (representativeKey 263)) := by decide +kernel
lemma dst_eq263 : dst263 = dst (unkey (representativeKey 263)) := by decide +kernel
lemma certificate263 : Certificate 263 := by
  refine ⟨data263,?_,?_⟩
  · rw [← src_eq263,← dst_eq263]
    exact valid263
  · decide +kernel

def src264 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,22,58,46,34]
def dst264 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,22,58,46,34,10]
def cycle264_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle264_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle264_2 : CycleData E W := ⟨3,![2,3,29,28,19],![6,8,10,34,46]⟩
def cycle264_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle264_4 : CycleData E W := ⟨3,![6,7,26,23,12],![16,18,22,58,32]⟩
def cycle264_5 : CycleData E W := ⟨3,![20,21,17,11,24],![8,20,44,30,32]⟩
def cycle264_6 : CycleData E W := ⟨1,![18,27,22],![44,46,58]⟩
def data264 : PartitionData E W := ⟨7,![cycle264_0,cycle264_1,cycle264_2,cycle264_3,cycle264_4,cycle264_5,cycle264_6]⟩
lemma valid264 : data264.Valid src264 dst264 Finset.univ := by decide +kernel
lemma src_eq264 : src264 = src (unkey (representativeKey 264)) := by decide +kernel
lemma dst_eq264 : dst264 = dst (unkey (representativeKey 264)) := by decide +kernel
lemma certificate264 : Certificate 264 := by
  refine ⟨data264,?_,?_⟩
  · rw [← src_eq264,← dst_eq264]
    exact valid264
  · decide +kernel

def src265 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,46,22,34,58]
def dst265 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,46,22,34,58,10]
def cycle265_0 : CycleData E W := ⟨3,![0,14,28,29,4],![2,4,34,58,10]⟩
def cycle265_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle265_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle265_3 : CycleData E W := ⟨3,![5,12,24,20,9],![2,16,32,8,20]⟩
def cycle265_4 : CycleData E W := ⟨2,![6,7,27,13],![16,18,22,34]⟩
def cycle265_5 : CycleData E W := ⟨2,![8,26,18,21],![20,22,46,44]⟩
def cycle265_6 : CycleData E W := ⟨2,![11,23,22,17],![30,32,58,44]⟩
def data265 : PartitionData E W := ⟨7,![cycle265_0,cycle265_1,cycle265_2,cycle265_3,cycle265_4,cycle265_5,cycle265_6]⟩
lemma valid265 : data265.Valid src265 dst265 Finset.univ := by decide +kernel
lemma src_eq265 : src265 = src (unkey (representativeKey 265)) := by decide +kernel
lemma dst_eq265 : dst265 = dst (unkey (representativeKey 265)) := by decide +kernel
lemma certificate265 : Certificate 265 := by
  refine ⟨data265,?_,?_⟩
  · rw [← src_eq265,← dst_eq265]
    exact valid265
  · decide +kernel

def src266 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,46,34,22,58]
def dst266 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle266_0 : CycleData E W := ⟨13,![5,13,14,1,2,3,25,18,22,23,11,16,7,8,9],![2,16,34,4,6,8,10,46,44,58,32,30,18,22,20]⟩
def cycle266_1 : CycleData E W := ⟨13,![0,10,17,21,20,24,12,6,15,19,26,27,28,29,4],![2,4,30,44,20,8,32,16,18,6,46,34,22,58,10]⟩
def data266 : PartitionData E W := ⟨2,![cycle266_0,cycle266_1]⟩
lemma valid266 : data266.Valid src266 dst266 Finset.univ := by decide +kernel
lemma src_eq266 : src266 = src (unkey (representativeKey 266)) := by decide +kernel
lemma dst_eq266 : dst266 = dst (unkey (representativeKey 266)) := by decide +kernel
lemma certificate266 : Certificate 266 := by
  refine ⟨data266,?_,?_⟩
  · rw [← src_eq266,← dst_eq266]
    exact valid266
  · decide +kernel

def src267 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,20,44,58,10,22,46,34,58]
def dst267 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,20,44,58,8,22,46,34,58,10]
def cycle267_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle267_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle267_2 : CycleData E W := ⟨5,![2,20,12,6,7,26,19],![6,8,32,16,18,22,46]⟩
def cycle267_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle267_4 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle267_5 : CycleData E W := ⟨2,![21,11,17,22],![20,32,30,44]⟩
def cycle267_6 : CycleData E W := ⟨2,![27,18,23,28],![34,46,44,58]⟩
def data267 : PartitionData E W := ⟨7,![cycle267_0,cycle267_1,cycle267_2,cycle267_3,cycle267_4,cycle267_5,cycle267_6]⟩
lemma valid267 : data267.Valid src267 dst267 Finset.univ := by decide +kernel
lemma src_eq267 : src267 = src (unkey (representativeKey 267)) := by decide +kernel
lemma dst_eq267 : dst267 = dst (unkey (representativeKey 267)) := by decide +kernel
lemma certificate267 : Certificate 267 := by
  refine ⟨data267,?_,?_⟩
  · rw [← src_eq267,← dst_eq267]
    exact valid267
  · decide +kernel

def src268 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,20,44,58,10,22,58,34,46]
def dst268 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,20,44,58,8,22,58,34,46,10]
def cycle268_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle268_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle268_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle268_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle268_4 : CycleData E W := ⟨4,![20,12,6,7,26,24],![8,32,16,18,22,58]⟩
def cycle268_5 : CycleData E W := ⟨2,![21,11,17,22],![20,32,30,44]⟩
def cycle268_6 : CycleData E W := ⟨2,![27,23,18,28],![34,58,44,46]⟩
def data268 : PartitionData E W := ⟨7,![cycle268_0,cycle268_1,cycle268_2,cycle268_3,cycle268_4,cycle268_5,cycle268_6]⟩
lemma valid268 : data268.Valid src268 dst268 Finset.univ := by decide +kernel
lemma src_eq268 : src268 = src (unkey (representativeKey 268)) := by decide +kernel
lemma dst_eq268 : dst268 = dst (unkey (representativeKey 268)) := by decide +kernel
lemma certificate268 : Certificate 268 := by
  refine ⟨data268,?_,?_⟩
  · rw [← src_eq268,← dst_eq268]
    exact valid268
  · decide +kernel

def src269 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,58,20,44,10,22,46,34,58]
def dst269 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,58,20,44,8,22,46,34,58,10]
def cycle269_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle269_1 : CycleData E W := ⟨3,![1,2,24,17,10],![4,6,8,44,30]⟩
def cycle269_2 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,32]⟩
def cycle269_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle269_4 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,32]⟩
def cycle269_5 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle269_6 : CycleData E W := ⟨3,![22,28,27,18,23],![20,58,34,46,44]⟩
def data269 : PartitionData E W := ⟨7,![cycle269_0,cycle269_1,cycle269_2,cycle269_3,cycle269_4,cycle269_5,cycle269_6]⟩
lemma valid269 : data269.Valid src269 dst269 Finset.univ := by decide +kernel
lemma src_eq269 : src269 = src (unkey (representativeKey 269)) := by decide +kernel
lemma dst_eq269 : dst269 = dst (unkey (representativeKey 269)) := by decide +kernel
lemma certificate269 : Certificate 269 := by
  refine ⟨data269,?_,?_⟩
  · rw [← src_eq269,← dst_eq269]
    exact valid269
  · decide +kernel

def src270 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,58,20,44,10,22,58,34,46]
def dst270 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,58,20,44,8,22,58,34,46,10]
def cycle270_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle270_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle270_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle270_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle270_4 : CycleData E W := ⟨3,![6,7,26,21,12],![16,18,22,58,32]⟩
def cycle270_5 : CycleData E W := ⟨2,![20,11,17,24],![8,32,30,44]⟩
def cycle270_6 : CycleData E W := ⟨3,![22,27,28,18,23],![20,58,34,46,44]⟩
def data270 : PartitionData E W := ⟨7,![cycle270_0,cycle270_1,cycle270_2,cycle270_3,cycle270_4,cycle270_5,cycle270_6]⟩
lemma valid270 : data270.Valid src270 dst270 Finset.univ := by decide +kernel
lemma src_eq270 : src270 = src (unkey (representativeKey 270)) := by decide +kernel
lemma dst_eq270 : dst270 = dst (unkey (representativeKey 270)) := by decide +kernel
lemma certificate270 : Certificate 270 := by
  refine ⟨data270,?_,?_⟩
  · rw [← src_eq270,← dst_eq270]
    exact valid270
  · decide +kernel

def src271 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,58,20,44,10,22,58,46,34]
def dst271 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,58,20,44,8,22,58,46,34,10]
def cycle271_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle271_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle271_2 : CycleData E W := ⟨3,![2,3,29,28,19],![6,8,10,34,46]⟩
def cycle271_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle271_4 : CycleData E W := ⟨3,![6,7,26,21,12],![16,18,22,58,32]⟩
def cycle271_5 : CycleData E W := ⟨2,![20,11,17,24],![8,32,30,44]⟩
def cycle271_6 : CycleData E W := ⟨2,![22,27,18,23],![20,58,46,44]⟩
def data271 : PartitionData E W := ⟨7,![cycle271_0,cycle271_1,cycle271_2,cycle271_3,cycle271_4,cycle271_5,cycle271_6]⟩
lemma valid271 : data271.Valid src271 dst271 Finset.univ := by decide +kernel
lemma src_eq271 : src271 = src (unkey (representativeKey 271)) := by decide +kernel
lemma dst_eq271 : dst271 = dst (unkey (representativeKey 271)) := by decide +kernel
lemma certificate271 : Certificate 271 := by
  refine ⟨data271,?_,?_⟩
  · rw [← src_eq271,← dst_eq271]
    exact valid271
  · decide +kernel

def src272 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,58,20,44,10,34,22,46,58]
def dst272 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,58,20,44,8,34,22,46,58,10]
def cycle272_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle272_1 : CycleData E W := ⟨3,![1,2,24,17,10],![4,6,8,44,30]⟩
def cycle272_2 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,32]⟩
def cycle272_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,20]⟩
def cycle272_4 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,32]⟩
def cycle272_5 : CycleData E W := ⟨2,![15,7,27,19],![6,18,22,46]⟩
def cycle272_6 : CycleData E W := ⟨2,![22,28,18,23],![20,58,46,44]⟩
def data272 : PartitionData E W := ⟨7,![cycle272_0,cycle272_1,cycle272_2,cycle272_3,cycle272_4,cycle272_5,cycle272_6]⟩
lemma valid272 : data272.Valid src272 dst272 Finset.univ := by decide +kernel
lemma src_eq272 : src272 = src (unkey (representativeKey 272)) := by decide +kernel
lemma dst_eq272 : dst272 = dst (unkey (representativeKey 272)) := by decide +kernel
lemma certificate272 : Certificate 272 := by
  refine ⟨data272,?_,?_⟩
  · rw [← src_eq272,← dst_eq272]
    exact valid272
  · decide +kernel

def src273 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,44,46,8,32,58,20,44,10,46,22,34,58]
def dst273 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,44,46,6,32,58,20,44,8,46,22,34,58,10]
def cycle273_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle273_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle273_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle273_3 : CycleData E W := ⟨2,![4,29,22,9],![2,10,58,20]⟩
def cycle273_4 : CycleData E W := ⟨4,![6,7,27,28,21,12],![16,18,22,34,58,32]⟩
def cycle273_5 : CycleData E W := ⟨2,![8,26,18,23],![20,22,46,44]⟩
def cycle273_6 : CycleData E W := ⟨2,![20,11,17,24],![8,32,30,44]⟩
def data273 : PartitionData E W := ⟨7,![cycle273_0,cycle273_1,cycle273_2,cycle273_3,cycle273_4,cycle273_5,cycle273_6]⟩
lemma valid273 : data273.Valid src273 dst273 Finset.univ := by decide +kernel
lemma src_eq273 : src273 = src (unkey (representativeKey 273)) := by decide +kernel
lemma dst_eq273 : dst273 = dst (unkey (representativeKey 273)) := by decide +kernel
lemma certificate273 : Certificate 273 := by
  refine ⟨data273,?_,?_⟩
  · rw [← src_eq273,← dst_eq273]
    exact valid273
  · decide +kernel

def src274 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,46,44,8,20,44,58,32,10,46,34,22,58]
def dst274 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,46,44,6,20,44,58,32,8,46,34,22,58,10]
def cycle274_0 : CycleData E W := ⟨13,![5,13,14,10,11,23,22,18,25,3,2,15,7,8,9],![2,16,34,4,30,32,58,44,46,10,8,6,18,22,20]⟩
def cycle274_1 : CycleData E W := ⟨13,![0,1,19,21,20,24,12,6,16,17,26,27,28,29,4],![2,4,6,44,20,8,32,16,18,30,46,34,22,58,10]⟩
def data274 : PartitionData E W := ⟨2,![cycle274_0,cycle274_1]⟩
lemma valid274 : data274.Valid src274 dst274 Finset.univ := by decide +kernel
lemma src_eq274 : src274 = src (unkey (representativeKey 274)) := by decide +kernel
lemma dst_eq274 : dst274 = dst (unkey (representativeKey 274)) := by decide +kernel
lemma certificate274 : Certificate 274 := by
  refine ⟨data274,?_,?_⟩
  · rw [← src_eq274,← dst_eq274]
    exact valid274
  · decide +kernel

def src275 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,32,16,34,6,18,30,46,44,8,32,44,20,58,10,22,34,58,46]
def dst275 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,32,16,34,4,18,30,46,44,6,32,44,20,58,8,22,34,58,46,10]
def cycle275_0 : CycleData E W := ⟨13,![0,14,13,12,11,17,18,19,15,7,25,3,24,23,9],![2,4,34,16,32,30,46,44,6,18,22,10,8,58,20]⟩
def cycle275_1 : CycleData E W := ⟨13,![4,29,28,27,26,8,22,21,20,2,1,10,16,6,5],![2,10,46,58,34,22,20,44,32,8,6,4,30,18,16]⟩
def data275 : PartitionData E W := ⟨2,![cycle275_0,cycle275_1]⟩
lemma valid275 : data275.Valid src275 dst275 Finset.univ := by decide +kernel
lemma src_eq275 : src275 = src (unkey (representativeKey 275)) := by decide +kernel
lemma dst_eq275 : dst275 = dst (unkey (representativeKey 275)) := by decide +kernel
lemma certificate275 : Certificate 275 := by
  refine ⟨data275,?_,?_⟩
  · rw [← src_eq275,← dst_eq275]
    exact valid275
  · decide +kernel

def src276 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,32,58,44,10,22,46,34,58]
def dst276 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,32,58,44,8,22,46,34,58,10]
def cycle276_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle276_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle276_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle276_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle276_4 : CycleData E W := ⟨3,![6,7,26,27,12],![16,18,22,46,34]⟩
def cycle276_5 : CycleData E W := ⟨3,![25,8,21,22,29],![10,22,20,32,58]⟩
def cycle276_6 : CycleData E W := ⟨2,![11,28,23,17],![30,34,58,44]⟩
def data276 : PartitionData E W := ⟨7,![cycle276_0,cycle276_1,cycle276_2,cycle276_3,cycle276_4,cycle276_5,cycle276_6]⟩
lemma valid276 : data276.Valid src276 dst276 Finset.univ := by decide +kernel
lemma src_eq276 : src276 = src (unkey (representativeKey 276)) := by decide +kernel
lemma dst_eq276 : dst276 = dst (unkey (representativeKey 276)) := by decide +kernel
lemma certificate276 : Certificate 276 := by
  refine ⟨data276,?_,?_⟩
  · rw [← src_eq276,← dst_eq276]
    exact valid276
  · decide +kernel

def src277 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,32,58,44,10,22,58,46,34]
def dst277 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle277_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle277_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle277_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle277_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle277_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle277_5 : CycleData E W := ⟨2,![8,26,22,21],![20,22,58,32]⟩
def cycle277_6 : CycleData E W := ⟨3,![11,28,27,23,17],![30,34,46,58,44]⟩
def data277 : PartitionData E W := ⟨7,![cycle277_0,cycle277_1,cycle277_2,cycle277_3,cycle277_4,cycle277_5,cycle277_6]⟩
lemma valid277 : data277.Valid src277 dst277 Finset.univ := by decide +kernel
lemma src_eq277 : src277 = src (unkey (representativeKey 277)) := by decide +kernel
lemma dst_eq277 : dst277 = dst (unkey (representativeKey 277)) := by decide +kernel
lemma certificate277 : Certificate 277 := by
  refine ⟨data277,?_,?_⟩
  · rw [← src_eq277,← dst_eq277]
    exact valid277
  · decide +kernel

def src278 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,32,58,44,10,34,58,22,46]
def dst278 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle278_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle278_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle278_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle278_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle278_4 : CycleData E W := ⟨4,![25,12,6,7,28,29],![10,34,16,18,22,46]⟩
def cycle278_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,32]⟩
def cycle278_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data278 : PartitionData E W := ⟨7,![cycle278_0,cycle278_1,cycle278_2,cycle278_3,cycle278_4,cycle278_5,cycle278_6]⟩
lemma valid278 : data278.Valid src278 dst278 Finset.univ := by decide +kernel
lemma src_eq278 : src278 = src (unkey (representativeKey 278)) := by decide +kernel
lemma dst_eq278 : dst278 = dst (unkey (representativeKey 278)) := by decide +kernel
lemma certificate278 : Certificate 278 := by
  refine ⟨data278,?_,?_⟩
  · rw [← src_eq278,← dst_eq278]
    exact valid278
  · decide +kernel

def src279 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,22,58,46,34]
def dst279 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,22,58,46,34,10]
def cycle279_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle279_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle279_2 : CycleData E W := ⟨2,![2,24,27,19],![6,8,58,46]⟩
def cycle279_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle279_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle279_5 : CycleData E W := ⟨3,![8,26,23,22,21],![20,22,58,32,44]⟩
def cycle279_6 : CycleData E W := ⟨2,![11,28,18,17],![30,34,46,44]⟩
def data279 : PartitionData E W := ⟨7,![cycle279_0,cycle279_1,cycle279_2,cycle279_3,cycle279_4,cycle279_5,cycle279_6]⟩
lemma valid279 : data279.Valid src279 dst279 Finset.univ := by decide +kernel
lemma src_eq279 : src279 = src (unkey (representativeKey 279)) := by decide +kernel
lemma dst_eq279 : dst279 = dst (unkey (representativeKey 279)) := by decide +kernel
lemma certificate279 : Certificate 279 := by
  refine ⟨data279,?_,?_⟩
  · rw [← src_eq279,← dst_eq279]
    exact valid279
  · decide +kernel

def src280 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,34,22,58,46]
def dst280 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,34,22,58,46,10]
def cycle280_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle280_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle280_2 : CycleData E W := ⟨2,![2,24,28,19],![6,8,58,46]⟩
def cycle280_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle280_4 : CycleData E W := ⟨2,![6,7,26,12],![16,18,22,34]⟩
def cycle280_5 : CycleData E W := ⟨3,![8,27,23,22,21],![20,22,58,32,44]⟩
def cycle280_6 : CycleData E W := ⟨3,![25,11,17,18,29],![10,34,30,44,46]⟩
def data280 : PartitionData E W := ⟨7,![cycle280_0,cycle280_1,cycle280_2,cycle280_3,cycle280_4,cycle280_5,cycle280_6]⟩
lemma valid280 : data280.Valid src280 dst280 Finset.univ := by decide +kernel
lemma src_eq280 : src280 = src (unkey (representativeKey 280)) := by decide +kernel
lemma dst_eq280 : dst280 = dst (unkey (representativeKey 280)) := by decide +kernel
lemma certificate280 : Certificate 280 := by
  refine ⟨data280,?_,?_⟩
  · rw [← src_eq280,← dst_eq280]
    exact valid280
  · decide +kernel

def src281 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,34,58,22,46]
def dst281 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,34,58,22,46,10]
def cycle281_0 : CycleData E W := ⟨13,![5,12,25,3,24,23,14,10,17,18,19,15,7,8,9],![2,16,34,10,8,58,32,4,30,44,46,6,18,22,20]⟩
def cycle281_1 : CycleData E W := ⟨13,![0,1,2,20,21,22,13,6,16,11,26,27,28,29,4],![2,4,6,8,20,44,32,16,18,30,34,58,22,46,10]⟩
def data281 : PartitionData E W := ⟨2,![cycle281_0,cycle281_1]⟩
lemma valid281 : data281.Valid src281 dst281 Finset.univ := by decide +kernel
lemma src_eq281 : src281 = src (unkey (representativeKey 281)) := by decide +kernel
lemma dst_eq281 : dst281 = dst (unkey (representativeKey 281)) := by decide +kernel
lemma certificate281 : Certificate 281 := by
  refine ⟨data281,?_,?_⟩
  · rw [← src_eq281,← dst_eq281]
    exact valid281
  · decide +kernel

def src282 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,46,22,34,58]
def dst282 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,46,22,34,58,10]
def cycle282_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle282_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle282_2 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle282_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle282_4 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,46,22,20]⟩
def cycle282_5 : CycleData E W := ⟨2,![6,7,27,12],![16,18,22,34]⟩
def cycle282_6 : CycleData E W := ⟨3,![11,28,23,22,17],![30,34,58,32,44]⟩
def data282 : PartitionData E W := ⟨7,![cycle282_0,cycle282_1,cycle282_2,cycle282_3,cycle282_4,cycle282_5,cycle282_6]⟩
lemma valid282 : data282.Valid src282 dst282 Finset.univ := by decide +kernel
lemma src_eq282 : src282 = src (unkey (representativeKey 282)) := by decide +kernel
lemma dst_eq282 : dst282 = dst (unkey (representativeKey 282)) := by decide +kernel
lemma certificate282 : Certificate 282 := by
  refine ⟨data282,?_,?_⟩
  · rw [← src_eq282,← dst_eq282]
    exact valid282
  · decide +kernel

def src283 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,58,32,44,10,22,46,34,58]
def dst283 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,58,32,44,8,22,46,34,58,10]
def cycle283_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle283_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle283_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle283_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle283_4 : CycleData E W := ⟨3,![6,7,26,27,12],![16,18,22,46,34]⟩
def cycle283_5 : CycleData E W := ⟨2,![25,8,21,29],![10,22,20,58]⟩
def cycle283_6 : CycleData E W := ⟨3,![11,28,22,23,17],![30,34,58,32,44]⟩
def data283 : PartitionData E W := ⟨7,![cycle283_0,cycle283_1,cycle283_2,cycle283_3,cycle283_4,cycle283_5,cycle283_6]⟩
lemma valid283 : data283.Valid src283 dst283 Finset.univ := by decide +kernel
lemma src_eq283 : src283 = src (unkey (representativeKey 283)) := by decide +kernel
lemma dst_eq283 : dst283 = dst (unkey (representativeKey 283)) := by decide +kernel
lemma certificate283 : Certificate 283 := by
  refine ⟨data283,?_,?_⟩
  · rw [← src_eq283,← dst_eq283]
    exact valid283
  · decide +kernel

def src284 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,58,32,44,10,34,22,58,46]
def dst284 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,58,32,44,8,34,22,58,46,10]
def cycle284_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle284_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle284_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle284_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle284_4 : CycleData E W := ⟨2,![6,7,26,12],![16,18,22,34]⟩
def cycle284_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle284_6 : CycleData E W := ⟨5,![25,11,17,23,22,28,29],![10,34,30,44,32,58,46]⟩
def data284 : PartitionData E W := ⟨7,![cycle284_0,cycle284_1,cycle284_2,cycle284_3,cycle284_4,cycle284_5,cycle284_6]⟩
lemma valid284 : data284.Valid src284 dst284 Finset.univ := by decide +kernel
lemma src_eq284 : src284 = src (unkey (representativeKey 284)) := by decide +kernel
lemma dst_eq284 : dst284 = dst (unkey (representativeKey 284)) := by decide +kernel
lemma certificate284 : Certificate 284 := by
  refine ⟨data284,?_,?_⟩
  · rw [← src_eq284,← dst_eq284]
    exact valid284
  · decide +kernel

def src285 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,20,58,32,44,10,34,58,22,46]
def dst285 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,20,58,32,44,8,34,58,22,46,10]
def cycle285_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle285_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle285_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle285_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle285_4 : CycleData E W := ⟨4,![25,12,6,7,28,29],![10,34,16,18,22,46]⟩
def cycle285_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle285_6 : CycleData E W := ⟨3,![11,26,22,23,17],![30,34,58,32,44]⟩
def data285 : PartitionData E W := ⟨7,![cycle285_0,cycle285_1,cycle285_2,cycle285_3,cycle285_4,cycle285_5,cycle285_6]⟩
lemma valid285 : data285.Valid src285 dst285 Finset.univ := by decide +kernel
lemma src_eq285 : src285 = src (unkey (representativeKey 285)) := by decide +kernel
lemma dst_eq285 : dst285 = dst (unkey (representativeKey 285)) := by decide +kernel
lemma certificate285 : Certificate 285 := by
  refine ⟨data285,?_,?_⟩
  · rw [← src_eq285,← dst_eq285]
    exact valid285
  · decide +kernel

def src286 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,32,20,44,58,10,34,58,22,46]
def dst286 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,32,20,44,58,8,34,58,22,46,10]
def cycle286_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle286_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle286_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle286_3 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle286_4 : CycleData E W := ⟨4,![20,13,6,7,27,24],![8,32,16,18,22,58]⟩
def cycle286_5 : CycleData E W := ⟨2,![8,28,18,22],![20,22,46,44]⟩
def cycle286_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data286 : PartitionData E W := ⟨7,![cycle286_0,cycle286_1,cycle286_2,cycle286_3,cycle286_4,cycle286_5,cycle286_6]⟩
lemma valid286 : data286.Valid src286 dst286 Finset.univ := by decide +kernel
lemma src_eq286 : src286 = src (unkey (representativeKey 286)) := by decide +kernel
lemma dst_eq286 : dst286 = dst (unkey (representativeKey 286)) := by decide +kernel
lemma certificate286 : Certificate 286 := by
  refine ⟨data286,?_,?_⟩
  · rw [← src_eq286,← dst_eq286]
    exact valid286
  · decide +kernel

def src287 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,32,44,20,58,10,22,46,58,34]
def dst287 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,32,44,20,58,8,22,46,58,34,10]
def cycle287_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,30,34,16]⟩
def cycle287_1 : CycleData E W := ⟨2,![1,2,20,14],![4,6,8,32]⟩
def cycle287_2 : CycleData E W := ⟨2,![3,29,28,24],![8,10,34,58]⟩
def cycle287_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle287_4 : CycleData E W := ⟨3,![6,16,17,21,13],![16,18,30,44,32]⟩
def cycle287_5 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle287_6 : CycleData E W := ⟨2,![22,18,27,23],![20,44,46,58]⟩
def data287 : PartitionData E W := ⟨7,![cycle287_0,cycle287_1,cycle287_2,cycle287_3,cycle287_4,cycle287_5,cycle287_6]⟩
lemma valid287 : data287.Valid src287 dst287 Finset.univ := by decide +kernel
lemma src_eq287 : src287 = src (unkey (representativeKey 287)) := by decide +kernel
lemma dst_eq287 : dst287 = dst (unkey (representativeKey 287)) := by decide +kernel
lemma certificate287 : Certificate 287 := by
  refine ⟨data287,?_,?_⟩
  · rw [← src_eq287,← dst_eq287]
    exact valid287
  · decide +kernel

def src288 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,44,20,32,58,10,22,46,58,34]
def dst288 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,44,20,32,58,8,22,46,58,34,10]
def cycle288_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle288_1 : CycleData E W := ⟨3,![1,2,20,17,10],![4,6,8,44,30]⟩
def cycle288_2 : CycleData E W := ⟨2,![3,29,28,24],![8,10,34,58]⟩
def cycle288_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle288_4 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle288_5 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle288_6 : CycleData E W := ⟨3,![21,18,27,23,22],![20,44,46,58,32]⟩
def data288 : PartitionData E W := ⟨7,![cycle288_0,cycle288_1,cycle288_2,cycle288_3,cycle288_4,cycle288_5,cycle288_6]⟩
lemma valid288 : data288.Valid src288 dst288 Finset.univ := by decide +kernel
lemma src_eq288 : src288 = src (unkey (representativeKey 288)) := by decide +kernel
lemma dst_eq288 : dst288 = dst (unkey (representativeKey 288)) := by decide +kernel
lemma certificate288 : Certificate 288 := by
  refine ⟨data288,?_,?_⟩
  · rw [← src_eq288,← dst_eq288]
    exact valid288
  · decide +kernel

def src289 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,44,20,32,58,10,22,58,46,34]
def dst289 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,44,20,32,58,8,22,58,46,34,10]
def cycle289_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle289_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle289_2 : CycleData E W := ⟨2,![2,24,27,19],![6,8,58,46]⟩
def cycle289_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,10,8,44,20]⟩
def cycle289_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle289_5 : CycleData E W := ⟨2,![8,26,23,22],![20,22,58,32]⟩
def cycle289_6 : CycleData E W := ⟨2,![11,28,18,17],![30,34,46,44]⟩
def data289 : PartitionData E W := ⟨7,![cycle289_0,cycle289_1,cycle289_2,cycle289_3,cycle289_4,cycle289_5,cycle289_6]⟩
lemma valid289 : data289.Valid src289 dst289 Finset.univ := by decide +kernel
lemma src_eq289 : src289 = src (unkey (representativeKey 289)) := by decide +kernel
lemma dst_eq289 : dst289 = dst (unkey (representativeKey 289)) := by decide +kernel
lemma certificate289 : Certificate 289 := by
  refine ⟨data289,?_,?_⟩
  · rw [← src_eq289,← dst_eq289]
    exact valid289
  · decide +kernel

def src290 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,44,20,32,58,10,34,22,58,46]
def dst290 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,44,20,32,58,8,34,22,58,46,10]
def cycle290_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle290_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle290_2 : CycleData E W := ⟨2,![2,20,18,19],![6,8,44,46]⟩
def cycle290_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle290_4 : CycleData E W := ⟨4,![4,25,11,17,21,9],![2,10,34,30,44,20]⟩
def cycle290_5 : CycleData E W := ⟨2,![6,7,26,12],![16,18,22,34]⟩
def cycle290_6 : CycleData E W := ⟨2,![8,27,23,22],![20,22,58,32]⟩
def data290 : PartitionData E W := ⟨7,![cycle290_0,cycle290_1,cycle290_2,cycle290_3,cycle290_4,cycle290_5,cycle290_6]⟩
lemma valid290 : data290.Valid src290 dst290 Finset.univ := by decide +kernel
lemma src_eq290 : src290 = src (unkey (representativeKey 290)) := by decide +kernel
lemma dst_eq290 : dst290 = dst (unkey (representativeKey 290)) := by decide +kernel
lemma certificate290 : Certificate 290 := by
  refine ⟨data290,?_,?_⟩
  · rw [← src_eq290,← dst_eq290]
    exact valid290
  · decide +kernel

def src291 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,44,46,8,44,20,32,58,10,34,58,22,46]
def dst291 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,44,46,6,44,20,32,58,8,34,58,22,46,10]
def cycle291_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle291_1 : CycleData E W := ⟨3,![1,2,20,17,10],![4,6,8,44,30]⟩
def cycle291_2 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle291_3 : CycleData E W := ⟨3,![4,29,18,21,9],![2,10,46,44,20]⟩
def cycle291_4 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle291_5 : CycleData E W := ⟨2,![15,7,28,19],![6,18,22,46]⟩
def cycle291_6 : CycleData E W := ⟨2,![8,27,23,22],![20,22,58,32]⟩
def data291 : PartitionData E W := ⟨7,![cycle291_0,cycle291_1,cycle291_2,cycle291_3,cycle291_4,cycle291_5,cycle291_6]⟩
lemma valid291 : data291.Valid src291 dst291 Finset.univ := by decide +kernel
lemma src_eq291 : src291 = src (unkey (representativeKey 291)) := by decide +kernel
lemma dst_eq291 : dst291 = dst (unkey (representativeKey 291)) := by decide +kernel
lemma certificate291 : Certificate 291 := by
  refine ⟨data291,?_,?_⟩
  · rw [← src_eq291,← dst_eq291]
    exact valid291
  · decide +kernel

def src292 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,30,46,44,8,20,44,32,58,10,34,58,22,46]
def dst292 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,30,46,44,6,20,44,32,58,8,34,58,22,46,10]
def cycle292_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle292_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle292_2 : CycleData E W := ⟨3,![2,24,23,22,19],![6,8,58,32,44]⟩
def cycle292_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle292_4 : CycleData E W := ⟨3,![6,7,27,26,12],![16,18,22,58,34]⟩
def cycle292_5 : CycleData E W := ⟨2,![8,28,18,21],![20,22,46,44]⟩
def cycle292_6 : CycleData E W := ⟨2,![25,11,17,29],![10,34,30,46]⟩
def data292 : PartitionData E W := ⟨7,![cycle292_0,cycle292_1,cycle292_2,cycle292_3,cycle292_4,cycle292_5,cycle292_6]⟩
lemma valid292 : data292.Valid src292 dst292 Finset.univ := by decide +kernel
lemma src_eq292 : src292 = src (unkey (representativeKey 292)) := by decide +kernel
lemma dst_eq292 : dst292 = dst (unkey (representativeKey 292)) := by decide +kernel
lemma certificate292 : Certificate 292 := by
  refine ⟨data292,?_,?_⟩
  · rw [← src_eq292,← dst_eq292]
    exact valid292
  · decide +kernel

def src293 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,20,32,44,58,10,22,46,58,34]
def dst293 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,20,32,44,58,8,22,46,58,34,10]
def cycle293_0 : CycleData E W := ⟨3,![0,10,11,12,5],![2,4,30,34,16]⟩
def cycle293_1 : CycleData E W := ⟨3,![1,2,20,21,14],![4,6,8,20,32]⟩
def cycle293_2 : CycleData E W := ⟨2,![3,29,28,24],![8,10,34,58]⟩
def cycle293_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,20]⟩
def cycle293_4 : CycleData E W := ⟨2,![6,16,22,13],![16,18,44,32]⟩
def cycle293_5 : CycleData E W := ⟨2,![15,7,26,19],![6,18,22,46]⟩
def cycle293_6 : CycleData E W := ⟨2,![17,23,27,18],![30,44,58,46]⟩
def data293 : PartitionData E W := ⟨7,![cycle293_0,cycle293_1,cycle293_2,cycle293_3,cycle293_4,cycle293_5,cycle293_6]⟩
lemma valid293 : data293.Valid src293 dst293 Finset.univ := by decide +kernel
lemma src_eq293 : src293 = src (unkey (representativeKey 293)) := by decide +kernel
lemma dst_eq293 : dst293 = dst (unkey (representativeKey 293)) := by decide +kernel
lemma certificate293 : Certificate 293 := by
  refine ⟨data293,?_,?_⟩
  · rw [← src_eq293,← dst_eq293]
    exact valid293
  · decide +kernel

def src294 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,20,32,44,58,10,46,22,34,58]
def dst294 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,20,32,44,58,8,46,22,34,58,10]
def cycle294_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle294_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle294_2 : CycleData E W := ⟨4,![2,20,21,22,16,15],![6,8,20,32,44,18]⟩
def cycle294_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle294_4 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,46,22,20]⟩
def cycle294_5 : CycleData E W := ⟨2,![6,7,27,12],![16,18,22,34]⟩
def cycle294_6 : CycleData E W := ⟨2,![11,28,23,17],![30,34,58,44]⟩
def data294 : PartitionData E W := ⟨7,![cycle294_0,cycle294_1,cycle294_2,cycle294_3,cycle294_4,cycle294_5,cycle294_6]⟩
lemma valid294 : data294.Valid src294 dst294 Finset.univ := by decide +kernel
lemma src_eq294 : src294 = src (unkey (representativeKey 294)) := by decide +kernel
lemma dst_eq294 : dst294 = dst (unkey (representativeKey 294)) := by decide +kernel
lemma certificate294 : Certificate 294 := by
  refine ⟨data294,?_,?_⟩
  · rw [← src_eq294,← dst_eq294]
    exact valid294
  · decide +kernel

def src295 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,20,32,58,44,10,22,46,58,34]
def dst295 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,20,32,58,44,8,22,46,58,34,10]
def cycle295_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle295_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle295_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle295_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle295_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle295_5 : CycleData E W := ⟨3,![8,26,27,22,21],![20,22,46,58,32]⟩
def cycle295_6 : CycleData E W := ⟨2,![11,28,23,17],![30,34,58,44]⟩
def data295 : PartitionData E W := ⟨7,![cycle295_0,cycle295_1,cycle295_2,cycle295_3,cycle295_4,cycle295_5,cycle295_6]⟩
lemma valid295 : data295.Valid src295 dst295 Finset.univ := by decide +kernel
lemma src_eq295 : src295 = src (unkey (representativeKey 295)) := by decide +kernel
lemma dst_eq295 : dst295 = dst (unkey (representativeKey 295)) := by decide +kernel
lemma certificate295 : Certificate 295 := by
  refine ⟨data295,?_,?_⟩
  · rw [← src_eq295,← dst_eq295]
    exact valid295
  · decide +kernel

def src296 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,20,32,58,44,10,22,58,46,34]
def dst296 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle296_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle296_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,44,30]⟩
def cycle296_2 : CycleData E W := ⟨3,![2,24,23,27,19],![6,8,44,58,46]⟩
def cycle296_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle296_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle296_5 : CycleData E W := ⟨2,![8,26,22,21],![20,22,58,32]⟩
def cycle296_6 : CycleData E W := ⟨1,![11,28,18],![30,34,46]⟩
def data296 : PartitionData E W := ⟨7,![cycle296_0,cycle296_1,cycle296_2,cycle296_3,cycle296_4,cycle296_5,cycle296_6]⟩
lemma valid296 : data296.Valid src296 dst296 Finset.univ := by decide +kernel
lemma src_eq296 : src296 = src (unkey (representativeKey 296)) := by decide +kernel
lemma dst_eq296 : dst296 = dst (unkey (representativeKey 296)) := by decide +kernel
lemma certificate296 : Certificate 296 := by
  refine ⟨data296,?_,?_⟩
  · rw [← src_eq296,← dst_eq296]
    exact valid296
  · decide +kernel

def src297 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,20,32,58,44,10,34,58,22,46]
def dst297 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle297_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle297_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle297_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle297_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle297_4 : CycleData E W := ⟨4,![25,12,6,7,28,29],![10,34,16,18,22,46]⟩
def cycle297_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,32]⟩
def cycle297_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data297 : PartitionData E W := ⟨7,![cycle297_0,cycle297_1,cycle297_2,cycle297_3,cycle297_4,cycle297_5,cycle297_6]⟩
lemma valid297 : data297.Valid src297 dst297 Finset.univ := by decide +kernel
lemma src_eq297 : src297 = src (unkey (representativeKey 297)) := by decide +kernel
lemma dst_eq297 : dst297 = dst (unkey (representativeKey 297)) := by decide +kernel
lemma certificate297 : Certificate 297 := by
  refine ⟨data297,?_,?_⟩
  · rw [← src_eq297,← dst_eq297]
    exact valid297
  · decide +kernel

def src298 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,32,20,44,58,10,22,58,46,34]
def dst298 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,32,20,44,58,8,22,58,46,34,10]
def cycle298_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle298_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,44,30]⟩
def cycle298_2 : CycleData E W := ⟨2,![2,24,27,19],![6,8,58,46]⟩
def cycle298_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,10,8,32,20]⟩
def cycle298_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle298_5 : CycleData E W := ⟨2,![8,26,23,22],![20,22,58,44]⟩
def cycle298_6 : CycleData E W := ⟨1,![11,28,18],![30,34,46]⟩
def data298 : PartitionData E W := ⟨7,![cycle298_0,cycle298_1,cycle298_2,cycle298_3,cycle298_4,cycle298_5,cycle298_6]⟩
lemma valid298 : data298.Valid src298 dst298 Finset.univ := by decide +kernel
lemma src_eq298 : src298 = src (unkey (representativeKey 298)) := by decide +kernel
lemma dst_eq298 : dst298 = dst (unkey (representativeKey 298)) := by decide +kernel
lemma certificate298 : Certificate 298 := by
  refine ⟨data298,?_,?_⟩
  · rw [← src_eq298,← dst_eq298]
    exact valid298
  · decide +kernel

def src299 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,32,20,44,58,10,34,58,22,46]
def dst299 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,32,20,44,58,8,34,58,22,46,10]
def cycle299_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,32,20]⟩
def cycle299_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle299_2 : CycleData E W := ⟨3,![2,20,13,6,15],![6,8,32,16,18]⟩
def cycle299_3 : CycleData E W := ⟨3,![3,29,28,27,24],![8,10,46,22,58]⟩
def cycle299_4 : CycleData E W := ⟨2,![4,25,12,5],![2,10,34,16]⟩
def cycle299_5 : CycleData E W := ⟨2,![7,8,22,16],![18,22,20,44]⟩
def cycle299_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data299 : PartitionData E W := ⟨7,![cycle299_0,cycle299_1,cycle299_2,cycle299_3,cycle299_4,cycle299_5,cycle299_6]⟩
lemma valid299 : data299.Valid src299 dst299 Finset.univ := by decide +kernel
lemma src_eq299 : src299 = src (unkey (representativeKey 299)) := by decide +kernel
lemma dst_eq299 : dst299 = dst (unkey (representativeKey 299)) := by decide +kernel
lemma certificate299 : Certificate 299 := by
  refine ⟨data299,?_,?_⟩
  · rw [← src_eq299,← dst_eq299]
    exact valid299
  · decide +kernel
#print axioms certificate299
end Erdos184Work.SixRepresentativeCertificates0

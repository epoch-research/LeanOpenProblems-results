import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src300 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,28,39,38]
def dst300 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,28,39,38,8]
def cycle300_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle300_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,38,26]⟩
def cycle300_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle300_3 : CycleData E W := ⟨2,![3,14,18,8],![3,5,26,16]⟩
def cycle300_4 : CycleData E W := ⟨3,![5,4,13,22,10],![2,6,5,28,18]⟩
def cycle300_5 : CycleData E W := ⟨2,![7,19,23,12],![14,16,39,28]⟩
def cycle300_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data300 : PartitionData E W := ⟨7,![cycle300_0,cycle300_1,cycle300_2,cycle300_3,cycle300_4,cycle300_5,cycle300_6]⟩
lemma valid_data300 : data300.Valid src300 dst300 Finset.univ := by decide +kernel

def src301 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,28,39]
def dst301 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle301_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle301_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle301_2 : CycleData E W := ⟨2,![4,16,23,13],![5,6,38,28]⟩
def cycle301_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle301_4 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle301_5 : CycleData E W := ⟨3,![8,18,17,22,9],![3,16,26,38,18]⟩
def data301 : PartitionData E W := ⟨6,![cycle301_0,cycle301_1,cycle301_2,cycle301_3,cycle301_4,cycle301_5]⟩
lemma valid_data301 : data301.Valid src301 dst301 Finset.univ := by decide +kernel

def src302 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,39,28]
def dst302 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,39,28,8]
def cycle302_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle302_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle302_2 : CycleData E W := ⟨2,![4,20,24,13],![5,6,39,28]⟩
def cycle302_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle302_4 : CycleData E W := ⟨4,![8,7,12,25,21,9],![3,16,14,28,8,18]⟩
def cycle302_5 : CycleData E W := ⟨2,![18,17,23,19],![16,26,38,39]⟩
def data302 : PartitionData E W := ⟨6,![cycle302_0,cycle302_1,cycle302_2,cycle302_3,cycle302_4,cycle302_5]⟩
lemma valid_data302 : data302.Valid src302 dst302 Finset.univ := by decide +kernel

def src303 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,39,28,38]
def dst303 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle303_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle303_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,38,26]⟩
def cycle303_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle303_3 : CycleData E W := ⟨2,![3,14,18,8],![3,5,26,16]⟩
def cycle303_4 : CycleData E W := ⟨2,![4,16,24,13],![5,6,38,28]⟩
def cycle303_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle303_6 : CycleData E W := ⟨2,![7,19,23,12],![14,16,39,28]⟩
def data303 : PartitionData E W := ⟨7,![cycle303_0,cycle303_1,cycle303_2,cycle303_3,cycle303_4,cycle303_5,cycle303_6]⟩
lemma valid_data303 : data303.Valid src303 dst303 Finset.univ := by decide +kernel

def src304 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,28,18,38,39]
def dst304 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,28,18,38,39,8]
def cycle304_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle304_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle304_2 : CycleData E W := ⟨3,![5,4,13,22,10],![2,6,5,28,18]⟩
def cycle304_3 : CycleData E W := ⟨3,![21,12,7,19,25],![8,28,14,16,39]⟩
def cycle304_4 : CycleData E W := ⟨3,![8,18,17,23,9],![3,16,26,38,18]⟩
def cycle304_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data304 : PartitionData E W := ⟨6,![cycle304_0,cycle304_1,cycle304_2,cycle304_3,cycle304_4,cycle304_5]⟩
lemma valid_data304 : data304.Valid src304 dst304 Finset.univ := by decide +kernel

def src305 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst305 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle305_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle305_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle305_2 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle305_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle305_4 : CycleData E W := ⟨3,![21,12,7,19,25],![8,28,14,16,39]⟩
def cycle305_5 : CycleData E W := ⟨3,![8,18,17,23,9],![3,16,26,38,18]⟩
def data305 : PartitionData E W := ⟨6,![cycle305_0,cycle305_1,cycle305_2,cycle305_3,cycle305_4,cycle305_5]⟩
lemma valid_data305 : data305.Valid src305 dst305 Finset.univ := by decide +kernel

def src306 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst306 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle306_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle306_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle306_2 : CycleData E W := ⟨2,![4,20,22,13],![5,6,39,28]⟩
def cycle306_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle306_4 : CycleData E W := ⟨4,![21,12,7,18,17,25],![8,28,14,16,26,38]⟩
def cycle306_5 : CycleData E W := ⟨2,![8,19,23,9],![3,16,39,18]⟩
def data306 : PartitionData E W := ⟨6,![cycle306_0,cycle306_1,cycle306_2,cycle306_3,cycle306_4,cycle306_5]⟩
lemma valid_data306 : data306.Valid src306 dst306 Finset.univ := by decide +kernel

def src307 : E → W := ![2,4,8,3,5,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst307 : E → W := ![4,8,3,5,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle307_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle307_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,8,4,26,5]⟩
def cycle307_2 : CycleData E W := ⟨3,![5,4,13,23,10],![2,6,5,28,18]⟩
def cycle307_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle307_4 : CycleData E W := ⟨3,![8,18,17,22,9],![3,16,26,38,18]⟩
def cycle307_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data307 : PartitionData E W := ⟨6,![cycle307_0,cycle307_1,cycle307_2,cycle307_3,cycle307_4,cycle307_5]⟩
lemma valid_data307 : data307.Valid src307 dst307 Finset.univ := by decide +kernel

def src308 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,16,38,26,39,8,38,18,28,39]
def dst308 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle308_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle308_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle308_2 : CycleData E W := ⟨2,![4,20,24,12],![5,6,39,28]⟩
def cycle308_3 : CycleData E W := ⟨3,![5,16,17,22,10],![2,6,16,38,18]⟩
def cycle308_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle308_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data308 : PartitionData E W := ⟨6,![cycle308_0,cycle308_1,cycle308_2,cycle308_3,cycle308_4,cycle308_5]⟩
lemma valid_data308 : data308.Valid src308 dst308 Finset.univ := by decide +kernel

def src309 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,16,38,26,39,8,38,28,18,39]
def dst309 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle309_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle309_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle309_2 : CycleData E W := ⟨3,![4,16,17,22,12],![5,6,16,38,28]⟩
def cycle309_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle309_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle309_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data309 : PartitionData E W := ⟨6,![cycle309_0,cycle309_1,cycle309_2,cycle309_3,cycle309_4,cycle309_5]⟩
lemma valid_data309 : data309.Valid src309 dst309 Finset.univ := by decide +kernel

def src310 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,16,39,26,38,8,38,18,28,39]
def dst310 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle310_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle310_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle310_2 : CycleData E W := ⟨3,![4,16,17,24,12],![5,6,16,39,28]⟩
def cycle310_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle310_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle310_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data310 : PartitionData E W := ⟨6,![cycle310_0,cycle310_1,cycle310_2,cycle310_3,cycle310_4,cycle310_5]⟩
lemma valid_data310 : data310.Valid src310 dst310 Finset.univ := by decide +kernel

def src311 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,16,39,26,38,8,38,28,18,39]
def dst311 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle311_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle311_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle311_2 : CycleData E W := ⟨2,![4,20,22,12],![5,6,38,28]⟩
def cycle311_3 : CycleData E W := ⟨3,![5,16,17,24,10],![2,6,16,39,18]⟩
def cycle311_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle311_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data311 : PartitionData E W := ⟨6,![cycle311_0,cycle311_1,cycle311_2,cycle311_3,cycle311_4,cycle311_5]⟩
lemma valid_data311 : data311.Valid src311 dst311 Finset.univ := by decide +kernel

def src312 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,16,26,39,8,18,38,28,39]
def dst312 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle312_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle312_1 : CycleData E W := ⟨3,![2,1,15,18,7],![3,8,4,26,16]⟩
def cycle312_2 : CycleData E W := ⟨2,![3,12,13,8],![3,5,28,14]⟩
def cycle312_3 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle312_4 : CycleData E W := ⟨3,![21,9,14,19,25],![8,18,14,26,39]⟩
def cycle312_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data312 : PartitionData E W := ⟨6,![cycle312_0,cycle312_1,cycle312_2,cycle312_3,cycle312_4,cycle312_5]⟩
lemma valid_data312 : data312.Valid src312 dst312 Finset.univ := by decide +kernel

def src313 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,16,26,39,8,18,39,28,38]
def dst313 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle313_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle313_1 : CycleData E W := ⟨3,![2,1,15,18,7],![3,8,4,26,16]⟩
def cycle313_2 : CycleData E W := ⟨2,![3,12,13,8],![3,5,28,14]⟩
def cycle313_3 : CycleData E W := ⟨3,![6,17,25,21,10],![2,16,38,8,18]⟩
def cycle313_4 : CycleData E W := ⟨2,![9,22,19,14],![14,18,39,26]⟩
def cycle313_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data313 : PartitionData E W := ⟨6,![cycle313_0,cycle313_1,cycle313_2,cycle313_3,cycle313_4,cycle313_5]⟩
lemma valid_data313 : data313.Valid src313 dst313 Finset.univ := by decide +kernel

def src314 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst314 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle314_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle314_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle314_2 : CycleData E W := ⟨2,![4,16,22,12],![5,6,38,28]⟩
def cycle314_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle314_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle314_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data314 : PartitionData E W := ⟨6,![cycle314_0,cycle314_1,cycle314_2,cycle314_3,cycle314_4,cycle314_5]⟩
lemma valid_data314 : data314.Valid src314 dst314 Finset.univ := by decide +kernel

def src315 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,26,16,39,8,18,38,28,39]
def dst315 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle315_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle315_1 : CycleData E W := ⟨3,![2,1,15,18,7],![3,8,4,26,16]⟩
def cycle315_2 : CycleData E W := ⟨2,![3,12,13,8],![3,5,28,14]⟩
def cycle315_3 : CycleData E W := ⟨3,![6,19,25,21,10],![2,16,39,8,18]⟩
def cycle315_4 : CycleData E W := ⟨2,![9,22,17,14],![14,18,38,26]⟩
def cycle315_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data315 : PartitionData E W := ⟨6,![cycle315_0,cycle315_1,cycle315_2,cycle315_3,cycle315_4,cycle315_5]⟩
lemma valid_data315 : data315.Valid src315 dst315 Finset.univ := by decide +kernel

def src316 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,26,16,39,8,18,39,28,38]
def dst316 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle316_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,6]⟩
def cycle316_1 : CycleData E W := ⟨3,![2,1,15,18,7],![3,8,4,26,16]⟩
def cycle316_2 : CycleData E W := ⟨2,![3,12,13,8],![3,5,28,14]⟩
def cycle316_3 : CycleData E W := ⟨2,![6,19,22,10],![2,16,39,18]⟩
def cycle316_4 : CycleData E W := ⟨3,![21,9,14,17,25],![8,18,14,26,38]⟩
def cycle316_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data316 : PartitionData E W := ⟨6,![cycle316_0,cycle316_1,cycle316_2,cycle316_3,cycle316_4,cycle316_5]⟩
lemma valid_data316 : data316.Valid src316 dst316 Finset.univ := by decide +kernel

def src317 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst317 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle317_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle317_1 : CycleData E W := ⟨3,![3,11,15,14,8],![3,5,4,26,14]⟩
def cycle317_2 : CycleData E W := ⟨2,![4,20,24,12],![5,6,39,28]⟩
def cycle317_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle317_4 : CycleData E W := ⟨1,![9,23,13],![14,18,28]⟩
def cycle317_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data317 : PartitionData E W := ⟨6,![cycle317_0,cycle317_1,cycle317_2,cycle317_3,cycle317_4,cycle317_5]⟩
lemma valid_data317 : data317.Valid src317 dst317 Finset.univ := by decide +kernel

def src318 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,26,38,39,8,38,18,28,39]
def dst318 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle318_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle318_1 : CycleData E W := ⟨3,![2,1,11,17,7],![3,8,4,26,16]⟩
def cycle318_2 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle318_3 : CycleData E W := ⟨2,![4,20,24,14],![5,6,39,28]⟩
def cycle318_4 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle318_5 : CycleData E W := ⟨2,![9,22,18,12],![14,18,38,26]⟩
def cycle318_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data318 : PartitionData E W := ⟨7,![cycle318_0,cycle318_1,cycle318_2,cycle318_3,cycle318_4,cycle318_5,cycle318_6]⟩
lemma valid_data318 : data318.Valid src318 dst318 Finset.univ := by decide +kernel

def src319 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,26,39,38,8,38,28,18,39]
def dst319 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle319_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle319_1 : CycleData E W := ⟨3,![2,1,11,17,7],![3,8,4,26,16]⟩
def cycle319_2 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle319_3 : CycleData E W := ⟨2,![4,20,22,14],![5,6,38,28]⟩
def cycle319_4 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle319_5 : CycleData E W := ⟨2,![9,24,18,12],![14,18,39,26]⟩
def cycle319_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data319 : PartitionData E W := ⟨7,![cycle319_0,cycle319_1,cycle319_2,cycle319_3,cycle319_4,cycle319_5,cycle319_6]⟩
lemma valid_data319 : data319.Valid src319 dst319 Finset.univ := by decide +kernel

def src320 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,28,38,18,39]
def dst320 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle320_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle320_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle320_2 : CycleData E W := ⟨3,![4,16,17,22,14],![5,6,16,38,28]⟩
def cycle320_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle320_4 : CycleData E W := ⟨2,![9,23,18,12],![14,18,38,26]⟩
def cycle320_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def data320 : PartitionData E W := ⟨6,![cycle320_0,cycle320_1,cycle320_2,cycle320_3,cycle320_4,cycle320_5]⟩
lemma valid_data320 : data320.Valid src320 dst320 Finset.univ := by decide +kernel

def src321 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,28,39,18,38]
def dst321 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle321_0 : CycleData E W := ⟨3,![0,11,12,9,10],![2,4,26,14,18]⟩
def cycle321_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle321_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle321_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle321_4 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle321_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle321_6 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data321 : PartitionData E W := ⟨7,![cycle321_0,cycle321_1,cycle321_2,cycle321_3,cycle321_4,cycle321_5,cycle321_6]⟩
lemma valid_data321 : data321.Valid src321 dst321 Finset.univ := by decide +kernel

def src322 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,38,18,28,39]
def dst322 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle322_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle322_1 : CycleData E W := ⟨2,![1,25,19,11],![4,8,39,26]⟩
def cycle322_2 : CycleData E W := ⟨2,![2,21,17,7],![3,8,38,16]⟩
def cycle322_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle322_4 : CycleData E W := ⟨2,![4,20,24,14],![5,6,39,28]⟩
def cycle322_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle322_6 : CycleData E W := ⟨2,![9,22,18,12],![14,18,38,26]⟩
def data322 : PartitionData E W := ⟨7,![cycle322_0,cycle322_1,cycle322_2,cycle322_3,cycle322_4,cycle322_5,cycle322_6]⟩
lemma valid_data322 : data322.Valid src322 dst322 Finset.univ := by decide +kernel

def src323 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,38,28,18,39]
def dst323 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle323_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle323_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle323_2 : CycleData E W := ⟨3,![4,16,17,22,14],![5,6,16,38,28]⟩
def cycle323_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle323_4 : CycleData E W := ⟨3,![11,12,9,23,15],![4,26,14,18,28]⟩
def cycle323_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data323 : PartitionData E W := ⟨6,![cycle323_0,cycle323_1,cycle323_2,cycle323_3,cycle323_4,cycle323_5]⟩
lemma valid_data323 : data323.Valid src323 dst323 Finset.univ := by decide +kernel

def src324 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,38,39,26,8,38,28,18,39]
def dst324 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle324_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle324_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle324_2 : CycleData E W := ⟨3,![11,20,4,14,15],![4,26,6,5,28]⟩
def cycle324_3 : CycleData E W := ⟨4,![5,16,17,22,23,10],![2,6,16,38,28,18]⟩
def cycle324_4 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle324_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data324 : PartitionData E W := ⟨6,![cycle324_0,cycle324_1,cycle324_2,cycle324_3,cycle324_4,cycle324_5]⟩
lemma valid_data324 : data324.Valid src324 dst324 Finset.univ := by decide +kernel

def src325 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,28,38,18,39]
def dst325 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle325_0 : CycleData E W := ⟨3,![0,11,12,9,10],![2,4,26,14,18]⟩
def cycle325_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle325_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,39,16]⟩
def cycle325_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle325_4 : CycleData E W := ⟨2,![4,20,22,14],![5,6,38,28]⟩
def cycle325_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle325_6 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data325 : PartitionData E W := ⟨7,![cycle325_0,cycle325_1,cycle325_2,cycle325_3,cycle325_4,cycle325_5,cycle325_6]⟩
lemma valid_data325 : data325.Valid src325 dst325 Finset.univ := by decide +kernel

def src326 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,28,39,18,38]
def dst326 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle326_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle326_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle326_2 : CycleData E W := ⟨3,![4,16,17,22,14],![5,6,16,39,28]⟩
def cycle326_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,38,18]⟩
def cycle326_4 : CycleData E W := ⟨2,![9,23,18,12],![14,18,39,26]⟩
def cycle326_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,38,8,28]⟩
def data326 : PartitionData E W := ⟨6,![cycle326_0,cycle326_1,cycle326_2,cycle326_3,cycle326_4,cycle326_5]⟩
lemma valid_data326 : data326.Valid src326 dst326 Finset.univ := by decide +kernel

def src327 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,38,18,28,39]
def dst327 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle327_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle327_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle327_2 : CycleData E W := ⟨3,![5,4,14,23,10],![2,6,5,28,18]⟩
def cycle327_3 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def cycle327_4 : CycleData E W := ⟨2,![11,18,24,15],![4,26,39,28]⟩
def cycle327_5 : CycleData E W := ⟨3,![16,17,25,21,20],![6,16,39,8,38]⟩
def data327 : PartitionData E W := ⟨6,![cycle327_0,cycle327_1,cycle327_2,cycle327_3,cycle327_4,cycle327_5]⟩
lemma valid_data327 : data327.Valid src327 dst327 Finset.univ := by decide +kernel

def src328 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,38,28,18,39]
def dst328 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle328_0 : CycleData E W := ⟨2,![0,15,23,10],![2,4,28,18]⟩
def cycle328_1 : CycleData E W := ⟨2,![1,21,19,11],![4,8,38,26]⟩
def cycle328_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,39,16]⟩
def cycle328_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle328_4 : CycleData E W := ⟨2,![4,20,22,14],![5,6,38,28]⟩
def cycle328_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle328_6 : CycleData E W := ⟨2,![9,24,18,12],![14,18,39,26]⟩
def data328 : PartitionData E W := ⟨7,![cycle328_0,cycle328_1,cycle328_2,cycle328_3,cycle328_4,cycle328_5,cycle328_6]⟩
lemma valid_data328 : data328.Valid src328 dst328 Finset.univ := by decide +kernel

def src329 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,16,39,38,26,8,38,18,28,39]
def dst329 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle329_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle329_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle329_2 : CycleData E W := ⟨3,![11,20,4,14,15],![4,26,6,5,28]⟩
def cycle329_3 : CycleData E W := ⟨4,![5,16,17,24,23,10],![2,6,16,39,28,18]⟩
def cycle329_4 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def cycle329_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data329 : PartitionData E W := ⟨6,![cycle329_0,cycle329_1,cycle329_2,cycle329_3,cycle329_4,cycle329_5]⟩
lemma valid_data329 : data329.Valid src329 dst329 Finset.univ := by decide +kernel

def src330 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,16,38,39,8,38,28,18,39]
def dst330 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle330_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle330_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle330_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle330_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle330_4 : CycleData E W := ⟨4,![9,23,22,18,17,12],![14,18,28,38,16,26]⟩
def cycle330_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data330 : PartitionData E W := ⟨6,![cycle330_0,cycle330_1,cycle330_2,cycle330_3,cycle330_4,cycle330_5]⟩
lemma valid_data330 : data330.Valid src330 dst330 Finset.univ := by decide +kernel

def src331 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,16,39,38,8,38,18,28,39]
def dst331 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle331_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle331_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle331_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle331_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle331_4 : CycleData E W := ⟨4,![9,23,24,18,17,12],![14,18,28,39,16,26]⟩
def cycle331_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data331 : PartitionData E W := ⟨6,![cycle331_0,cycle331_1,cycle331_2,cycle331_3,cycle331_4,cycle331_5]⟩
lemma valid_data331 : data331.Valid src331 dst331 Finset.univ := by decide +kernel

def src332 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,18,38,28,39]
def dst332 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle332_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle332_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle332_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle332_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle332_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle332_5 : CycleData E W := ⟨2,![18,23,24,19],![16,38,28,39]⟩
def data332 : PartitionData E W := ⟨6,![cycle332_0,cycle332_1,cycle332_2,cycle332_3,cycle332_4,cycle332_5]⟩
lemma valid_data332 : data332.Valid src332 dst332 Finset.univ := by decide +kernel

def src333 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,18,39,28,38]
def dst333 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle333_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle333_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle333_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle333_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle333_4 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,38]⟩
def cycle333_5 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data333 : PartitionData E W := ⟨6,![cycle333_0,cycle333_1,cycle333_2,cycle333_3,cycle333_4,cycle333_5]⟩
lemma valid_data333 : data333.Valid src333 dst333 Finset.univ := by decide +kernel

def src334 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst334 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle334_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle334_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle334_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle334_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle334_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle334_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data334 : PartitionData E W := ⟨6,![cycle334_0,cycle334_1,cycle334_2,cycle334_3,cycle334_4,cycle334_5]⟩
lemma valid_data334 : data334.Valid src334 dst334 Finset.univ := by decide +kernel

def src335 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst335 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle335_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle335_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle335_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle335_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle335_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle335_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data335 : PartitionData E W := ⟨6,![cycle335_0,cycle335_1,cycle335_2,cycle335_3,cycle335_4,cycle335_5]⟩
lemma valid_data335 : data335.Valid src335 dst335 Finset.univ := by decide +kernel

def src336 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,18,38,28,39]
def dst336 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle336_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle336_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle336_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle336_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle336_4 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,39]⟩
def cycle336_5 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data336 : PartitionData E W := ⟨6,![cycle336_0,cycle336_1,cycle336_2,cycle336_3,cycle336_4,cycle336_5]⟩
lemma valid_data336 : data336.Valid src336 dst336 Finset.univ := by decide +kernel

def src337 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,18,39,28,38]
def dst337 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle337_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle337_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle337_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle337_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,38,8,18]⟩
def cycle337_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,39,26]⟩
def cycle337_5 : CycleData E W := ⟨2,![18,23,24,19],![16,39,28,38]⟩
def data337 : PartitionData E W := ⟨6,![cycle337_0,cycle337_1,cycle337_2,cycle337_3,cycle337_4,cycle337_5]⟩
lemma valid_data337 : data337.Valid src337 dst337 Finset.univ := by decide +kernel

def src338 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst338 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle338_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle338_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle338_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle338_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle338_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle338_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data338 : PartitionData E W := ⟨6,![cycle338_0,cycle338_1,cycle338_2,cycle338_3,cycle338_4,cycle338_5]⟩
lemma valid_data338 : data338.Valid src338 dst338 Finset.univ := by decide +kernel

def src339 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst339 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle339_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle339_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle339_2 : CycleData E W := ⟨3,![11,16,4,14,15],![4,26,6,5,28]⟩
def cycle339_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle339_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle339_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data339 : PartitionData E W := ⟨6,![cycle339_0,cycle339_1,cycle339_2,cycle339_3,cycle339_4,cycle339_5]⟩
lemma valid_data339 : data339.Valid src339 dst339 Finset.univ := by decide +kernel

def src340 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,28,38,39]
def dst340 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle340_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle340_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle340_2 : CycleData E W := ⟨3,![5,4,14,22,10],![2,6,5,28,18]⟩
def cycle340_3 : CycleData E W := ⟨3,![21,9,12,19,25],![8,18,14,26,39]⟩
def cycle340_4 : CycleData E W := ⟨3,![11,18,17,23,15],![4,26,16,38,28]⟩
def cycle340_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data340 : PartitionData E W := ⟨6,![cycle340_0,cycle340_1,cycle340_2,cycle340_3,cycle340_4,cycle340_5]⟩
lemma valid_data340 : data340.Valid src340 dst340 Finset.univ := by decide +kernel

def src341 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,38,28,39]
def dst341 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle341_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle341_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle341_2 : CycleData E W := ⟨2,![4,16,23,14],![5,6,38,28]⟩
def cycle341_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle341_4 : CycleData E W := ⟨3,![9,22,17,18,12],![14,18,38,16,26]⟩
def cycle341_5 : CycleData E W := ⟨2,![11,19,24,15],![4,26,39,28]⟩
def data341 : PartitionData E W := ⟨6,![cycle341_0,cycle341_1,cycle341_2,cycle341_3,cycle341_4,cycle341_5]⟩
lemma valid_data341 : data341.Valid src341 dst341 Finset.univ := by decide +kernel

def src342 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,39,28,38]
def dst342 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle342_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle342_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle342_2 : CycleData E W := ⟨2,![4,20,23,14],![5,6,39,28]⟩
def cycle342_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle342_4 : CycleData E W := ⟨2,![9,22,19,12],![14,18,39,26]⟩
def cycle342_5 : CycleData E W := ⟨3,![11,18,17,24,15],![4,26,16,38,28]⟩
def data342 : PartitionData E W := ⟨6,![cycle342_0,cycle342_1,cycle342_2,cycle342_3,cycle342_4,cycle342_5]⟩
lemma valid_data342 : data342.Valid src342 dst342 Finset.univ := by decide +kernel

def src343 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,39,38,28]
def dst343 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle343_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle343_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle343_2 : CycleData E W := ⟨2,![4,16,24,14],![5,6,38,28]⟩
def cycle343_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle343_4 : CycleData E W := ⟨4,![11,12,9,21,25,15],![4,26,14,18,8,28]⟩
def cycle343_5 : CycleData E W := ⟨2,![17,23,19,18],![16,38,39,26]⟩
def data343 : PartitionData E W := ⟨6,![cycle343_0,cycle343_1,cycle343_2,cycle343_3,cycle343_4,cycle343_5]⟩
lemma valid_data343 : data343.Valid src343 dst343 Finset.univ := by decide +kernel

def src344 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,28,18,39,38]
def dst344 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle344_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle344_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle344_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle344_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle344_4 : CycleData E W := ⟨3,![5,4,14,22,10],![2,6,5,28,18]⟩
def cycle344_5 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle344_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data344 : PartitionData E W := ⟨7,![cycle344_0,cycle344_1,cycle344_2,cycle344_3,cycle344_4,cycle344_5,cycle344_6]⟩
lemma valid_data344 : data344.Valid src344 dst344 Finset.univ := by decide +kernel

def src345 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst345 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle345_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle345_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle345_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle345_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle345_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle345_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def data345 : PartitionData E W := ⟨6,![cycle345_0,cycle345_1,cycle345_2,cycle345_3,cycle345_4,cycle345_5]⟩
lemma valid_data345 : data345.Valid src345 dst345 Finset.univ := by decide +kernel

def src346 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst346 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle346_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle346_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle346_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle346_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle346_4 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle346_5 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle346_6 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def data346 : PartitionData E W := ⟨7,![cycle346_0,cycle346_1,cycle346_2,cycle346_3,cycle346_4,cycle346_5,cycle346_6]⟩
lemma valid_data346 : data346.Valid src346 dst346 Finset.univ := by decide +kernel

def src347 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst347 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle347_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle347_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle347_2 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle347_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle347_4 : CycleData E W := ⟨3,![11,12,9,23,15],![4,26,14,18,28]⟩
def cycle347_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data347 : PartitionData E W := ⟨6,![cycle347_0,cycle347_1,cycle347_2,cycle347_3,cycle347_4,cycle347_5]⟩
lemma valid_data347 : data347.Valid src347 dst347 Finset.univ := by decide +kernel

def src348 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,28,39,38]
def dst348 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle348_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle348_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle348_2 : CycleData E W := ⟨3,![5,4,14,22,10],![2,6,5,28,18]⟩
def cycle348_3 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,38]⟩
def cycle348_4 : CycleData E W := ⟨3,![11,18,19,23,15],![4,26,16,39,28]⟩
def cycle348_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data348 : PartitionData E W := ⟨6,![cycle348_0,cycle348_1,cycle348_2,cycle348_3,cycle348_4,cycle348_5]⟩
lemma valid_data348 : data348.Valid src348 dst348 Finset.univ := by decide +kernel

def src349 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,38,28,39]
def dst349 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle349_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle349_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle349_2 : CycleData E W := ⟨2,![4,16,23,14],![5,6,38,28]⟩
def cycle349_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle349_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle349_5 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def data349 : PartitionData E W := ⟨6,![cycle349_0,cycle349_1,cycle349_2,cycle349_3,cycle349_4,cycle349_5]⟩
lemma valid_data349 : data349.Valid src349 dst349 Finset.univ := by decide +kernel

def lookupB6 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data300 else (if j < 2 then data301 else data302)) else (if j < 4 then data303 else (if j < 5 then data304 else data305))) else (if j < 9 then (if j < 7 then data306 else (if j < 8 then data307 else data308)) else (if j < 10 then data309 else (if j < 11 then data310 else data311)))) else (if j < 18 then (if j < 15 then (if j < 13 then data312 else (if j < 14 then data313 else data314)) else (if j < 16 then data315 else (if j < 17 then data316 else data317))) else (if j < 21 then (if j < 19 then data318 else (if j < 20 then data319 else data320)) else (if j < 23 then (if j < 22 then data321 else data322) else (if j < 24 then data323 else data324))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data325 else (if j < 27 then data326 else data327)) else (if j < 29 then data328 else (if j < 30 then data329 else data330))) else (if j < 34 then (if j < 32 then data331 else (if j < 33 then data332 else data333)) else (if j < 35 then data334 else (if j < 36 then data335 else data336)))) else (if j < 43 then (if j < 40 then (if j < 38 then data337 else (if j < 39 then data338 else data339)) else (if j < 41 then data340 else (if j < 42 then data341 else data342))) else (if j < 46 then (if j < 44 then data343 else (if j < 45 then data344 else data345)) else (if j < 48 then (if j < 47 then data346 else data347) else (if j < 49 then data348 else data349))))))

def srcTableB6 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src300 else (if j < 2 then src301 else src302)) else (if j < 4 then src303 else (if j < 5 then src304 else src305))) else (if j < 9 then (if j < 7 then src306 else (if j < 8 then src307 else src308)) else (if j < 10 then src309 else (if j < 11 then src310 else src311)))) else (if j < 18 then (if j < 15 then (if j < 13 then src312 else (if j < 14 then src313 else src314)) else (if j < 16 then src315 else (if j < 17 then src316 else src317))) else (if j < 21 then (if j < 19 then src318 else (if j < 20 then src319 else src320)) else (if j < 23 then (if j < 22 then src321 else src322) else (if j < 24 then src323 else src324))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src325 else (if j < 27 then src326 else src327)) else (if j < 29 then src328 else (if j < 30 then src329 else src330))) else (if j < 34 then (if j < 32 then src331 else (if j < 33 then src332 else src333)) else (if j < 35 then src334 else (if j < 36 then src335 else src336)))) else (if j < 43 then (if j < 40 then (if j < 38 then src337 else (if j < 39 then src338 else src339)) else (if j < 41 then src340 else (if j < 42 then src341 else src342))) else (if j < 46 then (if j < 44 then src343 else (if j < 45 then src344 else src345)) else (if j < 48 then (if j < 47 then src346 else src347) else (if j < 49 then src348 else src349))))))

def dstTableB6 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst300 else (if j < 2 then dst301 else dst302)) else (if j < 4 then dst303 else (if j < 5 then dst304 else dst305))) else (if j < 9 then (if j < 7 then dst306 else (if j < 8 then dst307 else dst308)) else (if j < 10 then dst309 else (if j < 11 then dst310 else dst311)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst312 else (if j < 14 then dst313 else dst314)) else (if j < 16 then dst315 else (if j < 17 then dst316 else dst317))) else (if j < 21 then (if j < 19 then dst318 else (if j < 20 then dst319 else dst320)) else (if j < 23 then (if j < 22 then dst321 else dst322) else (if j < 24 then dst323 else dst324))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst325 else (if j < 27 then dst326 else dst327)) else (if j < 29 then dst328 else (if j < 30 then dst329 else dst330))) else (if j < 34 then (if j < 32 then dst331 else (if j < 33 then dst332 else dst333)) else (if j < 35 then dst334 else (if j < 36 then dst335 else dst336)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst337 else (if j < 39 then dst338 else dst339)) else (if j < 41 then dst340 else (if j < 42 then dst341 else dst342))) else (if j < 46 then (if j < 44 then dst343 else (if j < 45 then dst344 else dst345)) else (if j < 48 then (if j < 47 then dst346 else dst347) else (if j < 49 then dst348 else dst349))))))

def caseB6 (i : Fin 50) : Cases := ⟨300 + i.val,by have := i.isLt; omega⟩
lemma tableB6_valid (i : Fin 50) :
    (lookupB6 i.val).Valid (srcTableB6 i.val) (dstTableB6 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB6_row : ∀ (i : Fin 50) (e : E),
    srcTableB6 i.val e = caseSource (caseB6 i) e := by decide +kernel

lemma dstB6_row : ∀ (i : Fin 50) (e : E),
    dstTableB6 i.val e = caseTarget (caseB6 i) e := by decide +kernel

lemma sizeB6 : ∀ i : Fin 50, (lookupB6 i.val).size ≤ 5 →
    (lookupB6 i.val).size = 2 ∧
      (⟨caseKey (caseB6 i),caseKey_lt (caseB6 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB6 (i : Fin 50) : Certificate (caseB6 i) := by
  refine ⟨lookupB6 i.val,?_,sizeB6 i⟩
  have hv := tableB6_valid i
  rw [funext (srcB6_row i),funext (dstB6_row i)] at hv
  exact hv
lemma certificateInterval6 : FiniteIntervals.Covers CertificateAt 300 350 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 300 50 (fun i _ => certificateB6 i)
#print axioms certificateInterval6
end Erdos184Work.FiveRows4

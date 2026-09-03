import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src350 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,38,39,28]
def dst350 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle350_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle350_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle350_2 : CycleData E W := ⟨2,![4,20,24,14],![5,6,39,28]⟩
def cycle350_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle350_4 : CycleData E W := ⟨4,![11,12,9,21,25,15],![4,26,14,18,8,28]⟩
def cycle350_5 : CycleData E W := ⟨2,![18,17,23,19],![16,26,38,39]⟩
def data350 : PartitionData E W := ⟨6,![cycle350_0,cycle350_1,cycle350_2,cycle350_3,cycle350_4,cycle350_5]⟩
lemma valid_data350 : data350.Valid src350 dst350 Finset.univ := by decide +kernel

def src351 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,39,28,38]
def dst351 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle351_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle351_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle351_2 : CycleData E W := ⟨2,![4,20,23,14],![5,6,39,28]⟩
def cycle351_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle351_4 : CycleData E W := ⟨3,![9,22,19,18,12],![14,18,39,16,26]⟩
def cycle351_5 : CycleData E W := ⟨2,![11,17,24,15],![4,26,38,28]⟩
def data351 : PartitionData E W := ⟨6,![cycle351_0,cycle351_1,cycle351_2,cycle351_3,cycle351_4,cycle351_5]⟩
lemma valid_data351 : data351.Valid src351 dst351 Finset.univ := by decide +kernel

def src352 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,28,18,38,39]
def dst352 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle352_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle352_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle352_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle352_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle352_4 : CycleData E W := ⟨3,![5,4,14,22,10],![2,6,5,28,18]⟩
def cycle352_5 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle352_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data352 : PartitionData E W := ⟨7,![cycle352_0,cycle352_1,cycle352_2,cycle352_3,cycle352_4,cycle352_5,cycle352_6]⟩
lemma valid_data352 : data352.Valid src352 dst352 Finset.univ := by decide +kernel

def src353 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst353 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle353_0 : CycleData E W := ⟨2,![0,11,18,6],![2,4,26,16]⟩
def cycle353_1 : CycleData E W := ⟨1,![1,21,15],![4,8,28]⟩
def cycle353_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle353_3 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle353_4 : CycleData E W := ⟨2,![4,16,22,14],![5,6,38,28]⟩
def cycle353_5 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle353_6 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def data353 : PartitionData E W := ⟨7,![cycle353_0,cycle353_1,cycle353_2,cycle353_3,cycle353_4,cycle353_5,cycle353_6]⟩
lemma valid_data353 : data353.Valid src353 dst353 Finset.univ := by decide +kernel

def src354 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst354 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle354_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle354_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle354_2 : CycleData E W := ⟨2,![4,20,22,14],![5,6,39,28]⟩
def cycle354_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle354_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle354_5 : CycleData E W := ⟨3,![11,17,25,21,15],![4,26,38,8,28]⟩
def data354 : PartitionData E W := ⟨6,![cycle354_0,cycle354_1,cycle354_2,cycle354_3,cycle354_4,cycle354_5]⟩
lemma valid_data354 : data354.Valid src354 dst354 Finset.univ := by decide +kernel

def src355 : E → W := ![2,4,8,3,5,6,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst355 : E → W := ![4,8,3,5,6,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle355_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle355_1 : CycleData E W := ⟨1,![3,13,8],![3,5,14]⟩
def cycle355_2 : CycleData E W := ⟨3,![5,4,14,23,10],![2,6,5,28,18]⟩
def cycle355_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle355_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle355_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data355 : PartitionData E W := ⟨6,![cycle355_0,cycle355_1,cycle355_2,cycle355_3,cycle355_4,cycle355_5]⟩
lemma valid_data355 : data355.Valid src355 dst355 Finset.univ := by decide +kernel

def src356 : E → W := ![2,4,8,3,6,5,2,3,14,16,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst356 : E → W := ![4,8,3,6,5,2,3,14,16,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle356_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle356_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,6,5,28,14]⟩
def cycle356_2 : CycleData E W := ⟨3,![5,14,19,24,10],![2,5,26,39,18]⟩
def cycle356_3 : CycleData E W := ⟨2,![11,8,18,15],![4,14,16,26]⟩
def cycle356_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle356_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data356 : PartitionData E W := ⟨6,![cycle356_0,cycle356_1,cycle356_2,cycle356_3,cycle356_4,cycle356_5]⟩
lemma valid_data356 : data356.Valid src356 dst356 Finset.univ := by decide +kernel

def src357 : E → W := ![2,4,8,3,6,5,2,3,14,16,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst357 : E → W := ![4,8,3,6,5,2,3,14,16,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle357_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle357_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,6,5,28,14]⟩
def cycle357_2 : CycleData E W := ⟨3,![5,14,17,22,10],![2,5,26,38,18]⟩
def cycle357_3 : CycleData E W := ⟨2,![11,8,18,15],![4,14,16,26]⟩
def cycle357_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle357_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data357 : PartitionData E W := ⟨6,![cycle357_0,cycle357_1,cycle357_2,cycle357_3,cycle357_4,cycle357_5]⟩
lemma valid_data357 : data357.Valid src357 dst357 Finset.univ := by decide +kernel

def src358 : E → W := ![2,4,8,3,6,5,2,3,14,16,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst358 : E → W := ![4,8,3,6,5,2,3,14,16,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle358_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle358_1 : CycleData E W := ⟨2,![3,4,13,7],![3,6,5,14]⟩
def cycle358_2 : CycleData E W := ⟨4,![5,14,22,17,9,10],![2,5,28,38,16,18]⟩
def cycle358_3 : CycleData E W := ⟨1,![8,18,12],![14,16,26]⟩
def cycle358_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle358_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data358 : PartitionData E W := ⟨6,![cycle358_0,cycle358_1,cycle358_2,cycle358_3,cycle358_4,cycle358_5]⟩
lemma valid_data358 : data358.Valid src358 dst358 Finset.univ := by decide +kernel

def src359 : E → W := ![2,4,8,3,6,5,2,3,14,16,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst359 : E → W := ![4,8,3,6,5,2,3,14,16,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle359_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle359_1 : CycleData E W := ⟨2,![3,4,13,7],![3,6,5,14]⟩
def cycle359_2 : CycleData E W := ⟨5,![5,14,15,11,17,22,10],![2,5,28,4,26,38,18]⟩
def cycle359_3 : CycleData E W := ⟨1,![8,18,12],![14,16,26]⟩
def cycle359_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle359_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data359 : PartitionData E W := ⟨6,![cycle359_0,cycle359_1,cycle359_2,cycle359_3,cycle359_4,cycle359_5]⟩
lemma valid_data359 : data359.Valid src359 dst359 Finset.univ := by decide +kernel

def src360 : E → W := ![2,4,8,3,6,5,2,3,14,18,16,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst360 : E → W := ![4,8,3,6,5,2,3,14,18,16,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle360_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle360_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,6,5,28,14]⟩
def cycle360_2 : CycleData E W := ⟨2,![5,14,18,10],![2,5,26,16]⟩
def cycle360_3 : CycleData E W := ⟨3,![11,8,24,19,15],![4,14,18,39,26]⟩
def cycle360_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle360_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data360 : PartitionData E W := ⟨6,![cycle360_0,cycle360_1,cycle360_2,cycle360_3,cycle360_4,cycle360_5]⟩
lemma valid_data360 : data360.Valid src360 dst360 Finset.univ := by decide +kernel

def src361 : E → W := ![2,4,8,3,6,5,2,3,14,18,16,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst361 : E → W := ![4,8,3,6,5,2,3,14,18,16,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle361_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle361_1 : CycleData E W := ⟨3,![3,4,13,12,7],![3,6,5,28,14]⟩
def cycle361_2 : CycleData E W := ⟨2,![5,14,18,10],![2,5,26,16]⟩
def cycle361_3 : CycleData E W := ⟨3,![11,8,22,17,15],![4,14,18,38,26]⟩
def cycle361_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle361_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data361 : PartitionData E W := ⟨6,![cycle361_0,cycle361_1,cycle361_2,cycle361_3,cycle361_4,cycle361_5]⟩
lemma valid_data361 : data361.Valid src361 dst361 Finset.univ := by decide +kernel

def src362 : E → W := ![2,4,8,3,6,5,2,3,14,18,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst362 : E → W := ![4,8,3,6,5,2,3,14,18,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle362_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle362_1 : CycleData E W := ⟨2,![3,4,13,7],![3,6,5,14]⟩
def cycle362_2 : CycleData E W := ⟨4,![5,14,15,11,18,10],![2,5,28,4,26,16]⟩
def cycle362_3 : CycleData E W := ⟨2,![8,24,19,12],![14,18,39,26]⟩
def cycle362_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle362_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data362 : PartitionData E W := ⟨6,![cycle362_0,cycle362_1,cycle362_2,cycle362_3,cycle362_4,cycle362_5]⟩
lemma valid_data362 : data362.Valid src362 dst362 Finset.univ := by decide +kernel

def src363 : E → W := ![2,4,8,3,6,5,2,3,14,18,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst363 : E → W := ![4,8,3,6,5,2,3,14,18,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle363_0 : CycleData E W := ⟨2,![0,1,2,6],![2,4,8,3]⟩
def cycle363_1 : CycleData E W := ⟨2,![3,4,13,7],![3,6,5,14]⟩
def cycle363_2 : CycleData E W := ⟨4,![5,14,15,11,18,10],![2,5,28,4,26,16]⟩
def cycle363_3 : CycleData E W := ⟨2,![8,22,17,12],![14,18,38,26]⟩
def cycle363_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle363_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data363 : PartitionData E W := ⟨6,![cycle363_0,cycle363_1,cycle363_2,cycle363_3,cycle363_4,cycle363_5]⟩
lemma valid_data363 : data363.Valid src363 dst363 Finset.univ := by decide +kernel

def src364 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,38,18,28,39]
def dst364 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle364_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle364_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle364_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle364_3 : CycleData E W := ⟨2,![9,22,18,12],![14,18,38,26]⟩
def cycle364_4 : CycleData E W := ⟨2,![11,19,24,15],![4,26,39,28]⟩
def cycle364_5 : CycleData E W := ⟨3,![16,17,21,25,20],![6,16,38,8,39]⟩
def data364 : PartitionData E W := ⟨6,![cycle364_0,cycle364_1,cycle364_2,cycle364_3,cycle364_4,cycle364_5]⟩
lemma valid_data364 : data364.Valid src364 dst364 Finset.univ := by decide +kernel

def src365 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,16,38,26,39,8,38,28,18,39]
def dst365 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle365_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle365_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle365_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle365_3 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle365_4 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def cycle365_5 : CycleData E W := ⟨3,![16,17,21,25,20],![6,16,38,8,39]⟩
def data365 : PartitionData E W := ⟨6,![cycle365_0,cycle365_1,cycle365_2,cycle365_3,cycle365_4,cycle365_5]⟩
lemma valid_data365 : data365.Valid src365 dst365 Finset.univ := by decide +kernel

def src366 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,38,18,28,39]
def dst366 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle366_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle366_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle366_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle366_3 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def cycle366_4 : CycleData E W := ⟨2,![11,18,24,15],![4,26,39,28]⟩
def cycle366_5 : CycleData E W := ⟨3,![16,17,25,21,20],![6,16,39,8,38]⟩
def data366 : PartitionData E W := ⟨6,![cycle366_0,cycle366_1,cycle366_2,cycle366_3,cycle366_4,cycle366_5]⟩
lemma valid_data366 : data366.Valid src366 dst366 Finset.univ := by decide +kernel

def src367 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,16,39,26,38,8,38,28,18,39]
def dst367 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle367_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle367_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle367_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle367_3 : CycleData E W := ⟨2,![9,24,18,12],![14,18,39,26]⟩
def cycle367_4 : CycleData E W := ⟨2,![11,19,22,15],![4,26,38,28]⟩
def cycle367_5 : CycleData E W := ⟨3,![16,17,25,21,20],![6,16,39,8,38]⟩
def data367 : PartitionData E W := ⟨6,![cycle367_0,cycle367_1,cycle367_2,cycle367_3,cycle367_4,cycle367_5]⟩
lemma valid_data367 : data367.Valid src367 dst367 Finset.univ := by decide +kernel

def src368 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,38,28,39]
def dst368 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle368_0 : CycleData E W := ⟨3,![0,11,12,13,5],![2,4,26,14,5]⟩
def cycle368_1 : CycleData E W := ⟨2,![1,25,24,15],![4,8,39,28]⟩
def cycle368_2 : CycleData E W := ⟨2,![2,21,9,8],![3,8,18,14]⟩
def cycle368_3 : CycleData E W := ⟨3,![3,20,19,18,7],![3,6,39,26,16]⟩
def cycle368_4 : CycleData E W := ⟨2,![4,16,23,14],![5,6,38,28]⟩
def cycle368_5 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def data368 : PartitionData E W := ⟨6,![cycle368_0,cycle368_1,cycle368_2,cycle368_3,cycle368_4,cycle368_5]⟩
lemma valid_data368 : data368.Valid src368 dst368 Finset.univ := by decide +kernel

def src369 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,18,39,28,38]
def dst369 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle369_0 : CycleData E W := ⟨3,![0,11,12,13,5],![2,4,26,14,5]⟩
def cycle369_1 : CycleData E W := ⟨2,![1,25,24,15],![4,8,38,28]⟩
def cycle369_2 : CycleData E W := ⟨2,![2,21,9,8],![3,8,18,14]⟩
def cycle369_3 : CycleData E W := ⟨2,![3,16,17,7],![3,6,38,16]⟩
def cycle369_4 : CycleData E W := ⟨2,![4,20,23,14],![5,6,39,28]⟩
def cycle369_5 : CycleData E W := ⟨3,![6,18,19,22,10],![2,16,26,39,18]⟩
def data369 : PartitionData E W := ⟨6,![cycle369_0,cycle369_1,cycle369_2,cycle369_3,cycle369_4,cycle369_5]⟩
lemma valid_data369 : data369.Valid src369 dst369 Finset.univ := by decide +kernel

def src370 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst370 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle370_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle370_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle370_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle370_3 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle370_4 : CycleData E W := ⟨3,![11,18,17,22,15],![4,26,16,38,28]⟩
def cycle370_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data370 : PartitionData E W := ⟨6,![cycle370_0,cycle370_1,cycle370_2,cycle370_3,cycle370_4,cycle370_5]⟩
lemma valid_data370 : data370.Valid src370 dst370 Finset.univ := by decide +kernel

def src371 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,38,28,39]
def dst371 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle371_0 : CycleData E W := ⟨3,![0,11,12,13,5],![2,4,26,14,5]⟩
def cycle371_1 : CycleData E W := ⟨2,![1,25,24,15],![4,8,39,28]⟩
def cycle371_2 : CycleData E W := ⟨2,![2,21,9,8],![3,8,18,14]⟩
def cycle371_3 : CycleData E W := ⟨2,![3,20,19,7],![3,6,39,16]⟩
def cycle371_4 : CycleData E W := ⟨2,![4,16,23,14],![5,6,38,28]⟩
def cycle371_5 : CycleData E W := ⟨3,![6,18,17,22,10],![2,16,26,38,18]⟩
def data371 : PartitionData E W := ⟨6,![cycle371_0,cycle371_1,cycle371_2,cycle371_3,cycle371_4,cycle371_5]⟩
lemma valid_data371 : data371.Valid src371 dst371 Finset.univ := by decide +kernel

def src372 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,18,39,28,38]
def dst372 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle372_0 : CycleData E W := ⟨3,![0,11,12,13,5],![2,4,26,14,5]⟩
def cycle372_1 : CycleData E W := ⟨2,![1,25,24,15],![4,8,38,28]⟩
def cycle372_2 : CycleData E W := ⟨2,![2,21,9,8],![3,8,18,14]⟩
def cycle372_3 : CycleData E W := ⟨3,![3,16,17,18,7],![3,6,38,26,16]⟩
def cycle372_4 : CycleData E W := ⟨2,![4,20,23,14],![5,6,39,28]⟩
def cycle372_5 : CycleData E W := ⟨2,![6,19,22,10],![2,16,39,18]⟩
def data372 : PartitionData E W := ⟨6,![cycle372_0,cycle372_1,cycle372_2,cycle372_3,cycle372_4,cycle372_5]⟩
lemma valid_data372 : data372.Valid src372 dst372 Finset.univ := by decide +kernel

def src373 : E → W := ![2,4,8,3,6,5,2,16,3,14,18,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst373 : E → W := ![4,8,3,6,5,2,16,3,14,18,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle373_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,4,8,3,16]⟩
def cycle373_1 : CycleData E W := ⟨2,![3,4,13,8],![3,6,5,14]⟩
def cycle373_2 : CycleData E W := ⟨2,![5,14,23,10],![2,5,28,18]⟩
def cycle373_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle373_4 : CycleData E W := ⟨3,![11,18,19,24,15],![4,26,16,39,28]⟩
def cycle373_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data373 : PartitionData E W := ⟨6,![cycle373_0,cycle373_1,cycle373_2,cycle373_3,cycle373_4,cycle373_5]⟩
lemma valid_data373 : data373.Valid src373 dst373 Finset.univ := by decide +kernel

def src374 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,38,18,28,39]
def dst374 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle374_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle374_1 : CycleData E W := ⟨2,![1,21,18,15],![4,8,38,26]⟩
def cycle374_2 : CycleData E W := ⟨2,![2,25,20,3],![3,8,39,6]⟩
def cycle374_3 : CycleData E W := ⟨4,![5,4,16,17,22,10],![2,5,6,16,38,18]⟩
def cycle374_4 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def cycle374_5 : CycleData E W := ⟨2,![13,24,19,14],![5,28,39,26]⟩
def data374 : PartitionData E W := ⟨6,![cycle374_0,cycle374_1,cycle374_2,cycle374_3,cycle374_4,cycle374_5]⟩
lemma valid_data374 : data374.Valid src374 dst374 Finset.univ := by decide +kernel

def src375 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,16,38,26,39,8,38,28,18,39]
def dst375 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle375_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle375_1 : CycleData E W := ⟨2,![1,21,18,15],![4,8,38,26]⟩
def cycle375_2 : CycleData E W := ⟨2,![2,25,20,3],![3,8,39,6]⟩
def cycle375_3 : CycleData E W := ⟨3,![4,16,17,22,13],![5,6,16,38,28]⟩
def cycle375_4 : CycleData E W := ⟨3,![5,14,19,24,10],![2,5,26,39,18]⟩
def cycle375_5 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def data375 : PartitionData E W := ⟨6,![cycle375_0,cycle375_1,cycle375_2,cycle375_3,cycle375_4,cycle375_5]⟩
lemma valid_data375 : data375.Valid src375 dst375 Finset.univ := by decide +kernel

def src376 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,38,18,28,39]
def dst376 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle376_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle376_1 : CycleData E W := ⟨2,![1,21,19,15],![4,8,38,26]⟩
def cycle376_2 : CycleData E W := ⟨3,![2,25,17,16,3],![3,8,39,16,6]⟩
def cycle376_3 : CycleData E W := ⟨3,![5,4,20,22,10],![2,5,6,38,18]⟩
def cycle376_4 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def cycle376_5 : CycleData E W := ⟨2,![13,24,18,14],![5,28,39,26]⟩
def data376 : PartitionData E W := ⟨6,![cycle376_0,cycle376_1,cycle376_2,cycle376_3,cycle376_4,cycle376_5]⟩
lemma valid_data376 : data376.Valid src376 dst376 Finset.univ := by decide +kernel

def src377 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,38,28,18,39]
def dst377 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle377_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle377_1 : CycleData E W := ⟨2,![1,21,19,15],![4,8,38,26]⟩
def cycle377_2 : CycleData E W := ⟨3,![2,25,17,16,3],![3,8,39,16,6]⟩
def cycle377_3 : CycleData E W := ⟨2,![4,20,22,13],![5,6,38,28]⟩
def cycle377_4 : CycleData E W := ⟨3,![5,14,18,24,10],![2,5,26,39,18]⟩
def cycle377_5 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def data377 : PartitionData E W := ⟨6,![cycle377_0,cycle377_1,cycle377_2,cycle377_3,cycle377_4,cycle377_5]⟩
lemma valid_data377 : data377.Valid src377 dst377 Finset.univ := by decide +kernel

def src378 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,38,28,39]
def dst378 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle378_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle378_1 : CycleData E W := ⟨2,![1,25,19,15],![4,8,39,26]⟩
def cycle378_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle378_3 : CycleData E W := ⟨3,![3,4,13,12,8],![3,6,5,28,14]⟩
def cycle378_4 : CycleData E W := ⟨4,![5,14,18,17,22,10],![2,5,26,16,38,18]⟩
def cycle378_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data378 : PartitionData E W := ⟨6,![cycle378_0,cycle378_1,cycle378_2,cycle378_3,cycle378_4,cycle378_5]⟩
lemma valid_data378 : data378.Valid src378 dst378 Finset.univ := by decide +kernel

def src379 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,28,38]
def dst379 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle379_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle379_1 : CycleData E W := ⟨3,![1,25,17,18,15],![4,8,38,16,26]⟩
def cycle379_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle379_3 : CycleData E W := ⟨3,![3,4,13,12,8],![3,6,5,28,14]⟩
def cycle379_4 : CycleData E W := ⟨3,![5,14,19,22,10],![2,5,26,39,18]⟩
def cycle379_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data379 : PartitionData E W := ⟨6,![cycle379_0,cycle379_1,cycle379_2,cycle379_3,cycle379_4,cycle379_5]⟩
lemma valid_data379 : data379.Valid src379 dst379 Finset.univ := by decide +kernel

def src380 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst380 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle380_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle380_1 : CycleData E W := ⟨3,![1,21,17,18,15],![4,8,38,16,26]⟩
def cycle380_2 : CycleData E W := ⟨2,![2,25,20,3],![3,8,39,6]⟩
def cycle380_3 : CycleData E W := ⟨2,![4,16,22,13],![5,6,38,28]⟩
def cycle380_4 : CycleData E W := ⟨3,![5,14,19,24,10],![2,5,26,39,18]⟩
def cycle380_5 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def data380 : PartitionData E W := ⟨6,![cycle380_0,cycle380_1,cycle380_2,cycle380_3,cycle380_4,cycle380_5]⟩
lemma valid_data380 : data380.Valid src380 dst380 Finset.univ := by decide +kernel

def src381 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,28,39]
def dst381 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle381_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle381_1 : CycleData E W := ⟨3,![1,25,19,18,15],![4,8,39,16,26]⟩
def cycle381_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle381_3 : CycleData E W := ⟨3,![3,4,13,12,8],![3,6,5,28,14]⟩
def cycle381_4 : CycleData E W := ⟨3,![5,14,17,22,10],![2,5,26,38,18]⟩
def cycle381_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data381 : PartitionData E W := ⟨6,![cycle381_0,cycle381_1,cycle381_2,cycle381_3,cycle381_4,cycle381_5]⟩
lemma valid_data381 : data381.Valid src381 dst381 Finset.univ := by decide +kernel

def src382 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,39,28,38]
def dst382 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle382_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle382_1 : CycleData E W := ⟨2,![1,25,17,15],![4,8,38,26]⟩
def cycle382_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle382_3 : CycleData E W := ⟨3,![3,4,13,12,8],![3,6,5,28,14]⟩
def cycle382_4 : CycleData E W := ⟨4,![5,14,18,19,22,10],![2,5,26,16,39,18]⟩
def cycle382_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data382 : PartitionData E W := ⟨6,![cycle382_0,cycle382_1,cycle382_2,cycle382_3,cycle382_4,cycle382_5]⟩
lemma valid_data382 : data382.Valid src382 dst382 Finset.univ := by decide +kernel

def src383 : E → W := ![2,4,8,3,6,5,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst383 : E → W := ![4,8,3,6,5,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle383_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle383_1 : CycleData E W := ⟨2,![1,21,17,15],![4,8,38,26]⟩
def cycle383_2 : CycleData E W := ⟨2,![2,25,20,3],![3,8,39,6]⟩
def cycle383_3 : CycleData E W := ⟨3,![5,4,16,22,10],![2,5,6,38,18]⟩
def cycle383_4 : CycleData E W := ⟨2,![8,12,23,9],![3,14,28,18]⟩
def cycle383_5 : CycleData E W := ⟨3,![13,24,19,18,14],![5,28,39,16,26]⟩
def data383 : PartitionData E W := ⟨6,![cycle383_0,cycle383_1,cycle383_2,cycle383_3,cycle383_4,cycle383_5]⟩
lemma valid_data383 : data383.Valid src383 dst383 Finset.univ := by decide +kernel

def src384 : E → W := ![2,4,8,6,3,5,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst384 : E → W := ![4,8,6,3,5,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle384_0 : CycleData E W := ⟨3,![0,11,8,4,5],![2,4,14,3,5]⟩
def cycle384_1 : CycleData E W := ⟨2,![1,21,22,15],![4,8,38,28]⟩
def cycle384_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle384_3 : CycleData E W := ⟨2,![3,16,17,7],![3,6,38,16]⟩
def cycle384_4 : CycleData E W := ⟨3,![6,18,12,9,10],![2,16,26,14,18]⟩
def cycle384_5 : CycleData E W := ⟨3,![13,19,24,23,14],![5,26,39,18,28]⟩
def data384 : PartitionData E W := ⟨6,![cycle384_0,cycle384_1,cycle384_2,cycle384_3,cycle384_4,cycle384_5]⟩
lemma valid_data384 : data384.Valid src384 dst384 Finset.univ := by decide +kernel

def src385 : E → W := ![2,4,8,6,3,5,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst385 : E → W := ![4,8,6,3,5,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle385_0 : CycleData E W := ⟨3,![0,11,8,4,5],![2,4,14,3,5]⟩
def cycle385_1 : CycleData E W := ⟨2,![1,25,24,15],![4,8,39,28]⟩
def cycle385_2 : CycleData E W := ⟨1,![2,21,16],![6,8,38]⟩
def cycle385_3 : CycleData E W := ⟨2,![3,20,19,7],![3,6,39,16]⟩
def cycle385_4 : CycleData E W := ⟨3,![6,18,12,9,10],![2,16,26,14,18]⟩
def cycle385_5 : CycleData E W := ⟨3,![13,17,22,23,14],![5,26,38,18,28]⟩
def data385 : PartitionData E W := ⟨6,![cycle385_0,cycle385_1,cycle385_2,cycle385_3,cycle385_4,cycle385_5]⟩
lemma valid_data385 : data385.Valid src385 dst385 Finset.univ := by decide +kernel

def src386 : E → W := ![2,4,8,6,3,5,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst386 : E → W := ![4,8,6,3,5,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle386_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle386_1 : CycleData E W := ⟨3,![1,21,17,18,15],![4,8,38,16,26]⟩
def cycle386_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle386_3 : CycleData E W := ⟨3,![3,16,22,12,8],![3,6,38,28,14]⟩
def cycle386_4 : CycleData E W := ⟨2,![5,4,9,10],![2,5,3,18]⟩
def cycle386_5 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def data386 : PartitionData E W := ⟨6,![cycle386_0,cycle386_1,cycle386_2,cycle386_3,cycle386_4,cycle386_5]⟩
lemma valid_data386 : data386.Valid src386 dst386 Finset.univ := by decide +kernel

def src387 : E → W := ![2,4,8,6,3,5,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst387 : E → W := ![4,8,6,3,5,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle387_0 : CycleData E W := ⟨2,![0,11,7,6],![2,4,14,16]⟩
def cycle387_1 : CycleData E W := ⟨2,![1,21,17,15],![4,8,38,26]⟩
def cycle387_2 : CycleData E W := ⟨1,![2,25,20],![6,8,39]⟩
def cycle387_3 : CycleData E W := ⟨2,![3,16,22,9],![3,6,38,18]⟩
def cycle387_4 : CycleData E W := ⟨2,![4,13,12,8],![3,5,28,14]⟩
def cycle387_5 : CycleData E W := ⟨5,![5,14,18,19,24,23,10],![2,5,26,16,39,28,18]⟩
def data387 : PartitionData E W := ⟨6,![cycle387_0,cycle387_1,cycle387_2,cycle387_3,cycle387_4,cycle387_5]⟩
lemma valid_data387 : data387.Valid src387 dst387 Finset.univ := by decide +kernel

def src388 : E → W := ![2,5,3,4,6,8,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst388 : E → W := ![5,3,4,6,8,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle388_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle388_1 : CycleData E W := ⟨3,![2,11,12,23,9],![3,4,14,28,18]⟩
def cycle388_2 : CycleData E W := ⟨2,![3,20,19,15],![4,6,39,26]⟩
def cycle388_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle388_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle388_5 : CycleData E W := ⟨3,![13,22,17,18,14],![5,28,38,16,26]⟩
def data388 : PartitionData E W := ⟨6,![cycle388_0,cycle388_1,cycle388_2,cycle388_3,cycle388_4,cycle388_5]⟩
lemma valid_data388 : data388.Valid src388 dst388 Finset.univ := by decide +kernel

def src389 : E → W := ![2,5,3,4,6,8,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst389 : E → W := ![5,3,4,6,8,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle389_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle389_1 : CycleData E W := ⟨3,![2,11,12,23,9],![3,4,14,28,18]⟩
def cycle389_2 : CycleData E W := ⟨2,![3,16,17,15],![4,6,38,26]⟩
def cycle389_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle389_4 : CycleData E W := ⟨2,![5,21,22,10],![2,8,38,18]⟩
def cycle389_5 : CycleData E W := ⟨3,![13,24,19,18,14],![5,28,39,16,26]⟩
def data389 : PartitionData E W := ⟨6,![cycle389_0,cycle389_1,cycle389_2,cycle389_3,cycle389_4,cycle389_5]⟩
lemma valid_data389 : data389.Valid src389 dst389 Finset.univ := by decide +kernel

def src390 : E → W := ![2,5,3,4,6,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst390 : E → W := ![5,3,4,6,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle390_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle390_1 : CycleData E W := ⟨3,![2,11,12,18,9],![3,4,14,26,16]⟩
def cycle390_2 : CycleData E W := ⟨2,![3,16,22,15],![4,6,38,28]⟩
def cycle390_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle390_4 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle390_5 : CycleData E W := ⟨3,![13,19,24,23,14],![5,26,39,18,28]⟩
def data390 : PartitionData E W := ⟨6,![cycle390_0,cycle390_1,cycle390_2,cycle390_3,cycle390_4,cycle390_5]⟩
lemma valid_data390 : data390.Valid src390 dst390 Finset.univ := by decide +kernel

def src391 : E → W := ![2,5,3,4,6,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst391 : E → W := ![5,3,4,6,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle391_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle391_1 : CycleData E W := ⟨3,![2,11,12,18,9],![3,4,14,26,16]⟩
def cycle391_2 : CycleData E W := ⟨2,![3,20,24,15],![4,6,39,28]⟩
def cycle391_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle391_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle391_5 : CycleData E W := ⟨3,![13,17,22,23,14],![5,26,38,18,28]⟩
def data391 : PartitionData E W := ⟨6,![cycle391_0,cycle391_1,cycle391_2,cycle391_3,cycle391_4,cycle391_5]⟩
lemma valid_data391 : data391.Valid src391 dst391 Finset.univ := by decide +kernel

def src392 : E → W := ![2,5,3,4,8,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst392 : E → W := ![5,3,4,8,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle392_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle392_1 : CycleData E W := ⟨3,![2,11,12,23,9],![3,4,14,28,18]⟩
def cycle392_2 : CycleData E W := ⟨2,![3,25,19,15],![4,8,39,26]⟩
def cycle392_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle392_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle392_5 : CycleData E W := ⟨3,![13,22,17,18,14],![5,28,38,16,26]⟩
def data392 : PartitionData E W := ⟨6,![cycle392_0,cycle392_1,cycle392_2,cycle392_3,cycle392_4,cycle392_5]⟩
lemma valid_data392 : data392.Valid src392 dst392 Finset.univ := by decide +kernel

def src393 : E → W := ![2,5,3,4,8,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst393 : E → W := ![5,3,4,8,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle393_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle393_1 : CycleData E W := ⟨3,![2,11,12,23,9],![3,4,14,28,18]⟩
def cycle393_2 : CycleData E W := ⟨2,![3,21,17,15],![4,8,38,26]⟩
def cycle393_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle393_4 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle393_5 : CycleData E W := ⟨3,![13,24,19,18,14],![5,28,39,16,26]⟩
def data393 : PartitionData E W := ⟨6,![cycle393_0,cycle393_1,cycle393_2,cycle393_3,cycle393_4,cycle393_5]⟩
lemma valid_data393 : data393.Valid src393 dst393 Finset.univ := by decide +kernel

def src394 : E → W := ![2,5,3,4,8,6,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst394 : E → W := ![5,3,4,8,6,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle394_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle394_1 : CycleData E W := ⟨3,![2,11,12,18,9],![3,4,14,26,16]⟩
def cycle394_2 : CycleData E W := ⟨2,![3,21,22,15],![4,8,38,28]⟩
def cycle394_3 : CycleData E W := ⟨1,![4,25,20],![6,8,39]⟩
def cycle394_4 : CycleData E W := ⟨2,![5,16,17,10],![2,6,38,16]⟩
def cycle394_5 : CycleData E W := ⟨3,![13,19,24,23,14],![5,26,39,18,28]⟩
def data394 : PartitionData E W := ⟨6,![cycle394_0,cycle394_1,cycle394_2,cycle394_3,cycle394_4,cycle394_5]⟩
lemma valid_data394 : data394.Valid src394 dst394 Finset.univ := by decide +kernel

def src395 : E → W := ![2,5,3,4,8,6,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst395 : E → W := ![5,3,4,8,6,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle395_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle395_1 : CycleData E W := ⟨3,![2,11,12,18,9],![3,4,14,26,16]⟩
def cycle395_2 : CycleData E W := ⟨2,![3,25,24,15],![4,8,39,28]⟩
def cycle395_3 : CycleData E W := ⟨1,![4,21,16],![6,8,38]⟩
def cycle395_4 : CycleData E W := ⟨2,![5,20,19,10],![2,6,39,16]⟩
def cycle395_5 : CycleData E W := ⟨3,![13,17,22,23,14],![5,26,38,18,28]⟩
def data395 : PartitionData E W := ⟨6,![cycle395_0,cycle395_1,cycle395_2,cycle395_3,cycle395_4,cycle395_5]⟩
lemma valid_data395 : data395.Valid src395 dst395 Finset.univ := by decide +kernel

def src396 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,5,26,28,14,6,38,16,26,39,8,38,28,18,39]
def dst396 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,5,26,28,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle396_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle396_1 : CycleData E W := ⟨5,![2,3,11,12,19,24,8],![3,6,4,5,26,39,18]⟩
def cycle396_2 : CycleData E W := ⟨2,![5,4,15,6],![2,8,4,14]⟩
def cycle396_3 : CycleData E W := ⟨1,![7,23,14],![14,18,28]⟩
def cycle396_4 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,26]⟩
def cycle396_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data396 : PartitionData E W := ⟨6,![cycle396_0,cycle396_1,cycle396_2,cycle396_3,cycle396_4,cycle396_5]⟩
lemma valid_data396 : data396.Valid src396 dst396 Finset.univ := by decide +kernel

def src397 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,5,26,28,14,6,38,26,16,39,8,38,18,28,39]
def dst397 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,5,26,28,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle397_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle397_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle397_2 : CycleData E W := ⟨4,![3,20,19,18,12,11],![4,6,39,16,26,5]⟩
def cycle397_3 : CycleData E W := ⟨2,![5,4,15,6],![2,8,4,14]⟩
def cycle397_4 : CycleData E W := ⟨1,![7,23,14],![14,18,28]⟩
def cycle397_5 : CycleData E W := ⟨3,![21,17,13,24,25],![8,38,26,28,39]⟩
def data397 : PartitionData E W := ⟨6,![cycle397_0,cycle397_1,cycle397_2,cycle397_3,cycle397_4,cycle397_5]⟩
lemma valid_data397 : data397.Valid src397 dst397 Finset.univ := by decide +kernel

def src398 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,5,28,26,14,6,38,16,26,39,8,38,28,18,39]
def dst398 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,5,28,26,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle398_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle398_1 : CycleData E W := ⟨4,![2,3,11,12,23,8],![3,6,4,5,28,18]⟩
def cycle398_2 : CycleData E W := ⟨2,![5,4,15,6],![2,8,4,14]⟩
def cycle398_3 : CycleData E W := ⟨2,![7,24,19,14],![14,18,39,26]⟩
def cycle398_4 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,26]⟩
def cycle398_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data398 : PartitionData E W := ⟨6,![cycle398_0,cycle398_1,cycle398_2,cycle398_3,cycle398_4,cycle398_5]⟩
lemma valid_data398 : data398.Valid src398 dst398 Finset.univ := by decide +kernel

def src399 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,5,28,26,14,6,38,26,16,39,8,38,18,28,39]
def dst399 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,5,28,26,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle399_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle399_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle399_2 : CycleData E W := ⟨3,![3,20,24,12,11],![4,6,39,28,5]⟩
def cycle399_3 : CycleData E W := ⟨2,![5,4,15,6],![2,8,4,14]⟩
def cycle399_4 : CycleData E W := ⟨2,![7,23,13,14],![14,18,28,26]⟩
def cycle399_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data399 : PartitionData E W := ⟨6,![cycle399_0,cycle399_1,cycle399_2,cycle399_3,cycle399_4,cycle399_5]⟩
lemma valid_data399 : data399.Valid src399 dst399 Finset.univ := by decide +kernel

def lookupB7 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data350 else (if j < 2 then data351 else data352)) else (if j < 4 then data353 else (if j < 5 then data354 else data355))) else (if j < 9 then (if j < 7 then data356 else (if j < 8 then data357 else data358)) else (if j < 10 then data359 else (if j < 11 then data360 else data361)))) else (if j < 18 then (if j < 15 then (if j < 13 then data362 else (if j < 14 then data363 else data364)) else (if j < 16 then data365 else (if j < 17 then data366 else data367))) else (if j < 21 then (if j < 19 then data368 else (if j < 20 then data369 else data370)) else (if j < 23 then (if j < 22 then data371 else data372) else (if j < 24 then data373 else data374))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data375 else (if j < 27 then data376 else data377)) else (if j < 29 then data378 else (if j < 30 then data379 else data380))) else (if j < 34 then (if j < 32 then data381 else (if j < 33 then data382 else data383)) else (if j < 35 then data384 else (if j < 36 then data385 else data386)))) else (if j < 43 then (if j < 40 then (if j < 38 then data387 else (if j < 39 then data388 else data389)) else (if j < 41 then data390 else (if j < 42 then data391 else data392))) else (if j < 46 then (if j < 44 then data393 else (if j < 45 then data394 else data395)) else (if j < 48 then (if j < 47 then data396 else data397) else (if j < 49 then data398 else data399))))))

def srcTableB7 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src350 else (if j < 2 then src351 else src352)) else (if j < 4 then src353 else (if j < 5 then src354 else src355))) else (if j < 9 then (if j < 7 then src356 else (if j < 8 then src357 else src358)) else (if j < 10 then src359 else (if j < 11 then src360 else src361)))) else (if j < 18 then (if j < 15 then (if j < 13 then src362 else (if j < 14 then src363 else src364)) else (if j < 16 then src365 else (if j < 17 then src366 else src367))) else (if j < 21 then (if j < 19 then src368 else (if j < 20 then src369 else src370)) else (if j < 23 then (if j < 22 then src371 else src372) else (if j < 24 then src373 else src374))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src375 else (if j < 27 then src376 else src377)) else (if j < 29 then src378 else (if j < 30 then src379 else src380))) else (if j < 34 then (if j < 32 then src381 else (if j < 33 then src382 else src383)) else (if j < 35 then src384 else (if j < 36 then src385 else src386)))) else (if j < 43 then (if j < 40 then (if j < 38 then src387 else (if j < 39 then src388 else src389)) else (if j < 41 then src390 else (if j < 42 then src391 else src392))) else (if j < 46 then (if j < 44 then src393 else (if j < 45 then src394 else src395)) else (if j < 48 then (if j < 47 then src396 else src397) else (if j < 49 then src398 else src399))))))

def dstTableB7 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst350 else (if j < 2 then dst351 else dst352)) else (if j < 4 then dst353 else (if j < 5 then dst354 else dst355))) else (if j < 9 then (if j < 7 then dst356 else (if j < 8 then dst357 else dst358)) else (if j < 10 then dst359 else (if j < 11 then dst360 else dst361)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst362 else (if j < 14 then dst363 else dst364)) else (if j < 16 then dst365 else (if j < 17 then dst366 else dst367))) else (if j < 21 then (if j < 19 then dst368 else (if j < 20 then dst369 else dst370)) else (if j < 23 then (if j < 22 then dst371 else dst372) else (if j < 24 then dst373 else dst374))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst375 else (if j < 27 then dst376 else dst377)) else (if j < 29 then dst378 else (if j < 30 then dst379 else dst380))) else (if j < 34 then (if j < 32 then dst381 else (if j < 33 then dst382 else dst383)) else (if j < 35 then dst384 else (if j < 36 then dst385 else dst386)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst387 else (if j < 39 then dst388 else dst389)) else (if j < 41 then dst390 else (if j < 42 then dst391 else dst392))) else (if j < 46 then (if j < 44 then dst393 else (if j < 45 then dst394 else dst395)) else (if j < 48 then (if j < 47 then dst396 else dst397) else (if j < 49 then dst398 else dst399))))))

def caseB7 (i : Fin 50) : Cases := ⟨350 + i.val,by have := i.isLt; omega⟩
lemma tableB7_valid (i : Fin 50) :
    (lookupB7 i.val).Valid (srcTableB7 i.val) (dstTableB7 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB7_row : ∀ (i : Fin 50) (e : E),
    srcTableB7 i.val e = caseSource (caseB7 i) e := by decide +kernel

lemma dstB7_row : ∀ (i : Fin 50) (e : E),
    dstTableB7 i.val e = caseTarget (caseB7 i) e := by decide +kernel

lemma sizeB7 : ∀ i : Fin 50, (lookupB7 i.val).size ≤ 5 →
    (lookupB7 i.val).size = 2 ∧
      (⟨caseKey (caseB7 i),caseKey_lt (caseB7 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB7 (i : Fin 50) : Certificate (caseB7 i) := by
  refine ⟨lookupB7 i.val,?_,sizeB7 i⟩
  have hv := tableB7_valid i
  rw [funext (srcB7_row i),funext (dstB7_row i)] at hv
  exact hv
lemma certificateInterval7 : FiniteIntervals.Covers CertificateAt 350 400 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 350 50 (fun i _ => certificateB7 i)
#print axioms certificateInterval7
end Erdos184Work.FiveRows4

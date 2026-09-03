import Submission.SixRepresentativeCertificates0Base
namespace Erdos184Work.SixRepresentativeCertificates0
open PureSixRowModel0 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src350 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,20,44,32,58,10,46,34,22,58]
def dst350 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,20,44,32,58,8,46,34,22,58,10]
def cycle350_0 : CycleData E W := ⟨3,![0,1,15,8,9],![2,4,6,18,22]⟩
def cycle350_1 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle350_2 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle350_3 : CycleData E W := ⟨3,![4,25,26,12,5],![2,10,46,34,16]⟩
def cycle350_4 : CycleData E W := ⟨2,![6,7,16,11],![16,20,18,30]⟩
def cycle350_5 : CycleData E W := ⟨2,![10,17,22,14],![4,30,44,32]⟩
def cycle350_6 : CycleData E W := ⟨2,![27,13,23,28],![22,34,32,58]⟩
def data350 : PartitionData E W := ⟨7,![cycle350_0,cycle350_1,cycle350_2,cycle350_3,cycle350_4,cycle350_5,cycle350_6]⟩
lemma valid350 : data350.Valid src350 dst350 Finset.univ := by decide +kernel
lemma src_eq350 : src350 = src (unkey (representativeKey 350)) := by decide +kernel
lemma dst_eq350 : dst350 = dst (unkey (representativeKey 350)) := by decide +kernel
lemma certificate350 : Certificate 350 := by
  refine ⟨data350,?_,?_⟩
  · rw [← src_eq350,← dst_eq350]
    exact valid350
  · decide +kernel

def src351 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,44,20,32,58,10,34,22,58,46]
def dst351 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,44,20,32,58,8,34,22,58,46,10]
def cycle351_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle351_1 : CycleData E W := ⟨3,![1,2,24,23,14],![4,6,8,58,32]⟩
def cycle351_2 : CycleData E W := ⟨2,![3,29,18,20],![8,10,46,44]⟩
def cycle351_3 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle351_4 : CycleData E W := ⟨2,![6,22,13,12],![16,20,32,34]⟩
def cycle351_5 : CycleData E W := ⟨2,![7,21,17,16],![18,20,44,30]⟩
def cycle351_6 : CycleData E W := ⟨3,![15,8,27,28,19],![6,18,22,58,46]⟩
def data351 : PartitionData E W := ⟨7,![cycle351_0,cycle351_1,cycle351_2,cycle351_3,cycle351_4,cycle351_5,cycle351_6]⟩
lemma valid351 : data351.Valid src351 dst351 Finset.univ := by decide +kernel
lemma src_eq351 : src351 = src (unkey (representativeKey 351)) := by decide +kernel
lemma dst_eq351 : dst351 = dst (unkey (representativeKey 351)) := by decide +kernel
lemma certificate351 : Certificate 351 := by
  refine ⟨data351,?_,?_⟩
  · rw [← src_eq351,← dst_eq351]
    exact valid351
  · decide +kernel

def src352 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,44,20,32,58,10,34,58,22,46]
def dst352 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,44,20,32,58,8,34,58,22,46,10]
def cycle352_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle352_1 : CycleData E W := ⟨3,![1,2,24,23,14],![4,6,8,58,32]⟩
def cycle352_2 : CycleData E W := ⟨2,![3,29,18,20],![8,10,46,44]⟩
def cycle352_3 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,34,58,22]⟩
def cycle352_4 : CycleData E W := ⟨2,![6,22,13,12],![16,20,32,34]⟩
def cycle352_5 : CycleData E W := ⟨2,![7,21,17,16],![18,20,44,30]⟩
def cycle352_6 : CycleData E W := ⟨2,![15,8,28,19],![6,18,22,46]⟩
def data352 : PartitionData E W := ⟨7,![cycle352_0,cycle352_1,cycle352_2,cycle352_3,cycle352_4,cycle352_5,cycle352_6]⟩
lemma valid352 : data352.Valid src352 dst352 Finset.univ := by decide +kernel
lemma src_eq352 : src352 = src (unkey (representativeKey 352)) := by decide +kernel
lemma dst_eq352 : dst352 = dst (unkey (representativeKey 352)) := by decide +kernel
lemma certificate352 : Certificate 352 := by
  refine ⟨data352,?_,?_⟩
  · rw [← src_eq352,← dst_eq352]
    exact valid352
  · decide +kernel

def src353 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,44,46,30,8,20,32,44,58,10,34,58,22,46]
def dst353 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,44,46,30,6,20,32,44,58,8,34,58,22,46,10]
def cycle353_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle353_1 : CycleData E W := ⟨4,![1,19,18,17,22,14],![4,6,30,46,44,32]⟩
def cycle353_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle353_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle353_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle353_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle353_6 : CycleData E W := ⟨2,![8,27,23,16],![18,22,58,44]⟩
def data353 : PartitionData E W := ⟨7,![cycle353_0,cycle353_1,cycle353_2,cycle353_3,cycle353_4,cycle353_5,cycle353_6]⟩
lemma valid353 : data353.Valid src353 dst353 Finset.univ := by decide +kernel
lemma src_eq353 : src353 = src (unkey (representativeKey 353)) := by decide +kernel
lemma dst_eq353 : dst353 = dst (unkey (representativeKey 353)) := by decide +kernel
lemma certificate353 : Certificate 353 := by
  refine ⟨data353,?_,?_⟩
  · rw [← src_eq353,← dst_eq353]
    exact valid353
  · decide +kernel

def src354 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,44,46,30,8,20,32,44,58,10,46,34,22,58]
def dst354 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,44,46,30,6,20,32,44,58,8,46,34,22,58,10]
def cycle354_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle354_1 : CycleData E W := ⟨4,![1,19,18,17,22,14],![4,6,30,46,44,32]⟩
def cycle354_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle354_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle354_4 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,46,34,22]⟩
def cycle354_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle354_6 : CycleData E W := ⟨2,![8,28,23,16],![18,22,58,44]⟩
def data354 : PartitionData E W := ⟨7,![cycle354_0,cycle354_1,cycle354_2,cycle354_3,cycle354_4,cycle354_5,cycle354_6]⟩
lemma valid354 : data354.Valid src354 dst354 Finset.univ := by decide +kernel
lemma src_eq354 : src354 = src (unkey (representativeKey 354)) := by decide +kernel
lemma dst_eq354 : dst354 = dst (unkey (representativeKey 354)) := by decide +kernel
lemma certificate354 : Certificate 354 := by
  refine ⟨data354,?_,?_⟩
  · rw [← src_eq354,← dst_eq354]
    exact valid354
  · decide +kernel

def src355 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,30,44,8,20,32,44,58,10,34,22,58,46]
def dst355 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,30,44,6,20,32,44,58,8,34,22,58,46,10]
def cycle355_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle355_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,44,32]⟩
def cycle355_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle355_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle355_4 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle355_5 : CycleData E W := ⟨3,![25,26,8,16,29],![10,34,22,18,46]⟩
def cycle355_6 : CycleData E W := ⟨2,![17,28,23,18],![30,46,58,44]⟩
def data355 : PartitionData E W := ⟨7,![cycle355_0,cycle355_1,cycle355_2,cycle355_3,cycle355_4,cycle355_5,cycle355_6]⟩
lemma valid355 : data355.Valid src355 dst355 Finset.univ := by decide +kernel
lemma src_eq355 : src355 = src (unkey (representativeKey 355)) := by decide +kernel
lemma dst_eq355 : dst355 = dst (unkey (representativeKey 355)) := by decide +kernel
lemma certificate355 : Certificate 355 := by
  refine ⟨data355,?_,?_⟩
  · rw [← src_eq355,← dst_eq355]
    exact valid355
  · decide +kernel

def src356 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,30,44,8,20,32,44,58,10,46,34,22,58]
def dst356 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,30,44,6,20,32,44,58,8,46,34,22,58,10]
def cycle356_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle356_1 : CycleData E W := ⟨2,![1,19,22,14],![4,6,44,32]⟩
def cycle356_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle356_3 : CycleData E W := ⟨4,![3,25,17,18,23,24],![8,10,46,30,44,58]⟩
def cycle356_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle356_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle356_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data356 : PartitionData E W := ⟨7,![cycle356_0,cycle356_1,cycle356_2,cycle356_3,cycle356_4,cycle356_5,cycle356_6]⟩
lemma valid356 : data356.Valid src356 dst356 Finset.univ := by decide +kernel
lemma src_eq356 : src356 = src (unkey (representativeKey 356)) := by decide +kernel
lemma dst_eq356 : dst356 = dst (unkey (representativeKey 356)) := by decide +kernel
lemma certificate356 : Certificate 356 := by
  refine ⟨data356,?_,?_⟩
  · rw [← src_eq356,← dst_eq356]
    exact valid356
  · decide +kernel

def src357 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,30,44,8,20,58,44,32,10,34,22,58,46]
def dst357 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,30,44,6,20,58,44,32,8,34,22,58,46,10]
def cycle357_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle357_1 : CycleData E W := ⟨2,![1,19,23,14],![4,6,44,32]⟩
def cycle357_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle357_3 : CycleData E W := ⟨2,![3,25,13,24],![8,10,34,32]⟩
def cycle357_4 : CycleData E W := ⟨3,![4,29,16,8,9],![2,10,46,18,22]⟩
def cycle357_5 : CycleData E W := ⟨3,![6,21,27,26,12],![16,20,58,22,34]⟩
def cycle357_6 : CycleData E W := ⟨2,![17,28,22,18],![30,46,58,44]⟩
def data357 : PartitionData E W := ⟨7,![cycle357_0,cycle357_1,cycle357_2,cycle357_3,cycle357_4,cycle357_5,cycle357_6]⟩
lemma valid357 : data357.Valid src357 dst357 Finset.univ := by decide +kernel
lemma src_eq357 : src357 = src (unkey (representativeKey 357)) := by decide +kernel
lemma dst_eq357 : dst357 = dst (unkey (representativeKey 357)) := by decide +kernel
lemma certificate357 : Certificate 357 := by
  refine ⟨data357,?_,?_⟩
  · rw [← src_eq357,← dst_eq357]
    exact valid357
  · decide +kernel

def src358 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,44,30,8,20,32,44,58,10,34,58,22,46]
def dst358 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,44,30,6,20,32,44,58,8,34,58,22,46,10]
def cycle358_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle358_1 : CycleData E W := ⟨3,![1,19,18,22,14],![4,6,30,44,32]⟩
def cycle358_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle358_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle358_4 : CycleData E W := ⟨3,![4,29,16,8,9],![2,10,46,18,22]⟩
def cycle358_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle358_6 : CycleData E W := ⟨2,![27,23,17,28],![22,58,44,46]⟩
def data358 : PartitionData E W := ⟨7,![cycle358_0,cycle358_1,cycle358_2,cycle358_3,cycle358_4,cycle358_5,cycle358_6]⟩
lemma valid358 : data358.Valid src358 dst358 Finset.univ := by decide +kernel
lemma src_eq358 : src358 = src (unkey (representativeKey 358)) := by decide +kernel
lemma dst_eq358 : dst358 = dst (unkey (representativeKey 358)) := by decide +kernel
lemma certificate358 : Certificate 358 := by
  refine ⟨data358,?_,?_⟩
  · rw [← src_eq358,← dst_eq358]
    exact valid358
  · decide +kernel

def src359 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,44,30,8,20,32,58,44,10,34,58,22,46]
def dst359 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,44,30,6,20,32,58,44,8,34,58,22,46,10]
def cycle359_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle359_1 : CycleData E W := ⟨3,![1,15,7,21,14],![4,6,18,20,32]⟩
def cycle359_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,30]⟩
def cycle359_3 : CycleData E W := ⟨3,![3,25,12,6,20],![8,10,34,16,20]⟩
def cycle359_4 : CycleData E W := ⟨3,![4,29,16,8,9],![2,10,46,18,22]⟩
def cycle359_5 : CycleData E W := ⟨1,![13,26,22],![32,34,58]⟩
def cycle359_6 : CycleData E W := ⟨2,![27,23,17,28],![22,58,44,46]⟩
def data359 : PartitionData E W := ⟨7,![cycle359_0,cycle359_1,cycle359_2,cycle359_3,cycle359_4,cycle359_5,cycle359_6]⟩
lemma valid359 : data359.Valid src359 dst359 Finset.univ := by decide +kernel
lemma src_eq359 : src359 = src (unkey (representativeKey 359)) := by decide +kernel
lemma dst_eq359 : dst359 = dst (unkey (representativeKey 359)) := by decide +kernel
lemma certificate359 : Certificate 359 := by
  refine ⟨data359,?_,?_⟩
  · rw [← src_eq359,← dst_eq359]
    exact valid359
  · decide +kernel

def src360 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,44,30,8,20,44,32,58,10,34,22,58,46]
def dst360 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,44,30,6,20,44,32,58,8,34,22,58,46,10]
def cycle360_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,32,34,16]⟩
def cycle360_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle360_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle360_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle360_4 : CycleData E W := ⟨2,![6,21,18,11],![16,20,44,30]⟩
def cycle360_5 : CycleData E W := ⟨3,![25,26,8,16,29],![10,34,22,18,46]⟩
def cycle360_6 : CycleData E W := ⟨2,![22,17,28,23],![32,44,46,58]⟩
def data360 : PartitionData E W := ⟨7,![cycle360_0,cycle360_1,cycle360_2,cycle360_3,cycle360_4,cycle360_5,cycle360_6]⟩
lemma valid360 : data360.Valid src360 dst360 Finset.univ := by decide +kernel
lemma src_eq360 : src360 = src (unkey (representativeKey 360)) := by decide +kernel
lemma dst_eq360 : dst360 = dst (unkey (representativeKey 360)) := by decide +kernel
lemma certificate360 : Certificate 360 := by
  refine ⟨data360,?_,?_⟩
  · rw [← src_eq360,← dst_eq360]
    exact valid360
  · decide +kernel

def src361 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,46,44,30,8,44,20,32,58,10,34,58,22,46]
def dst361 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,46,44,30,6,44,20,32,58,8,34,58,22,46,10]
def cycle361_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle361_1 : CycleData E W := ⟨3,![1,15,7,22,14],![4,6,18,20,32]⟩
def cycle361_2 : CycleData E W := ⟨2,![2,20,18,19],![6,8,44,30]⟩
def cycle361_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle361_4 : CycleData E W := ⟨4,![25,12,6,21,17,29],![10,34,16,20,44,46]⟩
def cycle361_5 : CycleData E W := ⟨1,![8,28,16],![18,22,46]⟩
def cycle361_6 : CycleData E W := ⟨1,![13,26,23],![32,34,58]⟩
def data361 : PartitionData E W := ⟨7,![cycle361_0,cycle361_1,cycle361_2,cycle361_3,cycle361_4,cycle361_5,cycle361_6]⟩
lemma valid361 : data361.Valid src361 dst361 Finset.univ := by decide +kernel
lemma src_eq361 : src361 = src (unkey (representativeKey 361)) := by decide +kernel
lemma dst_eq361 : dst361 = dst (unkey (representativeKey 361)) := by decide +kernel
lemma certificate361 : Certificate 361 := by
  refine ⟨data361,?_,?_⟩
  · rw [← src_eq361,← dst_eq361]
    exact valid361
  · decide +kernel

def src362 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,44,18,30,46,8,20,32,44,58,10,34,22,58,46]
def dst362 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,44,18,30,46,6,20,32,44,58,8,34,22,58,46,10]
def cycle362_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle362_1 : CycleData E W := ⟨2,![1,15,22,14],![4,6,44,32]⟩
def cycle362_2 : CycleData E W := ⟨4,![2,20,7,17,18,19],![6,8,20,18,30,46]⟩
def cycle362_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle362_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle362_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle362_6 : CycleData E W := ⟨2,![8,27,23,16],![18,22,58,44]⟩
def data362 : PartitionData E W := ⟨7,![cycle362_0,cycle362_1,cycle362_2,cycle362_3,cycle362_4,cycle362_5,cycle362_6]⟩
lemma valid362 : data362.Valid src362 dst362 Finset.univ := by decide +kernel
lemma src_eq362 : src362 = src (unkey (representativeKey 362)) := by decide +kernel
lemma dst_eq362 : dst362 = dst (unkey (representativeKey 362)) := by decide +kernel
lemma certificate362 : Certificate 362 := by
  refine ⟨data362,?_,?_⟩
  · rw [← src_eq362,← dst_eq362]
    exact valid362
  · decide +kernel

def src363 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,44,18,30,46,8,20,32,44,58,10,34,58,22,46]
def dst363 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,44,18,30,46,6,20,32,44,58,8,34,58,22,46,10]
def cycle363_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle363_1 : CycleData E W := ⟨2,![1,15,22,14],![4,6,44,32]⟩
def cycle363_2 : CycleData E W := ⟨4,![2,20,7,17,18,19],![6,8,20,18,30,46]⟩
def cycle363_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle363_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle363_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle363_6 : CycleData E W := ⟨2,![8,27,23,16],![18,22,58,44]⟩
def data363 : PartitionData E W := ⟨7,![cycle363_0,cycle363_1,cycle363_2,cycle363_3,cycle363_4,cycle363_5,cycle363_6]⟩
lemma valid363 : data363.Valid src363 dst363 Finset.univ := by decide +kernel
lemma src_eq363 : src363 = src (unkey (representativeKey 363)) := by decide +kernel
lemma dst_eq363 : dst363 = dst (unkey (representativeKey 363)) := by decide +kernel
lemma certificate363 : Certificate 363 := by
  refine ⟨data363,?_,?_⟩
  · rw [← src_eq363,← dst_eq363]
    exact valid363
  · decide +kernel

def src364 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,44,18,30,46,8,20,32,58,44,10,34,58,22,46]
def dst364 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,44,18,30,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle364_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle364_1 : CycleData E W := ⟨5,![1,19,18,17,7,21,14],![4,6,46,30,18,20,32]⟩
def cycle364_2 : CycleData E W := ⟨1,![2,24,15],![6,8,44]⟩
def cycle364_3 : CycleData E W := ⟨3,![3,25,12,6,20],![8,10,34,16,20]⟩
def cycle364_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle364_5 : CycleData E W := ⟨2,![8,27,23,16],![18,22,58,44]⟩
def cycle364_6 : CycleData E W := ⟨1,![13,26,22],![32,34,58]⟩
def data364 : PartitionData E W := ⟨7,![cycle364_0,cycle364_1,cycle364_2,cycle364_3,cycle364_4,cycle364_5,cycle364_6]⟩
lemma valid364 : data364.Valid src364 dst364 Finset.univ := by decide +kernel
lemma src_eq364 : src364 = src (unkey (representativeKey 364)) := by decide +kernel
lemma dst_eq364 : dst364 = dst (unkey (representativeKey 364)) := by decide +kernel
lemma certificate364 : Certificate 364 := by
  refine ⟨data364,?_,?_⟩
  · rw [← src_eq364,← dst_eq364]
    exact valid364
  · decide +kernel

def src365 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,44,18,30,46,8,20,44,32,58,10,34,22,58,46]
def dst365 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,44,18,30,46,6,20,44,32,58,8,34,22,58,46,10]
def cycle365_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle365_1 : CycleData E W := ⟨2,![1,15,22,14],![4,6,44,32]⟩
def cycle365_2 : CycleData E W := ⟨2,![2,24,28,19],![6,8,58,46]⟩
def cycle365_3 : CycleData E W := ⟨3,![3,25,12,6,20],![8,10,34,16,20]⟩
def cycle365_4 : CycleData E W := ⟨4,![4,29,18,17,8,9],![2,10,46,30,18,22]⟩
def cycle365_5 : CycleData E W := ⟨1,![7,21,16],![18,20,44]⟩
def cycle365_6 : CycleData E W := ⟨2,![26,13,23,27],![22,34,32,58]⟩
def data365 : PartitionData E W := ⟨7,![cycle365_0,cycle365_1,cycle365_2,cycle365_3,cycle365_4,cycle365_5,cycle365_6]⟩
lemma valid365 : data365.Valid src365 dst365 Finset.univ := by decide +kernel
lemma src_eq365 : src365 = src (unkey (representativeKey 365)) := by decide +kernel
lemma dst_eq365 : dst365 = dst (unkey (representativeKey 365)) := by decide +kernel
lemma certificate365 : Certificate 365 := by
  refine ⟨data365,?_,?_⟩
  · rw [← src_eq365,← dst_eq365]
    exact valid365
  · decide +kernel

def src366 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,32,30,16,34,6,18,30,44,46,8,44,20,32,58,10,34,22,58,46]
def dst366 : E → W := ![4,6,8,10,2,16,20,18,22,2,32,30,16,34,4,18,30,44,46,6,44,20,32,58,8,34,22,58,46,10]
def cycle366_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle366_1 : CycleData E W := ⟨3,![1,15,16,11,10],![4,6,18,30,32]⟩
def cycle366_2 : CycleData E W := ⟨2,![2,20,18,19],![6,8,44,46]⟩
def cycle366_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle366_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle366_5 : CycleData E W := ⟨2,![6,21,17,12],![16,20,44,30]⟩
def cycle366_6 : CycleData E W := ⟨3,![7,22,23,27,8],![18,20,32,58,22]⟩
def data366 : PartitionData E W := ⟨7,![cycle366_0,cycle366_1,cycle366_2,cycle366_3,cycle366_4,cycle366_5,cycle366_6]⟩
lemma valid366 : data366.Valid src366 dst366 Finset.univ := by decide +kernel
lemma src_eq366 : src366 = src (unkey (representativeKey 366)) := by decide +kernel
lemma dst_eq366 : dst366 = dst (unkey (representativeKey 366)) := by decide +kernel
lemma certificate366 : Certificate 366 := by
  refine ⟨data366,?_,?_⟩
  · rw [← src_eq366,← dst_eq366]
    exact valid366
  · decide +kernel

def src367 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,32,30,16,34,6,18,46,44,30,8,32,58,20,44,10,34,22,58,46]
def dst367 : E → W := ![4,6,8,10,2,16,20,18,22,2,32,30,16,34,4,18,46,44,30,6,32,58,20,44,8,34,22,58,46,10]
def cycle367_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle367_1 : CycleData E W := ⟨2,![1,19,11,10],![4,6,30,32]⟩
def cycle367_2 : CycleData E W := ⟨4,![2,20,21,22,7,15],![6,8,32,58,20,18]⟩
def cycle367_3 : CycleData E W := ⟨2,![3,29,17,24],![8,10,46,44]⟩
def cycle367_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle367_5 : CycleData E W := ⟨2,![6,23,18,12],![16,20,44,30]⟩
def cycle367_6 : CycleData E W := ⟨2,![8,27,28,16],![18,22,58,46]⟩
def data367 : PartitionData E W := ⟨7,![cycle367_0,cycle367_1,cycle367_2,cycle367_3,cycle367_4,cycle367_5,cycle367_6]⟩
lemma valid367 : data367.Valid src367 dst367 Finset.univ := by decide +kernel
lemma src_eq367 : src367 = src (unkey (representativeKey 367)) := by decide +kernel
lemma dst_eq367 : dst367 = dst (unkey (representativeKey 367)) := by decide +kernel
lemma certificate367 : Certificate 367 := by
  refine ⟨data367,?_,?_⟩
  · rw [← src_eq367,← dst_eq367]
    exact valid367
  · decide +kernel

def src368 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,18,44,30,46,8,20,32,44,58,10,34,22,58,46]
def dst368 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,18,44,30,46,6,20,32,44,58,8,34,22,58,46,10]
def cycle368_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle368_1 : CycleData E W := ⟨4,![1,15,16,22,13,14],![4,6,18,44,32,34]⟩
def cycle368_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle368_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,18]⟩
def cycle368_4 : CycleData E W := ⟨2,![6,21,12,11],![16,20,32,30]⟩
def cycle368_5 : CycleData E W := ⟨2,![20,7,27,24],![8,20,22,58]⟩
def cycle368_6 : CycleData E W := ⟨2,![17,23,28,18],![30,44,58,46]⟩
def data368 : PartitionData E W := ⟨7,![cycle368_0,cycle368_1,cycle368_2,cycle368_3,cycle368_4,cycle368_5,cycle368_6]⟩
lemma valid368 : data368.Valid src368 dst368 Finset.univ := by decide +kernel
lemma src_eq368 : src368 = src (unkey (representativeKey 368)) := by decide +kernel
lemma dst_eq368 : dst368 = dst (unkey (representativeKey 368)) := by decide +kernel
lemma certificate368 : Certificate 368 := by
  refine ⟨data368,?_,?_⟩
  · rw [← src_eq368,← dst_eq368]
    exact valid368
  · decide +kernel

def src369 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,18,44,30,46,8,32,58,20,44,10,34,22,58,46]
def dst369 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,18,44,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle369_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle369_1 : CycleData E W := ⟨4,![1,19,18,12,13,14],![4,6,46,30,32,34]⟩
def cycle369_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle369_3 : CycleData E W := ⟨3,![3,29,28,21,20],![8,10,46,58,32]⟩
def cycle369_4 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,18]⟩
def cycle369_5 : CycleData E W := ⟨2,![6,23,17,11],![16,20,44,30]⟩
def cycle369_6 : CycleData E W := ⟨1,![7,27,22],![20,22,58]⟩
def data369 : PartitionData E W := ⟨7,![cycle369_0,cycle369_1,cycle369_2,cycle369_3,cycle369_4,cycle369_5,cycle369_6]⟩
lemma valid369 : data369.Valid src369 dst369 Finset.univ := by decide +kernel
lemma src_eq369 : src369 = src (unkey (representativeKey 369)) := by decide +kernel
lemma dst_eq369 : dst369 = dst (unkey (representativeKey 369)) := by decide +kernel
lemma certificate369 : Certificate 369 := by
  refine ⟨data369,?_,?_⟩
  · rw [← src_eq369,← dst_eq369]
    exact valid369
  · decide +kernel

def src370 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,30,44,18,46,8,20,32,44,58,10,46,34,22,58]
def dst370 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,30,44,18,46,6,20,32,44,58,8,46,34,22,58,10]
def cycle370_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle370_1 : CycleData E W := ⟨2,![1,19,26,14],![4,6,46,34]⟩
def cycle370_2 : CycleData E W := ⟨3,![2,20,6,11,15],![6,8,20,16,30]⟩
def cycle370_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle370_4 : CycleData E W := ⟨2,![4,25,18,9],![2,10,46,18]⟩
def cycle370_5 : CycleData E W := ⟨2,![7,27,13,21],![20,22,34,32]⟩
def cycle370_6 : CycleData E W := ⟨2,![8,28,23,17],![18,22,58,44]⟩
def cycle370_7 : CycleData E W := ⟨1,![12,22,16],![30,32,44]⟩
def data370 : PartitionData E W := ⟨8,![cycle370_0,cycle370_1,cycle370_2,cycle370_3,cycle370_4,cycle370_5,cycle370_6,cycle370_7]⟩
lemma valid370 : data370.Valid src370 dst370 Finset.univ := by decide +kernel
lemma src_eq370 : src370 = src (unkey (representativeKey 370)) := by decide +kernel
lemma dst_eq370 : dst370 = dst (unkey (representativeKey 370)) := by decide +kernel
lemma certificate370 : Certificate 370 := by
  refine ⟨data370,?_,?_⟩
  · rw [← src_eq370,← dst_eq370]
    exact valid370
  · decide +kernel

def src371 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,30,44,18,46,8,20,32,58,44,10,46,34,22,58]
def dst371 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,30,44,18,46,6,20,32,58,44,8,46,34,22,58,10]
def cycle371_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle371_1 : CycleData E W := ⟨3,![1,15,12,13,14],![4,6,30,32,34]⟩
def cycle371_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle371_3 : CycleData E W := ⟨3,![4,29,23,17,9],![2,10,58,44,18]⟩
def cycle371_4 : CycleData E W := ⟨3,![20,6,11,16,24],![8,20,16,30,44]⟩
def cycle371_5 : CycleData E W := ⟨2,![7,28,22,21],![20,22,58,32]⟩
def cycle371_6 : CycleData E W := ⟨2,![8,27,26,18],![18,22,34,46]⟩
def data371 : PartitionData E W := ⟨7,![cycle371_0,cycle371_1,cycle371_2,cycle371_3,cycle371_4,cycle371_5,cycle371_6]⟩
lemma valid371 : data371.Valid src371 dst371 Finset.univ := by decide +kernel
lemma src_eq371 : src371 = src (unkey (representativeKey 371)) := by decide +kernel
lemma dst_eq371 : dst371 = dst (unkey (representativeKey 371)) := by decide +kernel
lemma certificate371 : Certificate 371 := by
  refine ⟨data371,?_,?_⟩
  · rw [← src_eq371,← dst_eq371]
    exact valid371
  · decide +kernel

def src372 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,30,44,18,46,8,20,44,58,32,10,46,34,22,58]
def dst372 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,30,44,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle372_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle372_1 : CycleData E W := ⟨3,![1,15,12,13,14],![4,6,30,32,34]⟩
def cycle372_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle372_3 : CycleData E W := ⟨3,![4,29,22,17,9],![2,10,58,44,18]⟩
def cycle372_4 : CycleData E W := ⟨2,![6,21,16,11],![16,20,44,30]⟩
def cycle372_5 : CycleData E W := ⟨3,![20,7,28,23,24],![8,20,22,58,32]⟩
def cycle372_6 : CycleData E W := ⟨2,![8,27,26,18],![18,22,34,46]⟩
def data372 : PartitionData E W := ⟨7,![cycle372_0,cycle372_1,cycle372_2,cycle372_3,cycle372_4,cycle372_5,cycle372_6]⟩
lemma valid372 : data372.Valid src372 dst372 Finset.univ := by decide +kernel
lemma src_eq372 : src372 = src (unkey (representativeKey 372)) := by decide +kernel
lemma dst_eq372 : dst372 = dst (unkey (representativeKey 372)) := by decide +kernel
lemma certificate372 : Certificate 372 := by
  refine ⟨data372,?_,?_⟩
  · rw [← src_eq372,← dst_eq372]
    exact valid372
  · decide +kernel

def src373 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,44,18,30,46,8,20,32,44,58,10,34,22,58,46]
def dst373 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,44,18,30,46,6,20,32,44,58,8,34,22,58,46,10]
def cycle373_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle373_1 : CycleData E W := ⟨3,![1,15,22,13,14],![4,6,44,32,34]⟩
def cycle373_2 : CycleData E W := ⟨2,![2,24,28,19],![6,8,58,46]⟩
def cycle373_3 : CycleData E W := ⟨3,![3,25,26,7,20],![8,10,34,22,20]⟩
def cycle373_4 : CycleData E W := ⟨3,![4,29,18,17,9],![2,10,46,30,18]⟩
def cycle373_5 : CycleData E W := ⟨2,![6,21,12,11],![16,20,32,30]⟩
def cycle373_6 : CycleData E W := ⟨2,![8,27,23,16],![18,22,58,44]⟩
def data373 : PartitionData E W := ⟨7,![cycle373_0,cycle373_1,cycle373_2,cycle373_3,cycle373_4,cycle373_5,cycle373_6]⟩
lemma valid373 : data373.Valid src373 dst373 Finset.univ := by decide +kernel
lemma src_eq373 : src373 = src (unkey (representativeKey 373)) := by decide +kernel
lemma dst_eq373 : dst373 = dst (unkey (representativeKey 373)) := by decide +kernel
lemma certificate373 : Certificate 373 := by
  refine ⟨data373,?_,?_⟩
  · rw [← src_eq373,← dst_eq373]
    exact valid373
  · decide +kernel

def src374 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,16,30,32,34,6,44,18,30,46,8,20,44,58,32,10,34,22,58,46]
def dst374 : E → W := ![4,6,8,10,2,16,20,22,18,2,16,30,32,34,4,44,18,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle374_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle374_1 : CycleData E W := ⟨3,![1,2,3,25,14],![4,6,8,10,34]⟩
def cycle374_2 : CycleData E W := ⟨3,![4,29,18,17,9],![2,10,46,30,18]⟩
def cycle374_3 : CycleData E W := ⟨3,![20,6,11,12,24],![8,20,16,30,32]⟩
def cycle374_4 : CycleData E W := ⟨2,![8,7,21,16],![18,22,20,44]⟩
def cycle374_5 : CycleData E W := ⟨2,![26,13,23,27],![22,34,32,58]⟩
def cycle374_6 : CycleData E W := ⟨2,![15,22,28,19],![6,44,58,46]⟩
def data374 : PartitionData E W := ⟨7,![cycle374_0,cycle374_1,cycle374_2,cycle374_3,cycle374_4,cycle374_5,cycle374_6]⟩
lemma valid374 : data374.Valid src374 dst374 Finset.univ := by decide +kernel
lemma src_eq374 : src374 = src (unkey (representativeKey 374)) := by decide +kernel
lemma dst_eq374 : dst374 = dst (unkey (representativeKey 374)) := by decide +kernel
lemma certificate374 : Certificate 374 := by
  refine ⟨data374,?_,?_⟩
  · rw [← src_eq374,← dst_eq374]
    exact valid374
  · decide +kernel

def src375 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,16,34,32,6,18,30,44,46,8,20,32,58,44,10,46,34,22,58]
def dst375 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,16,34,32,4,18,30,44,46,6,20,32,58,44,8,46,34,22,58,10]
def cycle375_0 : CycleData E W := ⟨13,![0,1,2,20,7,8,16,11,12,13,22,23,18,25,4],![2,4,6,8,20,22,18,30,16,34,32,58,44,46,10]⟩
def cycle375_1 : CycleData E W := ⟨13,![5,6,21,14,10,17,24,3,29,28,27,26,19,15,9],![2,16,20,32,4,30,44,8,10,58,22,34,46,6,18]⟩
def data375 : PartitionData E W := ⟨2,![cycle375_0,cycle375_1]⟩
lemma valid375 : data375.Valid src375 dst375 Finset.univ := by decide +kernel
lemma src_eq375 : src375 = src (unkey (representativeKey 375)) := by decide +kernel
lemma dst_eq375 : dst375 = dst (unkey (representativeKey 375)) := by decide +kernel
lemma certificate375 : Certificate 375 := by
  refine ⟨data375,?_,?_⟩
  · rw [← src_eq375,← dst_eq375]
    exact valid375
  · decide +kernel

def src376 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,16,34,32,6,18,30,44,46,8,20,44,32,58,10,22,58,46,34]
def dst376 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,16,34,32,4,18,30,44,46,6,20,44,32,58,8,22,58,46,34,10]
def cycle376_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,32,34,16]⟩
def cycle376_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle376_2 : CycleData E W := ⟨3,![2,3,29,28,19],![6,8,10,34,46]⟩
def cycle376_3 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,18]⟩
def cycle376_4 : CycleData E W := ⟨2,![6,21,17,11],![16,20,44,30]⟩
def cycle376_5 : CycleData E W := ⟨2,![20,7,26,24],![8,20,22,58]⟩
def cycle376_6 : CycleData E W := ⟨2,![22,18,27,23],![32,44,46,58]⟩
def data376 : PartitionData E W := ⟨7,![cycle376_0,cycle376_1,cycle376_2,cycle376_3,cycle376_4,cycle376_5,cycle376_6]⟩
lemma valid376 : data376.Valid src376 dst376 Finset.univ := by decide +kernel
lemma src_eq376 : src376 = src (unkey (representativeKey 376)) := by decide +kernel
lemma dst_eq376 : dst376 = dst (unkey (representativeKey 376)) := by decide +kernel
lemma certificate376 : Certificate 376 := by
  refine ⟨data376,?_,?_⟩
  · rw [← src_eq376,← dst_eq376]
    exact valid376
  · decide +kernel

def src377 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,16,34,32,6,18,44,30,46,8,20,32,44,58,10,22,46,58,34]
def dst377 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,16,34,32,4,18,44,30,46,6,20,32,44,58,8,22,46,58,34,10]
def cycle377_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle377_1 : CycleData E W := ⟨3,![1,15,16,22,14],![4,6,18,44,32]⟩
def cycle377_2 : CycleData E W := ⟨3,![2,20,7,26,19],![6,8,20,22,46]⟩
def cycle377_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,34,58]⟩
def cycle377_4 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,18]⟩
def cycle377_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle377_6 : CycleData E W := ⟨2,![17,23,27,18],![30,44,58,46]⟩
def data377 : PartitionData E W := ⟨7,![cycle377_0,cycle377_1,cycle377_2,cycle377_3,cycle377_4,cycle377_5,cycle377_6]⟩
lemma valid377 : data377.Valid src377 dst377 Finset.univ := by decide +kernel
lemma src_eq377 : src377 = src (unkey (representativeKey 377)) := by decide +kernel
lemma dst_eq377 : dst377 = dst (unkey (representativeKey 377)) := by decide +kernel
lemma certificate377 : Certificate 377 := by
  refine ⟨data377,?_,?_⟩
  · rw [← src_eq377,← dst_eq377]
    exact valid377
  · decide +kernel

def src378 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,16,34,32,6,18,44,30,46,8,20,32,44,58,10,34,22,58,46]
def dst378 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,16,34,32,4,18,44,30,46,6,20,32,44,58,8,34,22,58,46,10]
def cycle378_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle378_1 : CycleData E W := ⟨3,![1,15,16,22,14],![4,6,18,44,32]⟩
def cycle378_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle378_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,18]⟩
def cycle378_4 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle378_5 : CycleData E W := ⟨2,![20,7,27,24],![8,20,22,58]⟩
def cycle378_6 : CycleData E W := ⟨2,![17,23,28,18],![30,44,58,46]⟩
def data378 : PartitionData E W := ⟨7,![cycle378_0,cycle378_1,cycle378_2,cycle378_3,cycle378_4,cycle378_5,cycle378_6]⟩
lemma valid378 : data378.Valid src378 dst378 Finset.univ := by decide +kernel
lemma src_eq378 : src378 = src (unkey (representativeKey 378)) := by decide +kernel
lemma dst_eq378 : dst378 = dst (unkey (representativeKey 378)) := by decide +kernel
lemma certificate378 : Certificate 378 := by
  refine ⟨data378,?_,?_⟩
  · rw [← src_eq378,← dst_eq378]
    exact valid378
  · decide +kernel

def src379 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,16,34,32,6,44,18,30,46,8,20,32,44,58,10,22,46,58,34]
def dst379 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,16,34,32,4,44,18,30,46,6,20,32,44,58,8,22,46,58,34,10]
def cycle379_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle379_1 : CycleData E W := ⟨2,![1,15,22,14],![4,6,44,32]⟩
def cycle379_2 : CycleData E W := ⟨3,![2,20,7,26,19],![6,8,20,22,46]⟩
def cycle379_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,34,58]⟩
def cycle379_4 : CycleData E W := ⟨2,![4,25,8,9],![2,10,22,18]⟩
def cycle379_5 : CycleData E W := ⟨2,![6,21,13,12],![16,20,32,34]⟩
def cycle379_6 : CycleData E W := ⟨3,![16,23,27,18,17],![18,44,58,46,30]⟩
def data379 : PartitionData E W := ⟨7,![cycle379_0,cycle379_1,cycle379_2,cycle379_3,cycle379_4,cycle379_5,cycle379_6]⟩
lemma valid379 : data379.Valid src379 dst379 Finset.univ := by decide +kernel
lemma src_eq379 : src379 = src (unkey (representativeKey 379)) := by decide +kernel
lemma dst_eq379 : dst379 = dst (unkey (representativeKey 379)) := by decide +kernel
lemma certificate379 : Certificate 379 := by
  refine ⟨data379,?_,?_⟩
  · rw [← src_eq379,← dst_eq379]
    exact valid379
  · decide +kernel

def src380 : E → W := ![2,4,6,8,10,2,16,20,22,18,4,30,34,16,32,6,44,18,30,46,8,20,44,32,58,10,22,46,58,34]
def dst380 : E → W := ![4,6,8,10,2,16,20,22,18,2,30,34,16,32,4,44,18,30,46,6,20,44,32,58,8,22,46,58,34,10]
def cycle380_0 : CycleData E W := ⟨3,![0,1,15,16,9],![2,4,6,44,18]⟩
def cycle380_1 : CycleData E W := ⟨2,![2,24,27,19],![6,8,58,46]⟩
def cycle380_2 : CycleData E W := ⟨2,![3,25,7,20],![8,10,22,20]⟩
def cycle380_3 : CycleData E W := ⟨2,![4,29,12,5],![2,10,34,16]⟩
def cycle380_4 : CycleData E W := ⟨2,![6,21,22,13],![16,20,44,32]⟩
def cycle380_5 : CycleData E W := ⟨2,![8,26,18,17],![18,22,46,30]⟩
def cycle380_6 : CycleData E W := ⟨3,![10,11,28,23,14],![4,30,34,58,32]⟩
def data380 : PartitionData E W := ⟨7,![cycle380_0,cycle380_1,cycle380_2,cycle380_3,cycle380_4,cycle380_5,cycle380_6]⟩
lemma valid380 : data380.Valid src380 dst380 Finset.univ := by decide +kernel
lemma src_eq380 : src380 = src (unkey (representativeKey 380)) := by decide +kernel
lemma dst_eq380 : dst380 = dst (unkey (representativeKey 380)) := by decide +kernel
lemma certificate380 : Certificate 380 := by
  refine ⟨data380,?_,?_⟩
  · rw [← src_eq380,← dst_eq380]
    exact valid380
  · decide +kernel
#print axioms certificate380
end Erdos184Work.SixRepresentativeCertificates0

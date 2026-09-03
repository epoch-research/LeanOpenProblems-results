import Submission.SixRepresentativeCertificates0Base
namespace Erdos184Work.SixRepresentativeCertificates0
open PureSixRowModel0 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src50 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,16,32,34,6,18,46,30,44,8,20,58,44,32,10,46,34,22,58]
def dst50 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,16,32,34,4,18,46,30,44,6,20,58,44,32,8,46,34,22,58,10]
def cycle50_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,34,32,16]⟩
def cycle50_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,44,30]⟩
def cycle50_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle50_3 : CycleData E W := ⟨3,![3,29,22,23,24],![8,10,58,44,32]⟩
def cycle50_4 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,46,34,22]⟩
def cycle50_5 : CycleData E W := ⟨2,![6,16,17,11],![16,18,46,30]⟩
def cycle50_6 : CycleData E W := ⟨1,![8,28,21],![20,22,58]⟩
def data50 : PartitionData E W := ⟨7,![cycle50_0,cycle50_1,cycle50_2,cycle50_3,cycle50_4,cycle50_5,cycle50_6]⟩
lemma valid50 : data50.Valid src50 dst50 Finset.univ := by decide +kernel
lemma src_eq50 : src50 = src (unkey (representativeKey 50)) := by decide +kernel
lemma dst_eq50 : dst50 = dst (unkey (representativeKey 50)) := by decide +kernel
lemma certificate50 : Certificate 50 := by
  refine ⟨data50,?_,?_⟩
  · rw [← src_eq50,← dst_eq50]
    exact valid50
  · decide +kernel

def src51 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,16,32,34,6,18,46,44,30,8,20,44,58,32,10,46,22,34,58]
def dst51 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,16,32,34,4,18,46,44,30,6,20,44,58,32,8,46,22,34,58,10]
def cycle51_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,34,32,16]⟩
def cycle51_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle51_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle51_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle51_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle51_5 : CycleData E W := ⟨3,![6,16,17,18,11],![16,18,46,44,30]⟩
def cycle51_6 : CycleData E W := ⟨3,![8,27,28,22,21],![20,22,34,58,44]⟩
def data51 : PartitionData E W := ⟨7,![cycle51_0,cycle51_1,cycle51_2,cycle51_3,cycle51_4,cycle51_5,cycle51_6]⟩
lemma valid51 : data51.Valid src51 dst51 Finset.univ := by decide +kernel
lemma src_eq51 : src51 = src (unkey (representativeKey 51)) := by decide +kernel
lemma dst_eq51 : dst51 = dst (unkey (representativeKey 51)) := by decide +kernel
lemma certificate51 : Certificate 51 := by
  refine ⟨data51,?_,?_⟩
  · rw [← src_eq51,← dst_eq51]
    exact valid51
  · decide +kernel

def src52 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,16,32,34,6,18,46,44,30,8,20,58,44,32,10,46,22,34,58]
def dst52 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,16,32,34,4,18,46,44,30,6,20,58,44,32,8,46,22,34,58,10]
def cycle52_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,34,32,16]⟩
def cycle52_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle52_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle52_3 : CycleData E W := ⟨3,![3,29,22,23,24],![8,10,58,44,32]⟩
def cycle52_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle52_5 : CycleData E W := ⟨3,![6,16,17,18,11],![16,18,46,44,30]⟩
def cycle52_6 : CycleData E W := ⟨2,![8,27,28,21],![20,22,34,58]⟩
def data52 : PartitionData E W := ⟨7,![cycle52_0,cycle52_1,cycle52_2,cycle52_3,cycle52_4,cycle52_5,cycle52_6]⟩
lemma valid52 : data52.Valid src52 dst52 Finset.univ := by decide +kernel
lemma src_eq52 : src52 = src (unkey (representativeKey 52)) := by decide +kernel
lemma dst_eq52 : dst52 = dst (unkey (representativeKey 52)) := by decide +kernel
lemma certificate52 : Certificate 52 := by
  refine ⟨data52,?_,?_⟩
  · rw [← src_eq52,← dst_eq52]
    exact valid52
  · decide +kernel

def src53 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,16,32,34,6,18,46,44,30,8,20,58,44,32,10,46,34,22,58]
def dst53 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,16,32,34,4,18,46,44,30,6,20,58,44,32,8,46,34,22,58,10]
def cycle53_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,34,32,16]⟩
def cycle53_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle53_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle53_3 : CycleData E W := ⟨3,![3,29,22,23,24],![8,10,58,44,32]⟩
def cycle53_4 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,46,34,22]⟩
def cycle53_5 : CycleData E W := ⟨3,![6,16,17,18,11],![16,18,46,44,30]⟩
def cycle53_6 : CycleData E W := ⟨1,![8,28,21],![20,22,58]⟩
def data53 : PartitionData E W := ⟨7,![cycle53_0,cycle53_1,cycle53_2,cycle53_3,cycle53_4,cycle53_5,cycle53_6]⟩
lemma valid53 : data53.Valid src53 dst53 Finset.univ := by decide +kernel
lemma src_eq53 : src53 = src (unkey (representativeKey 53)) := by decide +kernel
lemma dst_eq53 : dst53 = dst (unkey (representativeKey 53)) := by decide +kernel
lemma certificate53 : Certificate 53 := by
  refine ⟨data53,?_,?_⟩
  · rw [← src_eq53,← dst_eq53]
    exact valid53
  · decide +kernel

def src54 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,30,44,46,8,20,44,58,32,10,46,22,34,58]
def dst54 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,30,44,46,6,20,44,58,32,8,46,22,34,58,10]
def cycle54_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle54_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle54_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle54_3 : CycleData E W := ⟨3,![4,29,28,27,9],![2,10,58,34,22]⟩
def cycle54_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle54_5 : CycleData E W := ⟨2,![8,26,18,21],![20,22,46,44]⟩
def cycle54_6 : CycleData E W := ⟨2,![11,23,22,17],![30,32,58,44]⟩
def data54 : PartitionData E W := ⟨7,![cycle54_0,cycle54_1,cycle54_2,cycle54_3,cycle54_4,cycle54_5,cycle54_6]⟩
lemma valid54 : data54.Valid src54 dst54 Finset.univ := by decide +kernel
lemma src_eq54 : src54 = src (unkey (representativeKey 54)) := by decide +kernel
lemma dst_eq54 : dst54 = dst (unkey (representativeKey 54)) := by decide +kernel
lemma certificate54 : Certificate 54 := by
  refine ⟨data54,?_,?_⟩
  · rw [← src_eq54,← dst_eq54]
    exact valid54
  · decide +kernel

def src55 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,30,44,46,8,20,58,44,32,10,46,22,34,58]
def dst55 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,30,44,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle55_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle55_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle55_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle55_3 : CycleData E W := ⟨3,![4,29,21,8,9],![2,10,58,20,22]⟩
def cycle55_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle55_5 : CycleData E W := ⟨1,![11,23,17],![30,32,44]⟩
def cycle55_6 : CycleData E W := ⟨3,![26,18,22,28,27],![22,46,44,58,34]⟩
def data55 : PartitionData E W := ⟨7,![cycle55_0,cycle55_1,cycle55_2,cycle55_3,cycle55_4,cycle55_5,cycle55_6]⟩
lemma valid55 : data55.Valid src55 dst55 Finset.univ := by decide +kernel
lemma src_eq55 : src55 = src (unkey (representativeKey 55)) := by decide +kernel
lemma dst_eq55 : dst55 = dst (unkey (representativeKey 55)) := by decide +kernel
lemma certificate55 : Certificate 55 := by
  refine ⟨data55,?_,?_⟩
  · rw [← src_eq55,← dst_eq55]
    exact valid55
  · decide +kernel

def src56 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,30,46,44,8,20,44,58,32,10,46,22,34,58]
def dst56 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,30,46,44,6,20,44,58,32,8,46,22,34,58,10]
def cycle56_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle56_1 : CycleData E W := ⟨3,![1,19,18,17,10],![4,6,44,46,30]⟩
def cycle56_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle56_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle56_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle56_5 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,32]⟩
def cycle56_6 : CycleData E W := ⟨3,![8,27,28,22,21],![20,22,34,58,44]⟩
def data56 : PartitionData E W := ⟨7,![cycle56_0,cycle56_1,cycle56_2,cycle56_3,cycle56_4,cycle56_5,cycle56_6]⟩
lemma valid56 : data56.Valid src56 dst56 Finset.univ := by decide +kernel
lemma src_eq56 : src56 = src (unkey (representativeKey 56)) := by decide +kernel
lemma dst_eq56 : dst56 = dst (unkey (representativeKey 56)) := by decide +kernel
lemma certificate56 : Certificate 56 := by
  refine ⟨data56,?_,?_⟩
  · rw [← src_eq56,← dst_eq56]
    exact valid56
  · decide +kernel

def src57 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,30,46,44,8,20,58,44,32,10,34,58,22,46]
def dst57 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,30,46,44,6,20,58,44,32,8,34,58,22,46,10]
def cycle57_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle57_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle57_2 : CycleData E W := ⟨4,![2,3,25,26,22,19],![6,8,10,34,58,44]⟩
def cycle57_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle57_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle57_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle57_6 : CycleData E W := ⟨2,![11,23,18,17],![30,32,44,46]⟩
def data57 : PartitionData E W := ⟨7,![cycle57_0,cycle57_1,cycle57_2,cycle57_3,cycle57_4,cycle57_5,cycle57_6]⟩
lemma valid57 : data57.Valid src57 dst57 Finset.univ := by decide +kernel
lemma src_eq57 : src57 = src (unkey (representativeKey 57)) := by decide +kernel
lemma dst_eq57 : dst57 = dst (unkey (representativeKey 57)) := by decide +kernel
lemma certificate57 : Certificate 57 := by
  refine ⟨data57,?_,?_⟩
  · rw [← src_eq57,← dst_eq57]
    exact valid57
  · decide +kernel

def src58 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,30,46,44,8,20,58,44,32,10,46,22,34,58]
def dst58 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,30,46,44,6,20,58,44,32,8,46,22,34,58,10]
def cycle58_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle58_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle58_2 : CycleData E W := ⟨3,![2,3,29,22,19],![6,8,10,58,44]⟩
def cycle58_3 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle58_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle58_5 : CycleData E W := ⟨2,![8,27,28,21],![20,22,34,58]⟩
def cycle58_6 : CycleData E W := ⟨2,![11,23,18,17],![30,32,44,46]⟩
def data58 : PartitionData E W := ⟨7,![cycle58_0,cycle58_1,cycle58_2,cycle58_3,cycle58_4,cycle58_5,cycle58_6]⟩
lemma valid58 : data58.Valid src58 dst58 Finset.univ := by decide +kernel
lemma src_eq58 : src58 = src (unkey (representativeKey 58)) := by decide +kernel
lemma dst_eq58 : dst58 = dst (unkey (representativeKey 58)) := by decide +kernel
lemma certificate58 : Certificate 58 := by
  refine ⟨data58,?_,?_⟩
  · rw [← src_eq58,← dst_eq58]
    exact valid58
  · decide +kernel

def src59 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,46,30,44,8,20,44,58,32,10,34,22,58,46]
def dst59 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,46,30,44,6,20,44,58,32,8,34,22,58,46,10]
def cycle59_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle59_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,44,30]⟩
def cycle59_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle59_3 : CycleData E W := ⟨4,![3,29,16,6,12,24],![8,10,46,18,16,32]⟩
def cycle59_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle59_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,44]⟩
def cycle59_6 : CycleData E W := ⟨2,![11,23,28,17],![30,32,58,46]⟩
def data59 : PartitionData E W := ⟨7,![cycle59_0,cycle59_1,cycle59_2,cycle59_3,cycle59_4,cycle59_5,cycle59_6]⟩
lemma valid59 : data59.Valid src59 dst59 Finset.univ := by decide +kernel
lemma src_eq59 : src59 = src (unkey (representativeKey 59)) := by decide +kernel
lemma dst_eq59 : dst59 = dst (unkey (representativeKey 59)) := by decide +kernel
lemma certificate59 : Certificate 59 := by
  refine ⟨data59,?_,?_⟩
  · rw [← src_eq59,← dst_eq59]
    exact valid59
  · decide +kernel

def src60 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,46,30,44,8,20,44,58,32,10,34,58,22,46]
def dst60 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,46,30,44,6,20,44,58,32,8,34,58,22,46,10]
def cycle60_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle60_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,44,30]⟩
def cycle60_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle60_3 : CycleData E W := ⟨3,![3,25,26,23,24],![8,10,34,58,32]⟩
def cycle60_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle60_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,46,30,32]⟩
def cycle60_6 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,44]⟩
def data60 : PartitionData E W := ⟨7,![cycle60_0,cycle60_1,cycle60_2,cycle60_3,cycle60_4,cycle60_5,cycle60_6]⟩
lemma valid60 : data60.Valid src60 dst60 Finset.univ := by decide +kernel
lemma src_eq60 : src60 = src (unkey (representativeKey 60)) := by decide +kernel
lemma dst_eq60 : dst60 = dst (unkey (representativeKey 60)) := by decide +kernel
lemma certificate60 : Certificate 60 := by
  refine ⟨data60,?_,?_⟩
  · rw [← src_eq60,← dst_eq60]
    exact valid60
  · decide +kernel

def src61 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,46,30,44,8,20,44,58,32,10,46,22,34,58]
def dst61 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,46,30,44,6,20,44,58,32,8,46,22,34,58,10]
def cycle61_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle61_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,44,30]⟩
def cycle61_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle61_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle61_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle61_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,46,30,32]⟩
def cycle61_6 : CycleData E W := ⟨3,![8,27,28,22,21],![20,22,34,58,44]⟩
def data61 : PartitionData E W := ⟨7,![cycle61_0,cycle61_1,cycle61_2,cycle61_3,cycle61_4,cycle61_5,cycle61_6]⟩
lemma valid61 : data61.Valid src61 dst61 Finset.univ := by decide +kernel
lemma src_eq61 : src61 = src (unkey (representativeKey 61)) := by decide +kernel
lemma dst_eq61 : dst61 = dst (unkey (representativeKey 61)) := by decide +kernel
lemma certificate61 : Certificate 61 := by
  refine ⟨data61,?_,?_⟩
  · rw [← src_eq61,← dst_eq61]
    exact valid61
  · decide +kernel

def src62 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,46,30,44,8,20,58,44,32,10,34,58,22,46]
def dst62 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,46,30,44,6,20,58,44,32,8,34,58,22,46,10]
def cycle62_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle62_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,46,30]⟩
def cycle62_2 : CycleData E W := ⟨4,![2,3,25,26,22,19],![6,8,10,34,58,44]⟩
def cycle62_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle62_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle62_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle62_6 : CycleData E W := ⟨1,![11,23,18],![30,32,44]⟩
def data62 : PartitionData E W := ⟨7,![cycle62_0,cycle62_1,cycle62_2,cycle62_3,cycle62_4,cycle62_5,cycle62_6]⟩
lemma valid62 : data62.Valid src62 dst62 Finset.univ := by decide +kernel
lemma src_eq62 : src62 = src (unkey (representativeKey 62)) := by decide +kernel
lemma dst_eq62 : dst62 = dst (unkey (representativeKey 62)) := by decide +kernel
lemma certificate62 : Certificate 62 := by
  refine ⟨data62,?_,?_⟩
  · rw [← src_eq62,← dst_eq62]
    exact valid62
  · decide +kernel

def src63 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,32,16,34,6,18,46,30,44,8,20,58,44,32,10,46,22,34,58]
def dst63 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,32,16,34,4,18,46,30,44,6,20,58,44,32,8,46,22,34,58,10]
def cycle63_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,34,16]⟩
def cycle63_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,46,30]⟩
def cycle63_2 : CycleData E W := ⟨3,![2,3,29,22,19],![6,8,10,58,44]⟩
def cycle63_3 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle63_4 : CycleData E W := ⟨3,![20,7,6,12,24],![8,20,18,16,32]⟩
def cycle63_5 : CycleData E W := ⟨2,![8,27,28,21],![20,22,34,58]⟩
def cycle63_6 : CycleData E W := ⟨1,![11,23,18],![30,32,44]⟩
def data63 : PartitionData E W := ⟨7,![cycle63_0,cycle63_1,cycle63_2,cycle63_3,cycle63_4,cycle63_5,cycle63_6]⟩
lemma valid63 : data63.Valid src63 dst63 Finset.univ := by decide +kernel
lemma src_eq63 : src63 = src (unkey (representativeKey 63)) := by decide +kernel
lemma dst_eq63 : dst63 = dst (unkey (representativeKey 63)) := by decide +kernel
lemma certificate63 : Certificate 63 := by
  refine ⟨data63,?_,?_⟩
  · rw [← src_eq63,← dst_eq63]
    exact valid63
  · decide +kernel

def src64 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,32,44,58,10,34,58,22,46]
def dst64 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,32,44,58,8,34,58,22,46,10]
def cycle64_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle64_1 : CycleData E W := ⟨3,![1,19,18,17,10],![4,6,46,44,30]⟩
def cycle64_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle64_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle64_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle64_5 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle64_6 : CycleData E W := ⟨3,![8,27,23,22,21],![20,22,58,44,32]⟩
def data64 : PartitionData E W := ⟨7,![cycle64_0,cycle64_1,cycle64_2,cycle64_3,cycle64_4,cycle64_5,cycle64_6]⟩
lemma valid64 : data64.Valid src64 dst64 Finset.univ := by decide +kernel
lemma src_eq64 : src64 = src (unkey (representativeKey 64)) := by decide +kernel
lemma dst_eq64 : dst64 = dst (unkey (representativeKey 64)) := by decide +kernel
lemma certificate64 : Certificate 64 := by
  refine ⟨data64,?_,?_⟩
  · rw [← src_eq64,← dst_eq64]
    exact valid64
  · decide +kernel

def src65 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,32,58,44,10,34,58,22,46]
def dst65 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle65_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle65_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle65_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle65_3 : CycleData E W := ⟨4,![3,25,12,6,7,20],![8,10,34,16,18,20]⟩
def cycle65_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle65_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,32]⟩
def cycle65_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data65 : PartitionData E W := ⟨7,![cycle65_0,cycle65_1,cycle65_2,cycle65_3,cycle65_4,cycle65_5,cycle65_6]⟩
lemma valid65 : data65.Valid src65 dst65 Finset.univ := by decide +kernel
lemma src_eq65 : src65 = src (unkey (representativeKey 65)) := by decide +kernel
lemma dst_eq65 : dst65 = dst (unkey (representativeKey 65)) := by decide +kernel
lemma certificate65 : Certificate 65 := by
  refine ⟨data65,?_,?_⟩
  · rw [← src_eq65,← dst_eq65]
    exact valid65
  · decide +kernel

def src66 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,32,58,44,10,46,22,34,58]
def dst66 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,32,58,44,8,46,22,34,58,10]
def cycle66_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle66_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle66_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle66_3 : CycleData E W := ⟨3,![3,29,22,21,20],![8,10,58,32,20]⟩
def cycle66_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle66_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle66_6 : CycleData E W := ⟨2,![11,28,23,17],![30,34,58,44]⟩
def data66 : PartitionData E W := ⟨7,![cycle66_0,cycle66_1,cycle66_2,cycle66_3,cycle66_4,cycle66_5,cycle66_6]⟩
lemma valid66 : data66.Valid src66 dst66 Finset.univ := by decide +kernel
lemma src_eq66 : src66 = src (unkey (representativeKey 66)) := by decide +kernel
lemma dst_eq66 : dst66 = dst (unkey (representativeKey 66)) := by decide +kernel
lemma certificate66 : Certificate 66 := by
  refine ⟨data66,?_,?_⟩
  · rw [← src_eq66,← dst_eq66]
    exact valid66
  · decide +kernel

def src67 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,34,58,22,46]
def dst67 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,34,58,22,46,10]
def cycle67_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle67_1 : CycleData E W := ⟨3,![1,19,18,17,10],![4,6,46,44,30]⟩
def cycle67_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle67_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle67_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle67_5 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle67_6 : CycleData E W := ⟨3,![8,27,23,22,21],![20,22,58,32,44]⟩
def data67 : PartitionData E W := ⟨7,![cycle67_0,cycle67_1,cycle67_2,cycle67_3,cycle67_4,cycle67_5,cycle67_6]⟩
lemma valid67 : data67.Valid src67 dst67 Finset.univ := by decide +kernel
lemma src_eq67 : src67 = src (unkey (representativeKey 67)) := by decide +kernel
lemma dst_eq67 : dst67 = dst (unkey (representativeKey 67)) := by decide +kernel
lemma certificate67 : Certificate 67 := by
  refine ⟨data67,?_,?_⟩
  · rw [← src_eq67,← dst_eq67]
    exact valid67
  · decide +kernel

def src68 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,44,32,58,10,46,22,34,58]
def dst68 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,44,32,58,8,46,22,34,58,10]
def cycle68_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle68_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle68_2 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle68_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle68_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle68_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle68_6 : CycleData E W := ⟨3,![11,28,23,22,17],![30,34,58,32,44]⟩
def data68 : PartitionData E W := ⟨7,![cycle68_0,cycle68_1,cycle68_2,cycle68_3,cycle68_4,cycle68_5,cycle68_6]⟩
lemma valid68 : data68.Valid src68 dst68 Finset.univ := by decide +kernel
lemma src_eq68 : src68 = src (unkey (representativeKey 68)) := by decide +kernel
lemma dst_eq68 : dst68 = dst (unkey (representativeKey 68)) := by decide +kernel
lemma certificate68 : Certificate 68 := by
  refine ⟨data68,?_,?_⟩
  · rw [← src_eq68,← dst_eq68]
    exact valid68
  · decide +kernel

def src69 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,44,58,32,10,34,58,22,46]
def dst69 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,44,58,32,8,34,58,22,46,10]
def cycle69_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle69_1 : CycleData E W := ⟨3,![1,19,18,17,10],![4,6,46,44,30]⟩
def cycle69_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle69_3 : CycleData E W := ⟨3,![3,25,26,23,24],![8,10,34,58,32]⟩
def cycle69_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle69_5 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle69_6 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,44]⟩
def data69 : PartitionData E W := ⟨7,![cycle69_0,cycle69_1,cycle69_2,cycle69_3,cycle69_4,cycle69_5,cycle69_6]⟩
lemma valid69 : data69.Valid src69 dst69 Finset.univ := by decide +kernel
lemma src_eq69 : src69 = src (unkey (representativeKey 69)) := by decide +kernel
lemma dst_eq69 : dst69 = dst (unkey (representativeKey 69)) := by decide +kernel
lemma certificate69 : Certificate 69 := by
  refine ⟨data69,?_,?_⟩
  · rw [← src_eq69,← dst_eq69]
    exact valid69
  · decide +kernel

def src70 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,44,58,32,10,46,22,34,58]
def dst70 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,44,58,32,8,46,22,34,58,10]
def cycle70_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle70_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle70_2 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle70_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle70_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle70_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle70_6 : CycleData E W := ⟨2,![11,28,22,17],![30,34,58,44]⟩
def data70 : PartitionData E W := ⟨7,![cycle70_0,cycle70_1,cycle70_2,cycle70_3,cycle70_4,cycle70_5,cycle70_6]⟩
lemma valid70 : data70.Valid src70 dst70 Finset.univ := by decide +kernel
lemma src_eq70 : src70 = src (unkey (representativeKey 70)) := by decide +kernel
lemma dst_eq70 : dst70 = dst (unkey (representativeKey 70)) := by decide +kernel
lemma certificate70 : Certificate 70 := by
  refine ⟨data70,?_,?_⟩
  · rw [← src_eq70,← dst_eq70]
    exact valid70
  · decide +kernel

def src71 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,58,32,44,10,34,58,22,46]
def dst71 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,58,32,44,8,34,58,22,46,10]
def cycle71_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle71_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle71_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle71_3 : CycleData E W := ⟨4,![3,25,12,6,7,20],![8,10,34,16,18,20]⟩
def cycle71_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle71_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle71_6 : CycleData E W := ⟨3,![11,26,22,23,17],![30,34,58,32,44]⟩
def data71 : PartitionData E W := ⟨7,![cycle71_0,cycle71_1,cycle71_2,cycle71_3,cycle71_4,cycle71_5,cycle71_6]⟩
lemma valid71 : data71.Valid src71 dst71 Finset.univ := by decide +kernel
lemma src_eq71 : src71 = src (unkey (representativeKey 71)) := by decide +kernel
lemma dst_eq71 : dst71 = dst (unkey (representativeKey 71)) := by decide +kernel
lemma certificate71 : Certificate 71 := by
  refine ⟨data71,?_,?_⟩
  · rw [← src_eq71,← dst_eq71]
    exact valid71
  · decide +kernel

def src72 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,58,32,44,10,46,22,34,58]
def dst72 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,58,32,44,8,46,22,34,58,10]
def cycle72_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle72_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle72_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle72_3 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,20]⟩
def cycle72_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle72_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle72_6 : CycleData E W := ⟨3,![11,28,22,23,17],![30,34,58,32,44]⟩
def data72 : PartitionData E W := ⟨7,![cycle72_0,cycle72_1,cycle72_2,cycle72_3,cycle72_4,cycle72_5,cycle72_6]⟩
lemma valid72 : data72.Valid src72 dst72 Finset.univ := by decide +kernel
lemma src_eq72 : src72 = src (unkey (representativeKey 72)) := by decide +kernel
lemma dst_eq72 : dst72 = dst (unkey (representativeKey 72)) := by decide +kernel
lemma certificate72 : Certificate 72 := by
  refine ⟨data72,?_,?_⟩
  · rw [← src_eq72,← dst_eq72]
    exact valid72
  · decide +kernel

def src73 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,58,44,32,10,34,58,22,46]
def dst73 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle73_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle73_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle73_2 : CycleData E W := ⟨3,![2,24,23,18,19],![6,8,32,44,46]⟩
def cycle73_3 : CycleData E W := ⟨4,![3,25,12,6,7,20],![8,10,34,16,18,20]⟩
def cycle73_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle73_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle73_6 : CycleData E W := ⟨2,![11,26,22,17],![30,34,58,44]⟩
def data73 : PartitionData E W := ⟨7,![cycle73_0,cycle73_1,cycle73_2,cycle73_3,cycle73_4,cycle73_5,cycle73_6]⟩
lemma valid73 : data73.Valid src73 dst73 Finset.univ := by decide +kernel
lemma src_eq73 : src73 = src (unkey (representativeKey 73)) := by decide +kernel
lemma dst_eq73 : dst73 = dst (unkey (representativeKey 73)) := by decide +kernel
lemma certificate73 : Certificate 73 := by
  refine ⟨data73,?_,?_⟩
  · rw [← src_eq73,← dst_eq73]
    exact valid73
  · decide +kernel

def src74 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,44,46,8,20,58,44,32,10,46,22,34,58]
def dst74 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,44,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle74_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle74_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle74_2 : CycleData E W := ⟨3,![2,24,23,18,19],![6,8,32,44,46]⟩
def cycle74_3 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,20]⟩
def cycle74_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle74_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle74_6 : CycleData E W := ⟨2,![11,28,22,17],![30,34,58,44]⟩
def data74 : PartitionData E W := ⟨7,![cycle74_0,cycle74_1,cycle74_2,cycle74_3,cycle74_4,cycle74_5,cycle74_6]⟩
lemma valid74 : data74.Valid src74 dst74 Finset.univ := by decide +kernel
lemma src_eq74 : src74 = src (unkey (representativeKey 74)) := by decide +kernel
lemma dst_eq74 : dst74 = dst (unkey (representativeKey 74)) := by decide +kernel
lemma certificate74 : Certificate 74 := by
  refine ⟨data74,?_,?_⟩
  · rw [← src_eq74,← dst_eq74]
    exact valid74
  · decide +kernel

def src75 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,46,44,8,20,32,44,58,10,46,22,34,58]
def dst75 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,46,44,6,20,32,44,58,8,46,22,34,58,10]
def cycle75_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle75_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle75_2 : CycleData E W := ⟨3,![2,20,21,22,19],![6,8,20,32,44]⟩
def cycle75_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle75_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle75_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle75_6 : CycleData E W := ⟨3,![11,28,23,18,17],![30,34,58,44,46]⟩
def data75 : PartitionData E W := ⟨7,![cycle75_0,cycle75_1,cycle75_2,cycle75_3,cycle75_4,cycle75_5,cycle75_6]⟩
lemma valid75 : data75.Valid src75 dst75 Finset.univ := by decide +kernel
lemma src_eq75 : src75 = src (unkey (representativeKey 75)) := by decide +kernel
lemma dst_eq75 : dst75 = dst (unkey (representativeKey 75)) := by decide +kernel
lemma certificate75 : Certificate 75 := by
  refine ⟨data75,?_,?_⟩
  · rw [← src_eq75,← dst_eq75]
    exact valid75
  · decide +kernel

def src76 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,46,44,8,20,44,32,58,10,34,58,22,46]
def dst76 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,46,44,6,20,44,32,58,8,34,58,22,46,10]
def cycle76_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle76_1 : CycleData E W := ⟨3,![1,19,18,17,10],![4,6,44,46,30]⟩
def cycle76_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle76_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle76_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle76_5 : CycleData E W := ⟨2,![6,16,11,12],![16,18,30,34]⟩
def cycle76_6 : CycleData E W := ⟨3,![8,27,23,22,21],![20,22,58,32,44]⟩
def data76 : PartitionData E W := ⟨7,![cycle76_0,cycle76_1,cycle76_2,cycle76_3,cycle76_4,cycle76_5,cycle76_6]⟩
lemma valid76 : data76.Valid src76 dst76 Finset.univ := by decide +kernel
lemma src_eq76 : src76 = src (unkey (representativeKey 76)) := by decide +kernel
lemma dst_eq76 : dst76 = dst (unkey (representativeKey 76)) := by decide +kernel
lemma certificate76 : Certificate 76 := by
  refine ⟨data76,?_,?_⟩
  · rw [← src_eq76,← dst_eq76]
    exact valid76
  · decide +kernel

def src77 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,46,44,8,20,58,32,44,10,34,58,22,46]
def dst77 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,46,44,6,20,58,32,44,8,34,58,22,46,10]
def cycle77_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle77_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle77_2 : CycleData E W := ⟨1,![2,24,19],![6,8,44]⟩
def cycle77_3 : CycleData E W := ⟨3,![4,3,20,8,9],![2,10,8,20,22]⟩
def cycle77_4 : CycleData E W := ⟨3,![6,7,21,26,12],![16,18,20,58,34]⟩
def cycle77_5 : CycleData E W := ⟨2,![25,11,17,29],![10,34,30,46]⟩
def cycle77_6 : CycleData E W := ⟨3,![27,22,23,18,28],![22,58,32,44,46]⟩
def data77 : PartitionData E W := ⟨7,![cycle77_0,cycle77_1,cycle77_2,cycle77_3,cycle77_4,cycle77_5,cycle77_6]⟩
lemma valid77 : data77.Valid src77 dst77 Finset.univ := by decide +kernel
lemma src_eq77 : src77 = src (unkey (representativeKey 77)) := by decide +kernel
lemma dst_eq77 : dst77 = dst (unkey (representativeKey 77)) := by decide +kernel
lemma certificate77 : Certificate 77 := by
  refine ⟨data77,?_,?_⟩
  · rw [← src_eq77,← dst_eq77]
    exact valid77
  · decide +kernel

def src78 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,30,46,44,8,20,58,44,32,10,34,58,22,46]
def dst78 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,30,46,44,6,20,58,44,32,8,34,58,22,46,10]
def cycle78_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle78_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle78_2 : CycleData E W := ⟨2,![2,24,23,19],![6,8,32,44]⟩
def cycle78_3 : CycleData E W := ⟨3,![4,3,20,8,9],![2,10,8,20,22]⟩
def cycle78_4 : CycleData E W := ⟨3,![6,7,21,26,12],![16,18,20,58,34]⟩
def cycle78_5 : CycleData E W := ⟨2,![25,11,17,29],![10,34,30,46]⟩
def cycle78_6 : CycleData E W := ⟨2,![27,22,18,28],![22,58,44,46]⟩
def data78 : PartitionData E W := ⟨7,![cycle78_0,cycle78_1,cycle78_2,cycle78_3,cycle78_4,cycle78_5,cycle78_6]⟩
lemma valid78 : data78.Valid src78 dst78 Finset.univ := by decide +kernel
lemma src_eq78 : src78 = src (unkey (representativeKey 78)) := by decide +kernel
lemma dst_eq78 : dst78 = dst (unkey (representativeKey 78)) := by decide +kernel
lemma certificate78 : Certificate 78 := by
  refine ⟨data78,?_,?_⟩
  · rw [← src_eq78,← dst_eq78]
    exact valid78
  · decide +kernel

def src79 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,32,44,58,10,46,22,34,58]
def dst79 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,32,44,58,8,46,22,34,58,10]
def cycle79_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle79_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle79_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle79_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle79_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle79_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,44,30,34]⟩
def cycle79_6 : CycleData E W := ⟨4,![8,27,28,23,22,21],![20,22,34,58,44,32]⟩
def data79 : PartitionData E W := ⟨7,![cycle79_0,cycle79_1,cycle79_2,cycle79_3,cycle79_4,cycle79_5,cycle79_6]⟩
lemma valid79 : data79.Valid src79 dst79 Finset.univ := by decide +kernel
lemma src_eq79 : src79 = src (unkey (representativeKey 79)) := by decide +kernel
lemma dst_eq79 : dst79 = dst (unkey (representativeKey 79)) := by decide +kernel
lemma certificate79 : Certificate 79 := by
  refine ⟨data79,?_,?_⟩
  · rw [← src_eq79,← dst_eq79]
    exact valid79
  · decide +kernel

def src80 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,32,58,44,10,34,58,22,46]
def dst80 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle80_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle80_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle80_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle80_3 : CycleData E W := ⟨4,![3,25,12,6,16,24],![8,10,34,16,18,44]⟩
def cycle80_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle80_5 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,32]⟩
def cycle80_6 : CycleData E W := ⟨2,![11,26,23,17],![30,34,58,44]⟩
def data80 : PartitionData E W := ⟨7,![cycle80_0,cycle80_1,cycle80_2,cycle80_3,cycle80_4,cycle80_5,cycle80_6]⟩
lemma valid80 : data80.Valid src80 dst80 Finset.univ := by decide +kernel
lemma src_eq80 : src80 = src (unkey (representativeKey 80)) := by decide +kernel
lemma dst_eq80 : dst80 = dst (unkey (representativeKey 80)) := by decide +kernel
lemma certificate80 : Certificate 80 := by
  refine ⟨data80,?_,?_⟩
  · rw [← src_eq80,← dst_eq80]
    exact valid80
  · decide +kernel

def src81 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,32,58,44,10,46,22,34,58]
def dst81 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,32,58,44,8,46,22,34,58,10]
def cycle81_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle81_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle81_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle81_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,44]⟩
def cycle81_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle81_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,44,30,34]⟩
def cycle81_6 : CycleData E W := ⟨3,![8,27,28,22,21],![20,22,34,58,32]⟩
def data81 : PartitionData E W := ⟨7,![cycle81_0,cycle81_1,cycle81_2,cycle81_3,cycle81_4,cycle81_5,cycle81_6]⟩
lemma valid81 : data81.Valid src81 dst81 Finset.univ := by decide +kernel
lemma src_eq81 : src81 = src (unkey (representativeKey 81)) := by decide +kernel
lemma dst_eq81 : dst81 = dst (unkey (representativeKey 81)) := by decide +kernel
lemma certificate81 : Certificate 81 := by
  refine ⟨data81,?_,?_⟩
  · rw [← src_eq81,← dst_eq81]
    exact valid81
  · decide +kernel

def src82 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,44,58,32,10,34,58,22,46]
def dst82 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,44,58,32,8,34,58,22,46,10]
def cycle82_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle82_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle82_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle82_3 : CycleData E W := ⟨3,![3,25,26,23,24],![8,10,34,58,32]⟩
def cycle82_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle82_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,44,30,34]⟩
def cycle82_6 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,44]⟩
def data82 : PartitionData E W := ⟨7,![cycle82_0,cycle82_1,cycle82_2,cycle82_3,cycle82_4,cycle82_5,cycle82_6]⟩
lemma valid82 : data82.Valid src82 dst82 Finset.univ := by decide +kernel
lemma src_eq82 : src82 = src (unkey (representativeKey 82)) := by decide +kernel
lemma dst_eq82 : dst82 = dst (unkey (representativeKey 82)) := by decide +kernel
lemma certificate82 : Certificate 82 := by
  refine ⟨data82,?_,?_⟩
  · rw [← src_eq82,← dst_eq82]
    exact valid82
  · decide +kernel

def src83 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,44,58,32,10,46,22,34,58]
def dst83 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,44,58,32,8,46,22,34,58,10]
def cycle83_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle83_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle83_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle83_3 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,32]⟩
def cycle83_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle83_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,44,30,34]⟩
def cycle83_6 : CycleData E W := ⟨3,![8,27,28,22,21],![20,22,34,58,44]⟩
def data83 : PartitionData E W := ⟨7,![cycle83_0,cycle83_1,cycle83_2,cycle83_3,cycle83_4,cycle83_5,cycle83_6]⟩
lemma valid83 : data83.Valid src83 dst83 Finset.univ := by decide +kernel
lemma src_eq83 : src83 = src (unkey (representativeKey 83)) := by decide +kernel
lemma dst_eq83 : dst83 = dst (unkey (representativeKey 83)) := by decide +kernel
lemma certificate83 : Certificate 83 := by
  refine ⟨data83,?_,?_⟩
  · rw [← src_eq83,← dst_eq83]
    exact valid83
  · decide +kernel

def src84 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,30,46,8,20,58,44,32,10,34,58,22,46]
def dst84 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,30,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle84_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle84_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle84_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle84_3 : CycleData E W := ⟨5,![3,25,12,6,16,23,24],![8,10,34,16,18,44,32]⟩
def cycle84_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle84_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle84_6 : CycleData E W := ⟨2,![11,26,22,17],![30,34,58,44]⟩
def data84 : PartitionData E W := ⟨7,![cycle84_0,cycle84_1,cycle84_2,cycle84_3,cycle84_4,cycle84_5,cycle84_6]⟩
lemma valid84 : data84.Valid src84 dst84 Finset.univ := by decide +kernel
lemma src_eq84 : src84 = src (unkey (representativeKey 84)) := by decide +kernel
lemma dst_eq84 : dst84 = dst (unkey (representativeKey 84)) := by decide +kernel
lemma certificate84 : Certificate 84 := by
  refine ⟨data84,?_,?_⟩
  · rw [← src_eq84,← dst_eq84]
    exact valid84
  · decide +kernel

def src85 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,46,30,8,20,32,44,58,10,46,22,34,58]
def dst85 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,46,30,6,20,32,44,58,8,46,22,34,58,10]
def cycle85_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle85_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle85_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle85_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle85_4 : CycleData E W := ⟨5,![4,25,17,22,21,8,9],![2,10,46,44,32,20,22]⟩
def cycle85_5 : CycleData E W := ⟨3,![6,16,23,28,12],![16,18,44,58,34]⟩
def cycle85_6 : CycleData E W := ⟨2,![26,18,11,27],![22,46,30,34]⟩
def data85 : PartitionData E W := ⟨7,![cycle85_0,cycle85_1,cycle85_2,cycle85_3,cycle85_4,cycle85_5,cycle85_6]⟩
lemma valid85 : data85.Valid src85 dst85 Finset.univ := by decide +kernel
lemma src_eq85 : src85 = src (unkey (representativeKey 85)) := by decide +kernel
lemma dst_eq85 : dst85 = dst (unkey (representativeKey 85)) := by decide +kernel
lemma certificate85 : Certificate 85 := by
  refine ⟨data85,?_,?_⟩
  · rw [← src_eq85,← dst_eq85]
    exact valid85
  · decide +kernel

def src86 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,46,30,8,20,58,32,44,10,34,58,22,46]
def dst86 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,46,30,6,20,58,32,44,8,34,58,22,46,10]
def cycle86_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle86_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle86_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle86_3 : CycleData E W := ⟨4,![3,25,12,6,16,24],![8,10,34,16,18,44]⟩
def cycle86_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle86_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle86_6 : CycleData E W := ⟨4,![11,26,22,23,17,18],![30,34,58,32,44,46]⟩
def data86 : PartitionData E W := ⟨7,![cycle86_0,cycle86_1,cycle86_2,cycle86_3,cycle86_4,cycle86_5,cycle86_6]⟩
lemma valid86 : data86.Valid src86 dst86 Finset.univ := by decide +kernel
lemma src_eq86 : src86 = src (unkey (representativeKey 86)) := by decide +kernel
lemma dst_eq86 : dst86 = dst (unkey (representativeKey 86)) := by decide +kernel
lemma certificate86 : Certificate 86 := by
  refine ⟨data86,?_,?_⟩
  · rw [← src_eq86,← dst_eq86]
    exact valid86
  · decide +kernel

def src87 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,44,46,30,8,20,58,44,32,10,34,58,22,46]
def dst87 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,44,46,30,6,20,58,44,32,8,34,58,22,46,10]
def cycle87_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle87_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle87_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle87_3 : CycleData E W := ⟨5,![3,25,12,6,16,23,24],![8,10,34,16,18,44,32]⟩
def cycle87_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle87_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle87_6 : CycleData E W := ⟨3,![11,26,22,17,18],![30,34,58,44,46]⟩
def data87 : PartitionData E W := ⟨7,![cycle87_0,cycle87_1,cycle87_2,cycle87_3,cycle87_4,cycle87_5,cycle87_6]⟩
lemma valid87 : data87.Valid src87 dst87 Finset.univ := by decide +kernel
lemma src_eq87 : src87 = src (unkey (representativeKey 87)) := by decide +kernel
lemma dst_eq87 : dst87 = dst (unkey (representativeKey 87)) := by decide +kernel
lemma certificate87 : Certificate 87 := by
  refine ⟨data87,?_,?_⟩
  · rw [← src_eq87,← dst_eq87]
    exact valid87
  · decide +kernel

def src88 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,46,30,44,8,20,32,44,58,10,46,22,34,58]
def dst88 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,46,30,44,6,20,32,44,58,8,46,22,34,58,10]
def cycle88_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle88_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,46,30]⟩
def cycle88_2 : CycleData E W := ⟨3,![2,20,21,22,19],![6,8,20,32,44]⟩
def cycle88_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle88_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle88_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle88_6 : CycleData E W := ⟨2,![11,28,23,18],![30,34,58,44]⟩
def data88 : PartitionData E W := ⟨7,![cycle88_0,cycle88_1,cycle88_2,cycle88_3,cycle88_4,cycle88_5,cycle88_6]⟩
lemma valid88 : data88.Valid src88 dst88 Finset.univ := by decide +kernel
lemma src_eq88 : src88 = src (unkey (representativeKey 88)) := by decide +kernel
lemma dst_eq88 : dst88 = dst (unkey (representativeKey 88)) := by decide +kernel
lemma certificate88 : Certificate 88 := by
  refine ⟨data88,?_,?_⟩
  · rw [← src_eq88,← dst_eq88]
    exact valid88
  · decide +kernel

def src89 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,46,30,44,8,20,32,58,44,10,46,22,34,58]
def dst89 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,46,30,44,6,20,32,58,44,8,46,22,34,58,10]
def cycle89_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle89_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,46,30]⟩
def cycle89_2 : CycleData E W := ⟨1,![2,24,19],![6,8,44]⟩
def cycle89_3 : CycleData E W := ⟨3,![3,29,22,21,20],![8,10,58,32,20]⟩
def cycle89_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle89_5 : CycleData E W := ⟨3,![6,7,8,27,12],![16,18,20,22,34]⟩
def cycle89_6 : CycleData E W := ⟨2,![11,28,23,18],![30,34,58,44]⟩
def data89 : PartitionData E W := ⟨7,![cycle89_0,cycle89_1,cycle89_2,cycle89_3,cycle89_4,cycle89_5,cycle89_6]⟩
lemma valid89 : data89.Valid src89 dst89 Finset.univ := by decide +kernel
lemma src_eq89 : src89 = src (unkey (representativeKey 89)) := by decide +kernel
lemma dst_eq89 : dst89 = dst (unkey (representativeKey 89)) := by decide +kernel
lemma certificate89 : Certificate 89 := by
  refine ⟨data89,?_,?_⟩
  · rw [← src_eq89,← dst_eq89]
    exact valid89
  · decide +kernel

def src90 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,46,30,44,8,20,44,58,32,10,34,58,22,46]
def dst90 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,46,30,44,6,20,44,58,32,8,34,58,22,46,10]
def cycle90_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle90_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,44,30]⟩
def cycle90_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle90_3 : CycleData E W := ⟨3,![3,25,26,23,24],![8,10,34,58,32]⟩
def cycle90_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle90_5 : CycleData E W := ⟨3,![6,16,17,11,12],![16,18,46,30,34]⟩
def cycle90_6 : CycleData E W := ⟨2,![8,27,22,21],![20,22,58,44]⟩
def data90 : PartitionData E W := ⟨7,![cycle90_0,cycle90_1,cycle90_2,cycle90_3,cycle90_4,cycle90_5,cycle90_6]⟩
lemma valid90 : data90.Valid src90 dst90 Finset.univ := by decide +kernel
lemma src_eq90 : src90 = src (unkey (representativeKey 90)) := by decide +kernel
lemma dst_eq90 : dst90 = dst (unkey (representativeKey 90)) := by decide +kernel
lemma certificate90 : Certificate 90 := by
  refine ⟨data90,?_,?_⟩
  · rw [← src_eq90,← dst_eq90]
    exact valid90
  · decide +kernel

def src91 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,46,30,44,8,20,58,44,32,10,34,58,22,46]
def dst91 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,46,30,44,6,20,58,44,32,8,34,58,22,46,10]
def cycle91_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle91_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,46,30]⟩
def cycle91_2 : CycleData E W := ⟨2,![2,24,23,19],![6,8,32,44]⟩
def cycle91_3 : CycleData E W := ⟨4,![3,25,12,6,7,20],![8,10,34,16,18,20]⟩
def cycle91_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle91_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle91_6 : CycleData E W := ⟨2,![11,26,22,18],![30,34,58,44]⟩
def data91 : PartitionData E W := ⟨7,![cycle91_0,cycle91_1,cycle91_2,cycle91_3,cycle91_4,cycle91_5,cycle91_6]⟩
lemma valid91 : data91.Valid src91 dst91 Finset.univ := by decide +kernel
lemma src_eq91 : src91 = src (unkey (representativeKey 91)) := by decide +kernel
lemma dst_eq91 : dst91 = dst (unkey (representativeKey 91)) := by decide +kernel
lemma certificate91 : Certificate 91 := by
  refine ⟨data91,?_,?_⟩
  · rw [← src_eq91,← dst_eq91]
    exact valid91
  · decide +kernel

def src92 : E → W := ![2,4,6,8,10,2,16,18,20,22,4,30,34,16,32,6,18,46,44,30,8,20,32,44,58,10,46,22,34,58]
def dst92 : E → W := ![4,6,8,10,2,16,18,20,22,2,30,34,16,32,4,18,46,44,30,6,20,32,44,58,8,46,22,34,58,10]
def cycle92_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle92_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle92_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle92_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle92_4 : CycleData E W := ⟨5,![4,25,17,22,21,8,9],![2,10,46,44,32,20,22]⟩
def cycle92_5 : CycleData E W := ⟨3,![6,16,26,27,12],![16,18,46,22,34]⟩
def cycle92_6 : CycleData E W := ⟨2,![11,28,23,18],![30,34,58,44]⟩
def data92 : PartitionData E W := ⟨7,![cycle92_0,cycle92_1,cycle92_2,cycle92_3,cycle92_4,cycle92_5,cycle92_6]⟩
lemma valid92 : data92.Valid src92 dst92 Finset.univ := by decide +kernel
lemma src_eq92 : src92 = src (unkey (representativeKey 92)) := by decide +kernel
lemma dst_eq92 : dst92 = dst (unkey (representativeKey 92)) := by decide +kernel
lemma certificate92 : Certificate 92 := by
  refine ⟨data92,?_,?_⟩
  · rw [← src_eq92,← dst_eq92]
    exact valid92
  · decide +kernel

def src93 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,30,46,44,8,32,20,44,58,10,34,22,58,46]
def dst93 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,30,46,44,6,32,20,44,58,8,34,22,58,46,10]
def cycle93_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle93_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle93_2 : CycleData E W := ⟨3,![3,25,26,27,24],![8,10,34,22,58]⟩
def cycle93_3 : CycleData E W := ⟨4,![4,29,17,12,21,9],![2,10,46,30,32,20]⟩
def cycle93_4 : CycleData E W := ⟨1,![6,16,11],![16,18,30]⟩
def cycle93_5 : CycleData E W := ⟨3,![15,7,8,22,19],![6,18,22,20,44]⟩
def cycle93_6 : CycleData E W := ⟨1,![18,28,23],![44,46,58]⟩
def data93 : PartitionData E W := ⟨7,![cycle93_0,cycle93_1,cycle93_2,cycle93_3,cycle93_4,cycle93_5,cycle93_6]⟩
lemma valid93 : data93.Valid src93 dst93 Finset.univ := by decide +kernel
lemma src_eq93 : src93 = src (unkey (representativeKey 93)) := by decide +kernel
lemma dst_eq93 : dst93 = dst (unkey (representativeKey 93)) := by decide +kernel
lemma certificate93 : Certificate 93 := by
  refine ⟨data93,?_,?_⟩
  · rw [← src_eq93,← dst_eq93]
    exact valid93
  · decide +kernel

def src94 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,30,46,44,8,32,20,44,58,10,34,58,22,46]
def dst94 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,30,46,44,6,32,20,44,58,8,34,58,22,46,10]
def cycle94_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle94_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle94_2 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle94_3 : CycleData E W := ⟨4,![4,29,17,12,21,9],![2,10,46,30,32,20]⟩
def cycle94_4 : CycleData E W := ⟨1,![6,16,11],![16,18,30]⟩
def cycle94_5 : CycleData E W := ⟨3,![15,7,8,22,19],![6,18,22,20,44]⟩
def cycle94_6 : CycleData E W := ⟨2,![27,23,18,28],![22,58,44,46]⟩
def data94 : PartitionData E W := ⟨7,![cycle94_0,cycle94_1,cycle94_2,cycle94_3,cycle94_4,cycle94_5,cycle94_6]⟩
lemma valid94 : data94.Valid src94 dst94 Finset.univ := by decide +kernel
lemma src_eq94 : src94 = src (unkey (representativeKey 94)) := by decide +kernel
lemma dst_eq94 : dst94 = dst (unkey (representativeKey 94)) := by decide +kernel
lemma certificate94 : Certificate 94 := by
  refine ⟨data94,?_,?_⟩
  · rw [← src_eq94,← dst_eq94]
    exact valid94
  · decide +kernel

def src95 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,44,30,46,8,20,32,44,58,10,34,22,46,58]
def dst95 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,44,30,46,6,20,32,44,58,8,34,22,46,58,10]
def cycle95_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle95_1 : CycleData E W := ⟨4,![1,2,20,21,13,14],![4,6,8,20,32,34]⟩
def cycle95_2 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle95_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,20]⟩
def cycle95_4 : CycleData E W := ⟨2,![6,16,17,11],![16,18,44,30]⟩
def cycle95_5 : CycleData E W := ⟨2,![15,7,27,19],![6,18,22,46]⟩
def cycle95_6 : CycleData E W := ⟨3,![12,22,23,28,18],![30,32,44,58,46]⟩
def data95 : PartitionData E W := ⟨7,![cycle95_0,cycle95_1,cycle95_2,cycle95_3,cycle95_4,cycle95_5,cycle95_6]⟩
lemma valid95 : data95.Valid src95 dst95 Finset.univ := by decide +kernel
lemma src_eq95 : src95 = src (unkey (representativeKey 95)) := by decide +kernel
lemma dst_eq95 : dst95 = dst (unkey (representativeKey 95)) := by decide +kernel
lemma certificate95 : Certificate 95 := by
  refine ⟨data95,?_,?_⟩
  · rw [← src_eq95,← dst_eq95]
    exact valid95
  · decide +kernel

def src96 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,44,30,46,8,20,32,44,58,10,34,22,58,46]
def dst96 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,44,30,46,6,20,32,44,58,8,34,22,58,46,10]
def cycle96_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle96_1 : CycleData E W := ⟨4,![1,2,20,21,13,14],![4,6,8,20,32,34]⟩
def cycle96_2 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle96_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,20]⟩
def cycle96_4 : CycleData E W := ⟨3,![15,6,11,18,19],![6,18,16,30,46]⟩
def cycle96_5 : CycleData E W := ⟨2,![7,27,23,16],![18,22,58,44]⟩
def cycle96_6 : CycleData E W := ⟨1,![12,22,17],![30,32,44]⟩
def data96 : PartitionData E W := ⟨7,![cycle96_0,cycle96_1,cycle96_2,cycle96_3,cycle96_4,cycle96_5,cycle96_6]⟩
lemma valid96 : data96.Valid src96 dst96 Finset.univ := by decide +kernel
lemma src_eq96 : src96 = src (unkey (representativeKey 96)) := by decide +kernel
lemma dst_eq96 : dst96 = dst (unkey (representativeKey 96)) := by decide +kernel
lemma certificate96 : Certificate 96 := by
  refine ⟨data96,?_,?_⟩
  · rw [← src_eq96,← dst_eq96]
    exact valid96
  · decide +kernel

def src97 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,44,30,46,8,20,32,44,58,10,34,58,22,46]
def dst97 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,44,30,46,6,20,32,44,58,8,34,58,22,46,10]
def cycle97_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle97_1 : CycleData E W := ⟨4,![1,2,20,21,13,14],![4,6,8,20,32,34]⟩
def cycle97_2 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle97_3 : CycleData E W := ⟨3,![4,29,28,8,9],![2,10,46,22,20]⟩
def cycle97_4 : CycleData E W := ⟨3,![15,6,11,18,19],![6,18,16,30,46]⟩
def cycle97_5 : CycleData E W := ⟨2,![7,27,23,16],![18,22,58,44]⟩
def cycle97_6 : CycleData E W := ⟨1,![12,22,17],![30,32,44]⟩
def data97 : PartitionData E W := ⟨7,![cycle97_0,cycle97_1,cycle97_2,cycle97_3,cycle97_4,cycle97_5,cycle97_6]⟩
lemma valid97 : data97.Valid src97 dst97 Finset.univ := by decide +kernel
lemma src_eq97 : src97 = src (unkey (representativeKey 97)) := by decide +kernel
lemma dst_eq97 : dst97 = dst (unkey (representativeKey 97)) := by decide +kernel
lemma certificate97 : Certificate 97 := by
  refine ⟨data97,?_,?_⟩
  · rw [← src_eq97,← dst_eq97]
    exact valid97
  · decide +kernel

def src98 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,44,30,46,8,20,32,44,58,10,46,22,34,58]
def dst98 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,44,30,46,6,20,32,44,58,8,46,22,34,58,10]
def cycle98_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle98_1 : CycleData E W := ⟨4,![1,2,20,21,13,14],![4,6,8,20,32,34]⟩
def cycle98_2 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle98_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,46,22,20]⟩
def cycle98_4 : CycleData E W := ⟨3,![15,6,11,18,19],![6,18,16,30,46]⟩
def cycle98_5 : CycleData E W := ⟨3,![7,27,28,23,16],![18,22,34,58,44]⟩
def cycle98_6 : CycleData E W := ⟨1,![12,22,17],![30,32,44]⟩
def data98 : PartitionData E W := ⟨7,![cycle98_0,cycle98_1,cycle98_2,cycle98_3,cycle98_4,cycle98_5,cycle98_6]⟩
lemma valid98 : data98.Valid src98 dst98 Finset.univ := by decide +kernel
lemma src_eq98 : src98 = src (unkey (representativeKey 98)) := by decide +kernel
lemma dst_eq98 : dst98 = dst (unkey (representativeKey 98)) := by decide +kernel
lemma certificate98 : Certificate 98 := by
  refine ⟨data98,?_,?_⟩
  · rw [← src_eq98,← dst_eq98]
    exact valid98
  · decide +kernel

def src99 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,16,30,32,34,6,18,44,30,46,8,20,32,58,44,10,34,22,46,58]
def dst99 : E → W := ![4,6,8,10,2,16,18,22,20,2,16,30,32,34,4,18,44,30,46,6,20,32,58,44,8,34,22,46,58,10]
def cycle99_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle99_1 : CycleData E W := ⟨4,![1,2,20,21,13,14],![4,6,8,20,32,34]⟩
def cycle99_2 : CycleData E W := ⟨2,![3,29,23,24],![8,10,58,44]⟩
def cycle99_3 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,34,22,20]⟩
def cycle99_4 : CycleData E W := ⟨2,![6,16,17,11],![16,18,44,30]⟩
def cycle99_5 : CycleData E W := ⟨2,![15,7,27,19],![6,18,22,46]⟩
def cycle99_6 : CycleData E W := ⟨2,![12,22,28,18],![30,32,58,46]⟩
def data99 : PartitionData E W := ⟨7,![cycle99_0,cycle99_1,cycle99_2,cycle99_3,cycle99_4,cycle99_5,cycle99_6]⟩
lemma valid99 : data99.Valid src99 dst99 Finset.univ := by decide +kernel
lemma src_eq99 : src99 = src (unkey (representativeKey 99)) := by decide +kernel
lemma dst_eq99 : dst99 = dst (unkey (representativeKey 99)) := by decide +kernel
lemma certificate99 : Certificate 99 := by
  refine ⟨data99,?_,?_⟩
  · rw [← src_eq99,← dst_eq99]
    exact valid99
  · decide +kernel
#print axioms certificate99
end Erdos184Work.SixRepresentativeCertificates0

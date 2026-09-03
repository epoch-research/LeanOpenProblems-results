import Submission.SixRepresentativeCertificates1Base
namespace Erdos184Work.SixRepresentativeCertificates1
open PureSixRowModel1 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src100 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,30,46,8,20,58,44,32,10,34,22,58,46]
def dst100 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle100_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle100_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle100_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle100_3 : CycleData E W := ⟨3,![5,31,20,14,6],![2,10,46,30,16]⟩
def cycle100_4 : CycleData E W := ⟨3,![7,23,29,28,15],![16,20,58,22,34]⟩
def cycle100_5 : CycleData E W := ⟨1,![13,25,19],![30,32,44]⟩
def cycle100_6 : CycleData E W := ⟨3,![17,18,24,30,21],![6,18,44,58,46]⟩
def data100 : PartitionData E W := ⟨7,![cycle100_0,cycle100_1,cycle100_2,cycle100_3,cycle100_4,cycle100_5,cycle100_6]⟩
lemma valid100 : data100.Valid src100 dst100 Finset.univ := by decide +kernel
lemma src_eq100 : src100 = src (unkey (representativeKey 100)) := by decide +kernel
lemma dst_eq100 : dst100 = dst (unkey (representativeKey 100)) := by decide +kernel
lemma certificate100 : Certificate 100 := by
  refine ⟨data100,?_,?_⟩
  · rw [← src_eq100,← dst_eq100]
    exact valid100
  · decide +kernel

def src101 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,30,46,8,20,58,44,32,10,34,58,22,46]
def dst101 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,30,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle101_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle101_1 : CycleData E W := ⟨2,![2,21,30,9],![3,6,46,22]⟩
def cycle101_2 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle101_3 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle101_4 : CycleData E W := ⟨4,![12,26,22,23,28,16],![4,32,8,20,58,34]⟩
def cycle101_5 : CycleData E W := ⟨1,![13,25,19],![30,32,44]⟩
def cycle101_6 : CycleData E W := ⟨3,![27,15,14,20,31],![10,34,16,30,46]⟩
def data101 : PartitionData E W := ⟨7,![cycle101_0,cycle101_1,cycle101_2,cycle101_3,cycle101_4,cycle101_5,cycle101_6]⟩
lemma valid101 : data101.Valid src101 dst101 Finset.univ := by decide +kernel
lemma src_eq101 : src101 = src (unkey (representativeKey 101)) := by decide +kernel
lemma dst_eq101 : dst101 = dst (unkey (representativeKey 101)) := by decide +kernel
lemma certificate101 : Certificate 101 := by
  refine ⟨data101,?_,?_⟩
  · rw [← src_eq101,← dst_eq101]
    exact valid101
  · decide +kernel

def src102 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,30,46,8,20,58,44,32,10,46,34,22,58]
def dst102 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,30,46,6,20,58,44,32,8,46,34,22,58,10]
def cycle102_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle102_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle102_2 : CycleData E W := ⟨2,![3,4,27,21],![6,8,10,46]⟩
def cycle102_3 : CycleData E W := ⟨3,![5,31,24,18,11],![2,10,58,44,18]⟩
def cycle102_4 : CycleData E W := ⟨5,![12,26,22,23,30,29,16],![4,32,8,20,58,22,34]⟩
def cycle102_5 : CycleData E W := ⟨1,![13,25,19],![30,32,44]⟩
def cycle102_6 : CycleData E W := ⟨2,![14,20,28,15],![16,30,46,34]⟩
def data102 : PartitionData E W := ⟨7,![cycle102_0,cycle102_1,cycle102_2,cycle102_3,cycle102_4,cycle102_5,cycle102_6]⟩
lemma valid102 : data102.Valid src102 dst102 Finset.univ := by decide +kernel
lemma src_eq102 : src102 = src (unkey (representativeKey 102)) := by decide +kernel
lemma dst_eq102 : dst102 = dst (unkey (representativeKey 102)) := by decide +kernel
lemma certificate102 : Certificate 102 := by
  refine ⟨data102,?_,?_⟩
  · rw [← src_eq102,← dst_eq102]
    exact valid102
  · decide +kernel

def src103 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,44,58,32,10,22,58,34,46]
def dst103 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,44,58,32,8,22,58,34,46,10]
def cycle103_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle103_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle103_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle103_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle103_4 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle103_5 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def cycle103_6 : CycleData E W := ⟨3,![27,28,24,19,31],![10,22,58,44,46]⟩
def data103 : PartitionData E W := ⟨7,![cycle103_0,cycle103_1,cycle103_2,cycle103_3,cycle103_4,cycle103_5,cycle103_6]⟩
lemma valid103 : data103.Valid src103 dst103 Finset.univ := by decide +kernel
lemma src_eq103 : src103 = src (unkey (representativeKey 103)) := by decide +kernel
lemma dst_eq103 : dst103 = dst (unkey (representativeKey 103)) := by decide +kernel
lemma certificate103 : Certificate 103 := by
  refine ⟨data103,?_,?_⟩
  · rw [← src_eq103,← dst_eq103]
    exact valid103
  · decide +kernel

def src104 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,44,58,32,10,34,22,58,46]
def dst104 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,44,58,32,8,34,22,58,46,10]
def cycle104_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle104_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle104_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle104_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle104_4 : CycleData E W := ⟨3,![12,25,29,28,16],![4,32,58,22,34]⟩
def cycle104_5 : CycleData E W := ⟨3,![27,15,14,20,31],![10,34,16,30,46]⟩
def cycle104_6 : CycleData E W := ⟨1,![19,30,24],![44,46,58]⟩
def data104 : PartitionData E W := ⟨7,![cycle104_0,cycle104_1,cycle104_2,cycle104_3,cycle104_4,cycle104_5,cycle104_6]⟩
lemma valid104 : data104.Valid src104 dst104 Finset.univ := by decide +kernel
lemma src_eq104 : src104 = src (unkey (representativeKey 104)) := by decide +kernel
lemma dst_eq104 : dst104 = dst (unkey (representativeKey 104)) := by decide +kernel
lemma certificate104 : Certificate 104 := by
  refine ⟨data104,?_,?_⟩
  · rw [← src_eq104,← dst_eq104]
    exact valid104
  · decide +kernel

def src105 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,44,58,32,10,34,58,22,46]
def dst105 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,44,58,32,8,34,58,22,46,10]
def cycle105_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle105_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle105_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle105_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle105_4 : CycleData E W := ⟨2,![12,25,28,16],![4,32,58,34]⟩
def cycle105_5 : CycleData E W := ⟨3,![27,15,14,20,31],![10,34,16,30,46]⟩
def cycle105_6 : CycleData E W := ⟨2,![29,24,19,30],![22,58,44,46]⟩
def data105 : PartitionData E W := ⟨7,![cycle105_0,cycle105_1,cycle105_2,cycle105_3,cycle105_4,cycle105_5,cycle105_6]⟩
lemma valid105 : data105.Valid src105 dst105 Finset.univ := by decide +kernel
lemma src_eq105 : src105 = src (unkey (representativeKey 105)) := by decide +kernel
lemma dst_eq105 : dst105 = dst (unkey (representativeKey 105)) := by decide +kernel
lemma certificate105 : Certificate 105 := by
  refine ⟨data105,?_,?_⟩
  · rw [← src_eq105,← dst_eq105]
    exact valid105
  · decide +kernel

def src106 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,44,58,32,10,46,34,22,58]
def dst106 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,44,58,32,8,46,34,22,58,10]
def cycle106_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle106_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle106_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle106_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle106_4 : CycleData E W := ⟨3,![12,25,30,29,16],![4,32,58,22,34]⟩
def cycle106_5 : CycleData E W := ⟨2,![14,20,28,15],![16,30,46,34]⟩
def cycle106_6 : CycleData E W := ⟨2,![27,19,24,31],![10,46,44,58]⟩
def data106 : PartitionData E W := ⟨7,![cycle106_0,cycle106_1,cycle106_2,cycle106_3,cycle106_4,cycle106_5,cycle106_6]⟩
lemma valid106 : data106.Valid src106 dst106 Finset.univ := by decide +kernel
lemma src_eq106 : src106 = src (unkey (representativeKey 106)) := by decide +kernel
lemma dst_eq106 : dst106 = dst (unkey (representativeKey 106)) := by decide +kernel
lemma certificate106 : Certificate 106 := by
  refine ⟨data106,?_,?_⟩
  · rw [← src_eq106,← dst_eq106]
    exact valid106
  · decide +kernel

def src107 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,58,44,32,10,22,58,34,46]
def dst107 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,58,44,32,8,22,58,34,46,10]
def cycle107_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle107_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle107_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle107_3 : CycleData E W := ⟨3,![4,27,28,23,22],![8,10,22,58,20]⟩
def cycle107_4 : CycleData E W := ⟨3,![5,31,19,18,11],![2,10,46,44,18]⟩
def cycle107_5 : CycleData E W := ⟨3,![12,25,24,29,16],![4,32,44,58,34]⟩
def cycle107_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data107 : PartitionData E W := ⟨7,![cycle107_0,cycle107_1,cycle107_2,cycle107_3,cycle107_4,cycle107_5,cycle107_6]⟩
lemma valid107 : data107.Valid src107 dst107 Finset.univ := by decide +kernel
lemma src_eq107 : src107 = src (unkey (representativeKey 107)) := by decide +kernel
lemma dst_eq107 : dst107 = dst (unkey (representativeKey 107)) := by decide +kernel
lemma certificate107 : Certificate 107 := by
  refine ⟨data107,?_,?_⟩
  · rw [← src_eq107,← dst_eq107]
    exact valid107
  · decide +kernel

def src108 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,58,44,32,10,34,22,58,46]
def dst108 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,58,44,32,8,34,22,58,46,10]
def cycle108_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle108_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle108_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle108_3 : CycleData E W := ⟨3,![5,31,20,14,6],![2,10,46,30,16]⟩
def cycle108_4 : CycleData E W := ⟨3,![7,23,29,28,15],![16,20,58,22,34]⟩
def cycle108_5 : CycleData E W := ⟨3,![17,18,25,13,21],![6,18,44,32,30]⟩
def cycle108_6 : CycleData E W := ⟨1,![19,30,24],![44,46,58]⟩
def data108 : PartitionData E W := ⟨7,![cycle108_0,cycle108_1,cycle108_2,cycle108_3,cycle108_4,cycle108_5,cycle108_6]⟩
lemma valid108 : data108.Valid src108 dst108 Finset.univ := by decide +kernel
lemma src_eq108 : src108 = src (unkey (representativeKey 108)) := by decide +kernel
lemma dst_eq108 : dst108 = dst (unkey (representativeKey 108)) := by decide +kernel
lemma certificate108 : Certificate 108 := by
  refine ⟨data108,?_,?_⟩
  · rw [← src_eq108,← dst_eq108]
    exact valid108
  · decide +kernel

def src109 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,58,44,32,10,34,58,22,46]
def dst109 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,58,44,32,8,34,58,22,46,10]
def cycle109_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle109_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle109_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle109_3 : CycleData E W := ⟨3,![5,31,20,14,6],![2,10,46,30,16]⟩
def cycle109_4 : CycleData E W := ⟨2,![7,23,28,15],![16,20,58,34]⟩
def cycle109_5 : CycleData E W := ⟨3,![17,18,25,13,21],![6,18,44,32,30]⟩
def cycle109_6 : CycleData E W := ⟨2,![29,24,19,30],![22,58,44,46]⟩
def data109 : PartitionData E W := ⟨7,![cycle109_0,cycle109_1,cycle109_2,cycle109_3,cycle109_4,cycle109_5,cycle109_6]⟩
lemma valid109 : data109.Valid src109 dst109 Finset.univ := by decide +kernel
lemma src_eq109 : src109 = src (unkey (representativeKey 109)) := by decide +kernel
lemma dst_eq109 : dst109 = dst (unkey (representativeKey 109)) := by decide +kernel
lemma certificate109 : Certificate 109 := by
  refine ⟨data109,?_,?_⟩
  · rw [← src_eq109,← dst_eq109]
    exact valid109
  · decide +kernel

def src110 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,46,30,8,20,58,44,32,10,46,34,22,58]
def dst110 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,46,30,6,20,58,44,32,8,46,34,22,58,10]
def cycle110_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle110_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,22]⟩
def cycle110_2 : CycleData E W := ⟨2,![3,26,13,21],![6,8,32,30]⟩
def cycle110_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle110_4 : CycleData E W := ⟨3,![5,27,19,18,11],![2,10,46,44,18]⟩
def cycle110_5 : CycleData E W := ⟨4,![12,25,24,30,29,16],![4,32,44,58,22,34]⟩
def cycle110_6 : CycleData E W := ⟨2,![14,20,28,15],![16,30,46,34]⟩
def data110 : PartitionData E W := ⟨7,![cycle110_0,cycle110_1,cycle110_2,cycle110_3,cycle110_4,cycle110_5,cycle110_6]⟩
lemma valid110 : data110.Valid src110 dst110 Finset.univ := by decide +kernel
lemma src_eq110 : src110 = src (unkey (representativeKey 110)) := by decide +kernel
lemma dst_eq110 : dst110 = dst (unkey (representativeKey 110)) := by decide +kernel
lemma certificate110 : Certificate 110 := by
  refine ⟨data110,?_,?_⟩
  · rw [← src_eq110,← dst_eq110]
    exact valid110
  · decide +kernel

def src111 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,44,58,32,10,22,58,34,46]
def dst111 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,44,58,32,8,22,58,34,46,10]
def cycle111_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle111_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle111_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle111_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle111_4 : CycleData E W := ⟨3,![7,23,19,18,14],![16,20,44,18,30]⟩
def cycle111_5 : CycleData E W := ⟨4,![8,22,26,25,28,9],![3,20,8,32,58,22]⟩
def cycle111_6 : CycleData E W := ⟨2,![29,24,20,30],![34,58,44,46]⟩
def data111 : PartitionData E W := ⟨7,![cycle111_0,cycle111_1,cycle111_2,cycle111_3,cycle111_4,cycle111_5,cycle111_6]⟩
lemma valid111 : data111.Valid src111 dst111 Finset.univ := by decide +kernel
lemma src_eq111 : src111 = src (unkey (representativeKey 111)) := by decide +kernel
lemma dst_eq111 : dst111 = dst (unkey (representativeKey 111)) := by decide +kernel
lemma certificate111 : Certificate 111 := by
  refine ⟨data111,?_,?_⟩
  · rw [← src_eq111,← dst_eq111]
    exact valid111
  · decide +kernel

def src112 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,44,58,32,10,22,58,46,34]
def dst112 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,44,58,32,8,22,58,46,34,10]
def cycle112_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle112_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle112_2 : CycleData E W := ⟨3,![4,27,28,25,26],![8,10,22,58,32]⟩
def cycle112_3 : CycleData E W := ⟨2,![5,31,15,6],![2,10,34,16]⟩
def cycle112_4 : CycleData E W := ⟨3,![7,23,19,18,14],![16,20,44,18,30]⟩
def cycle112_5 : CycleData E W := ⟨4,![12,13,17,21,30,16],![4,32,30,6,46,34]⟩
def cycle112_6 : CycleData E W := ⟨1,![20,29,24],![44,46,58]⟩
def data112 : PartitionData E W := ⟨7,![cycle112_0,cycle112_1,cycle112_2,cycle112_3,cycle112_4,cycle112_5,cycle112_6]⟩
lemma valid112 : data112.Valid src112 dst112 Finset.univ := by decide +kernel
lemma src_eq112 : src112 = src (unkey (representativeKey 112)) := by decide +kernel
lemma dst_eq112 : dst112 = dst (unkey (representativeKey 112)) := by decide +kernel
lemma certificate112 : Certificate 112 := by
  refine ⟨data112,?_,?_⟩
  · rw [← src_eq112,← dst_eq112]
    exact valid112
  · decide +kernel

def src113 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,44,58,32,10,34,46,22,58]
def dst113 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle113_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle113_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle113_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle113_3 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle113_4 : CycleData E W := ⟨3,![7,23,19,18,14],![16,20,44,18,30]⟩
def cycle113_5 : CycleData E W := ⟨4,![12,13,17,21,28,16],![4,32,30,6,46,34]⟩
def cycle113_6 : CycleData E W := ⟨2,![29,20,24,30],![22,46,44,58]⟩
def data113 : PartitionData E W := ⟨7,![cycle113_0,cycle113_1,cycle113_2,cycle113_3,cycle113_4,cycle113_5,cycle113_6]⟩
lemma valid113 : data113.Valid src113 dst113 Finset.univ := by decide +kernel
lemma src_eq113 : src113 = src (unkey (representativeKey 113)) := by decide +kernel
lemma dst_eq113 : dst113 = dst (unkey (representativeKey 113)) := by decide +kernel
lemma certificate113 : Certificate 113 := by
  refine ⟨data113,?_,?_⟩
  · rw [← src_eq113,← dst_eq113]
    exact valid113
  · decide +kernel

def src114 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,44,58,32,10,46,34,22,58]
def dst114 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle114_0 : CycleData E W := ⟨3,![0,12,13,14,6],![2,4,32,30,16]⟩
def cycle114_1 : CycleData E W := ⟨2,![1,16,29,9],![3,4,34,22]⟩
def cycle114_2 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle114_3 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle114_4 : CycleData E W := ⟨4,![5,27,21,17,18,11],![2,10,46,6,30,18]⟩
def cycle114_5 : CycleData E W := ⟨3,![7,23,20,28,15],![16,20,44,46,34]⟩
def cycle114_6 : CycleData E W := ⟨2,![10,30,24,19],![18,22,58,44]⟩
def data114 : PartitionData E W := ⟨7,![cycle114_0,cycle114_1,cycle114_2,cycle114_3,cycle114_4,cycle114_5,cycle114_6]⟩
lemma valid114 : data114.Valid src114 dst114 Finset.univ := by decide +kernel
lemma src_eq114 : src114 = src (unkey (representativeKey 114)) := by decide +kernel
lemma dst_eq114 : dst114 = dst (unkey (representativeKey 114)) := by decide +kernel
lemma certificate114 : Certificate 114 := by
  refine ⟨data114,?_,?_⟩
  · rw [← src_eq114,← dst_eq114]
    exact valid114
  · decide +kernel

def src115 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,32,44,10,22,58,34,46]
def dst115 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,32,44,8,22,58,34,46,10]
def cycle115_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle115_1 : CycleData E W := ⟨4,![2,3,22,23,28,9],![3,6,8,20,58,22]⟩
def cycle115_2 : CycleData E W := ⟨2,![4,31,20,26],![8,10,46,44]⟩
def cycle115_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle115_4 : CycleData E W := ⟨2,![12,24,29,16],![4,32,58,34]⟩
def cycle115_5 : CycleData E W := ⟨2,![18,13,25,19],![18,30,32,44]⟩
def cycle115_6 : CycleData E W := ⟨3,![17,14,15,30,21],![6,30,16,34,46]⟩
def data115 : PartitionData E W := ⟨7,![cycle115_0,cycle115_1,cycle115_2,cycle115_3,cycle115_4,cycle115_5,cycle115_6]⟩
lemma valid115 : data115.Valid src115 dst115 Finset.univ := by decide +kernel
lemma src_eq115 : src115 = src (unkey (representativeKey 115)) := by decide +kernel
lemma dst_eq115 : dst115 = dst (unkey (representativeKey 115)) := by decide +kernel
lemma certificate115 : Certificate 115 := by
  refine ⟨data115,?_,?_⟩
  · rw [← src_eq115,← dst_eq115]
    exact valid115
  · decide +kernel

def src116 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,32,44,10,22,58,46,34]
def dst116 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,32,44,8,22,58,46,34,10]
def cycle116_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle116_1 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,20]⟩
def cycle116_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle116_3 : CycleData E W := ⟨3,![4,27,28,23,22],![8,10,22,58,20]⟩
def cycle116_4 : CycleData E W := ⟨2,![5,31,15,6],![2,10,34,16]⟩
def cycle116_5 : CycleData E W := ⟨3,![12,24,29,30,16],![4,32,58,46,34]⟩
def cycle116_6 : CycleData E W := ⟨2,![18,13,25,19],![18,30,32,44]⟩
def data116 : PartitionData E W := ⟨7,![cycle116_0,cycle116_1,cycle116_2,cycle116_3,cycle116_4,cycle116_5,cycle116_6]⟩
lemma valid116 : data116.Valid src116 dst116 Finset.univ := by decide +kernel
lemma src_eq116 : src116 = src (unkey (representativeKey 116)) := by decide +kernel
lemma dst_eq116 : dst116 = dst (unkey (representativeKey 116)) := by decide +kernel
lemma certificate116 : Certificate 116 := by
  refine ⟨data116,?_,?_⟩
  · rw [← src_eq116,← dst_eq116]
    exact valid116
  · decide +kernel

def src117 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,32,44,10,34,46,22,58]
def dst117 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,32,44,8,34,46,22,58,10]
def cycle117_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle117_1 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,20]⟩
def cycle117_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle117_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle117_4 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle117_5 : CycleData E W := ⟨4,![12,24,30,29,28,16],![4,32,58,22,46,34]⟩
def cycle117_6 : CycleData E W := ⟨2,![18,13,25,19],![18,30,32,44]⟩
def data117 : PartitionData E W := ⟨7,![cycle117_0,cycle117_1,cycle117_2,cycle117_3,cycle117_4,cycle117_5,cycle117_6]⟩
lemma valid117 : data117.Valid src117 dst117 Finset.univ := by decide +kernel
lemma src_eq117 : src117 = src (unkey (representativeKey 117)) := by decide +kernel
lemma dst_eq117 : dst117 = dst (unkey (representativeKey 117)) := by decide +kernel
lemma certificate117 : Certificate 117 := by
  refine ⟨data117,?_,?_⟩
  · rw [← src_eq117,← dst_eq117]
    exact valid117
  · decide +kernel

def src118 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,32,44,10,46,34,22,58]
def dst118 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,32,44,8,46,34,22,58,10]
def cycle118_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle118_1 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,20]⟩
def cycle118_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle118_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle118_4 : CycleData E W := ⟨3,![5,27,28,15,6],![2,10,46,34,16]⟩
def cycle118_5 : CycleData E W := ⟨3,![12,24,30,29,16],![4,32,58,22,34]⟩
def cycle118_6 : CycleData E W := ⟨2,![18,13,25,19],![18,30,32,44]⟩
def data118 : PartitionData E W := ⟨7,![cycle118_0,cycle118_1,cycle118_2,cycle118_3,cycle118_4,cycle118_5,cycle118_6]⟩
lemma valid118 : data118.Valid src118 dst118 Finset.univ := by decide +kernel
lemma src_eq118 : src118 = src (unkey (representativeKey 118)) := by decide +kernel
lemma dst_eq118 : dst118 = dst (unkey (representativeKey 118)) := by decide +kernel
lemma certificate118 : Certificate 118 := by
  refine ⟨data118,?_,?_⟩
  · rw [← src_eq118,← dst_eq118]
    exact valid118
  · decide +kernel

def src119 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,44,32,10,22,58,34,46]
def dst119 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle119_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle119_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle119_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle119_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle119_4 : CycleData E W := ⟨5,![22,7,14,18,19,25,26],![8,20,16,30,18,44,32]⟩
def cycle119_5 : CycleData E W := ⟨2,![8,23,28,9],![3,20,58,22]⟩
def cycle119_6 : CycleData E W := ⟨2,![29,24,20,30],![34,58,44,46]⟩
def data119 : PartitionData E W := ⟨7,![cycle119_0,cycle119_1,cycle119_2,cycle119_3,cycle119_4,cycle119_5,cycle119_6]⟩
lemma valid119 : data119.Valid src119 dst119 Finset.univ := by decide +kernel
lemma src_eq119 : src119 = src (unkey (representativeKey 119)) := by decide +kernel
lemma dst_eq119 : dst119 = dst (unkey (representativeKey 119)) := by decide +kernel
lemma certificate119 : Certificate 119 := by
  refine ⟨data119,?_,?_⟩
  · rw [← src_eq119,← dst_eq119]
    exact valid119
  · decide +kernel

def src120 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,20,58,44,32,10,46,34,22,58]
def dst120 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,20,58,44,32,8,46,34,22,58,10]
def cycle120_0 : CycleData E W := ⟨3,![0,12,13,18,11],![2,4,32,30,18]⟩
def cycle120_1 : CycleData E W := ⟨2,![1,16,29,9],![3,4,34,22]⟩
def cycle120_2 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,20]⟩
def cycle120_3 : CycleData E W := ⟨3,![3,26,25,20,21],![6,8,32,44,46]⟩
def cycle120_4 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle120_5 : CycleData E W := ⟨3,![5,27,28,15,6],![2,10,46,34,16]⟩
def cycle120_6 : CycleData E W := ⟨2,![10,30,24,19],![18,22,58,44]⟩
def data120 : PartitionData E W := ⟨7,![cycle120_0,cycle120_1,cycle120_2,cycle120_3,cycle120_4,cycle120_5,cycle120_6]⟩
lemma valid120 : data120.Valid src120 dst120 Finset.univ := by decide +kernel
lemma src_eq120 : src120 = src (unkey (representativeKey 120)) := by decide +kernel
lemma dst_eq120 : dst120 = dst (unkey (representativeKey 120)) := by decide +kernel
lemma certificate120 : Certificate 120 := by
  refine ⟨data120,?_,?_⟩
  · rw [← src_eq120,← dst_eq120]
    exact valid120
  · decide +kernel

def src121 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,32,58,20,44,10,22,58,34,46]
def dst121 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,32,58,20,44,8,22,58,34,46,10]
def cycle121_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle121_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle121_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle121_3 : CycleData E W := ⟨4,![4,31,30,29,23,22],![8,10,46,34,58,32]⟩
def cycle121_4 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle121_5 : CycleData E W := ⟨3,![7,25,19,18,14],![16,20,44,18,30]⟩
def cycle121_6 : CycleData E W := ⟨2,![8,24,28,9],![3,20,58,22]⟩
def data121 : PartitionData E W := ⟨7,![cycle121_0,cycle121_1,cycle121_2,cycle121_3,cycle121_4,cycle121_5,cycle121_6]⟩
lemma valid121 : data121.Valid src121 dst121 Finset.univ := by decide +kernel
lemma src_eq121 : src121 = src (unkey (representativeKey 121)) := by decide +kernel
lemma dst_eq121 : dst121 = dst (unkey (representativeKey 121)) := by decide +kernel
lemma certificate121 : Certificate 121 := by
  refine ⟨data121,?_,?_⟩
  · rw [← src_eq121,← dst_eq121]
    exact valid121
  · decide +kernel

def src122 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,32,58,20,44,10,22,58,46,34]
def dst122 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,32,58,20,44,8,22,58,46,34,10]
def cycle122_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle122_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle122_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle122_3 : CycleData E W := ⟨4,![4,31,30,29,23,22],![8,10,34,46,58,32]⟩
def cycle122_4 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle122_5 : CycleData E W := ⟨3,![7,25,19,18,14],![16,20,44,18,30]⟩
def cycle122_6 : CycleData E W := ⟨2,![8,24,28,9],![3,20,58,22]⟩
def data122 : PartitionData E W := ⟨7,![cycle122_0,cycle122_1,cycle122_2,cycle122_3,cycle122_4,cycle122_5,cycle122_6]⟩
lemma valid122 : data122.Valid src122 dst122 Finset.univ := by decide +kernel
lemma src_eq122 : src122 = src (unkey (representativeKey 122)) := by decide +kernel
lemma dst_eq122 : dst122 = dst (unkey (representativeKey 122)) := by decide +kernel
lemma certificate122 : Certificate 122 := by
  refine ⟨data122,?_,?_⟩
  · rw [← src_eq122,← dst_eq122]
    exact valid122
  · decide +kernel

def src123 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,32,58,20,44,10,34,46,22,58]
def dst123 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,32,58,20,44,8,34,46,22,58,10]
def cycle123_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle123_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle123_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle123_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,32]⟩
def cycle123_4 : CycleData E W := ⟨4,![5,27,28,29,10,11],![2,10,34,46,22,18]⟩
def cycle123_5 : CycleData E W := ⟨3,![7,25,19,18,14],![16,20,44,18,30]⟩
def cycle123_6 : CycleData E W := ⟨2,![8,24,30,9],![3,20,58,22]⟩
def data123 : PartitionData E W := ⟨7,![cycle123_0,cycle123_1,cycle123_2,cycle123_3,cycle123_4,cycle123_5,cycle123_6]⟩
lemma valid123 : data123.Valid src123 dst123 Finset.univ := by decide +kernel
lemma src_eq123 : src123 = src (unkey (representativeKey 123)) := by decide +kernel
lemma dst_eq123 : dst123 = dst (unkey (representativeKey 123)) := by decide +kernel
lemma certificate123 : Certificate 123 := by
  refine ⟨data123,?_,?_⟩
  · rw [← src_eq123,← dst_eq123]
    exact valid123
  · decide +kernel

def src124 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,18,44,46,8,32,58,20,44,10,46,34,22,58]
def dst124 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,18,44,46,6,32,58,20,44,8,46,34,22,58,10]
def cycle124_0 : CycleData E W := ⟨2,![0,16,15,6],![2,4,34,16]⟩
def cycle124_1 : CycleData E W := ⟨3,![1,12,13,17,2],![3,4,32,30,6]⟩
def cycle124_2 : CycleData E W := ⟨2,![3,26,20,21],![6,8,44,46]⟩
def cycle124_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,32]⟩
def cycle124_4 : CycleData E W := ⟨4,![5,27,28,29,10,11],![2,10,46,34,22,18]⟩
def cycle124_5 : CycleData E W := ⟨3,![7,25,19,18,14],![16,20,44,18,30]⟩
def cycle124_6 : CycleData E W := ⟨2,![8,24,30,9],![3,20,58,22]⟩
def data124 : PartitionData E W := ⟨7,![cycle124_0,cycle124_1,cycle124_2,cycle124_3,cycle124_4,cycle124_5,cycle124_6]⟩
lemma valid124 : data124.Valid src124 dst124 Finset.univ := by decide +kernel
lemma src_eq124 : src124 = src (unkey (representativeKey 124)) := by decide +kernel
lemma dst_eq124 : dst124 = dst (unkey (representativeKey 124)) := by decide +kernel
lemma certificate124 : Certificate 124 := by
  refine ⟨data124,?_,?_⟩
  · rw [← src_eq124,← dst_eq124]
    exact valid124
  · decide +kernel

def src125 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,44,18,46,8,20,44,58,32,10,22,58,34,46]
def dst125 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,44,18,46,6,20,44,58,32,8,22,58,34,46,10]
def cycle125_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle125_1 : CycleData E W := ⟨3,![2,3,4,27,9],![3,6,8,10,22]⟩
def cycle125_2 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle125_3 : CycleData E W := ⟨2,![10,28,24,19],![18,22,58,44]⟩
def cycle125_4 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle125_5 : CycleData E W := ⟨3,![22,23,18,13,26],![8,20,44,30,32]⟩
def cycle125_6 : CycleData E W := ⟨3,![17,14,15,30,21],![6,30,16,34,46]⟩
def data125 : PartitionData E W := ⟨7,![cycle125_0,cycle125_1,cycle125_2,cycle125_3,cycle125_4,cycle125_5,cycle125_6]⟩
lemma valid125 : data125.Valid src125 dst125 Finset.univ := by decide +kernel
lemma src_eq125 : src125 = src (unkey (representativeKey 125)) := by decide +kernel
lemma dst_eq125 : dst125 = dst (unkey (representativeKey 125)) := by decide +kernel
lemma certificate125 : Certificate 125 := by
  refine ⟨data125,?_,?_⟩
  · rw [← src_eq125,← dst_eq125]
    exact valid125
  · decide +kernel

def src126 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,44,18,46,8,20,44,58,32,10,22,58,46,34]
def dst126 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,44,18,46,6,20,44,58,32,8,22,58,46,34,10]
def cycle126_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle126_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle126_2 : CycleData E W := ⟨3,![4,27,28,25,26],![8,10,22,58,32]⟩
def cycle126_3 : CycleData E W := ⟨2,![5,31,15,6],![2,10,34,16]⟩
def cycle126_4 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle126_5 : CycleData E W := ⟨4,![12,13,17,21,30,16],![4,32,30,6,46,34]⟩
def cycle126_6 : CycleData E W := ⟨2,![19,24,29,20],![18,44,58,46]⟩
def data126 : PartitionData E W := ⟨7,![cycle126_0,cycle126_1,cycle126_2,cycle126_3,cycle126_4,cycle126_5,cycle126_6]⟩
lemma valid126 : data126.Valid src126 dst126 Finset.univ := by decide +kernel
lemma src_eq126 : src126 = src (unkey (representativeKey 126)) := by decide +kernel
lemma dst_eq126 : dst126 = dst (unkey (representativeKey 126)) := by decide +kernel
lemma certificate126 : Certificate 126 := by
  refine ⟨data126,?_,?_⟩
  · rw [← src_eq126,← dst_eq126]
    exact valid126
  · decide +kernel

def src127 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,44,18,46,8,20,58,44,32,10,22,58,34,46]
def dst127 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,44,18,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle127_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle127_1 : CycleData E W := ⟨3,![2,3,4,27,9],![3,6,8,10,22]⟩
def cycle127_2 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle127_3 : CycleData E W := ⟨2,![10,28,24,19],![18,22,58,44]⟩
def cycle127_4 : CycleData E W := ⟨4,![12,26,22,23,29,16],![4,32,8,20,58,34]⟩
def cycle127_5 : CycleData E W := ⟨1,![13,25,18],![30,32,44]⟩
def cycle127_6 : CycleData E W := ⟨3,![17,14,15,30,21],![6,30,16,34,46]⟩
def data127 : PartitionData E W := ⟨7,![cycle127_0,cycle127_1,cycle127_2,cycle127_3,cycle127_4,cycle127_5,cycle127_6]⟩
lemma valid127 : data127.Valid src127 dst127 Finset.univ := by decide +kernel
lemma src_eq127 : src127 = src (unkey (representativeKey 127)) := by decide +kernel
lemma dst_eq127 : dst127 = dst (unkey (representativeKey 127)) := by decide +kernel
lemma certificate127 : Certificate 127 := by
  refine ⟨data127,?_,?_⟩
  · rw [← src_eq127,← dst_eq127]
    exact valid127
  · decide +kernel

def src128 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,20,44,58,32,10,22,58,34,46]
def dst128 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,20,44,58,32,8,22,58,34,46,10]
def cycle128_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle128_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,44,18,22]⟩
def cycle128_2 : CycleData E W := ⟨2,![3,26,13,17],![6,8,32,30]⟩
def cycle128_3 : CycleData E W := ⟨4,![4,27,28,24,23,22],![8,10,22,58,44,20]⟩
def cycle128_4 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle128_5 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle128_6 : CycleData E W := ⟨2,![14,18,30,15],![16,30,46,34]⟩
def data128 : PartitionData E W := ⟨7,![cycle128_0,cycle128_1,cycle128_2,cycle128_3,cycle128_4,cycle128_5,cycle128_6]⟩
lemma valid128 : data128.Valid src128 dst128 Finset.univ := by decide +kernel
lemma src_eq128 : src128 = src (unkey (representativeKey 128)) := by decide +kernel
lemma dst_eq128 : dst128 = dst (unkey (representativeKey 128)) := by decide +kernel
lemma certificate128 : Certificate 128 := by
  refine ⟨data128,?_,?_⟩
  · rw [← src_eq128,← dst_eq128]
    exact valid128
  · decide +kernel

def src129 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,20,44,58,32,10,34,22,58,46]
def dst129 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,20,44,58,32,8,34,22,58,46,10]
def cycle129_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle129_1 : CycleData E W := ⟨4,![2,17,14,15,28,9],![3,6,30,16,34,22]⟩
def cycle129_2 : CycleData E W := ⟨2,![3,22,23,21],![6,8,20,44]⟩
def cycle129_3 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle129_4 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle129_5 : CycleData E W := ⟨2,![10,29,24,20],![18,22,58,44]⟩
def cycle129_6 : CycleData E W := ⟨2,![13,25,30,18],![30,32,58,46]⟩
def data129 : PartitionData E W := ⟨7,![cycle129_0,cycle129_1,cycle129_2,cycle129_3,cycle129_4,cycle129_5,cycle129_6]⟩
lemma valid129 : data129.Valid src129 dst129 Finset.univ := by decide +kernel
lemma src_eq129 : src129 = src (unkey (representativeKey 129)) := by decide +kernel
lemma dst_eq129 : dst129 = dst (unkey (representativeKey 129)) := by decide +kernel
lemma certificate129 : Certificate 129 := by
  refine ⟨data129,?_,?_⟩
  · rw [← src_eq129,← dst_eq129]
    exact valid129
  · decide +kernel

def src130 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,20,58,32,44,10,34,22,58,46]
def dst130 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,20,58,32,44,8,34,22,58,46,10]
def cycle130_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle130_1 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,20]⟩
def cycle130_2 : CycleData E W := ⟨1,![3,26,21],![6,8,44]⟩
def cycle130_3 : CycleData E W := ⟨3,![4,31,30,23,22],![8,10,46,58,20]⟩
def cycle130_4 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle130_5 : CycleData E W := ⟨3,![12,24,29,28,16],![4,32,58,22,34]⟩
def cycle130_6 : CycleData E W := ⟨3,![19,18,13,25,20],![18,46,30,32,44]⟩
def data130 : PartitionData E W := ⟨7,![cycle130_0,cycle130_1,cycle130_2,cycle130_3,cycle130_4,cycle130_5,cycle130_6]⟩
lemma valid130 : data130.Valid src130 dst130 Finset.univ := by decide +kernel
lemma src_eq130 : src130 = src (unkey (representativeKey 130)) := by decide +kernel
lemma dst_eq130 : dst130 = dst (unkey (representativeKey 130)) := by decide +kernel
lemma certificate130 : Certificate 130 := by
  refine ⟨data130,?_,?_⟩
  · rw [← src_eq130,← dst_eq130]
    exact valid130
  · decide +kernel

def src131 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,20,58,44,32,10,22,58,34,46]
def dst131 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,20,58,44,32,8,22,58,34,46,10]
def cycle131_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle131_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,44,18,22]⟩
def cycle131_2 : CycleData E W := ⟨2,![3,26,13,17],![6,8,32,30]⟩
def cycle131_3 : CycleData E W := ⟨3,![4,27,28,23,22],![8,10,22,58,20]⟩
def cycle131_4 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle131_5 : CycleData E W := ⟨3,![12,25,24,29,16],![4,32,44,58,34]⟩
def cycle131_6 : CycleData E W := ⟨2,![14,18,30,15],![16,30,46,34]⟩
def data131 : PartitionData E W := ⟨7,![cycle131_0,cycle131_1,cycle131_2,cycle131_3,cycle131_4,cycle131_5,cycle131_6]⟩
lemma valid131 : data131.Valid src131 dst131 Finset.univ := by decide +kernel
lemma src_eq131 : src131 = src (unkey (representativeKey 131)) := by decide +kernel
lemma dst_eq131 : dst131 = dst (unkey (representativeKey 131)) := by decide +kernel
lemma certificate131 : Certificate 131 := by
  refine ⟨data131,?_,?_⟩
  · rw [← src_eq131,← dst_eq131]
    exact valid131
  · decide +kernel

def src132 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,20,58,44,32,10,34,22,58,46]
def dst132 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,20,58,44,32,8,34,22,58,46,10]
def cycle132_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle132_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle132_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle132_3 : CycleData E W := ⟨3,![5,31,18,14,6],![2,10,46,30,16]⟩
def cycle132_4 : CycleData E W := ⟨3,![7,23,29,28,15],![16,20,58,22,34]⟩
def cycle132_5 : CycleData E W := ⟨2,![17,13,25,21],![6,30,32,44]⟩
def cycle132_6 : CycleData E W := ⟨2,![19,30,24,20],![18,46,58,44]⟩
def data132 : PartitionData E W := ⟨7,![cycle132_0,cycle132_1,cycle132_2,cycle132_3,cycle132_4,cycle132_5,cycle132_6]⟩
lemma valid132 : data132.Valid src132 dst132 Finset.univ := by decide +kernel
lemma src_eq132 : src132 = src (unkey (representativeKey 132)) := by decide +kernel
lemma dst_eq132 : dst132 = dst (unkey (representativeKey 132)) := by decide +kernel
lemma certificate132 : Certificate 132 := by
  refine ⟨data132,?_,?_⟩
  · rw [← src_eq132,← dst_eq132]
    exact valid132
  · decide +kernel

def src133 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,30,46,18,44,8,32,58,20,44,10,34,22,58,46]
def dst133 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,30,46,18,44,6,32,58,20,44,8,34,22,58,46,10]
def cycle133_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle133_1 : CycleData E W := ⟨4,![2,17,14,15,28,9],![3,6,30,16,34,22]⟩
def cycle133_2 : CycleData E W := ⟨1,![3,26,21],![6,8,44]⟩
def cycle133_3 : CycleData E W := ⟨3,![12,22,4,27,16],![4,32,8,10,34]⟩
def cycle133_4 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle133_5 : CycleData E W := ⟨3,![10,29,24,25,20],![18,22,58,20,44]⟩
def cycle133_6 : CycleData E W := ⟨2,![13,23,30,18],![30,32,58,46]⟩
def data133 : PartitionData E W := ⟨7,![cycle133_0,cycle133_1,cycle133_2,cycle133_3,cycle133_4,cycle133_5,cycle133_6]⟩
lemma valid133 : data133.Valid src133 dst133 Finset.univ := by decide +kernel
lemma src_eq133 : src133 = src (unkey (representativeKey 133)) := by decide +kernel
lemma dst_eq133 : dst133 = dst (unkey (representativeKey 133)) := by decide +kernel
lemma certificate133 : Certificate 133 := by
  refine ⟨data133,?_,?_⟩
  · rw [← src_eq133,← dst_eq133]
    exact valid133
  · decide +kernel

def src134 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,44,58,32,10,22,58,34,46]
def dst134 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,44,58,32,8,22,58,34,46,10]
def cycle134_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle134_1 : CycleData E W := ⟨3,![2,17,24,28,9],![3,6,44,58,22]⟩
def cycle134_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle134_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle134_4 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle134_5 : CycleData E W := ⟨4,![22,23,18,19,13,26],![8,20,44,18,30,32]⟩
def cycle134_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data134 : PartitionData E W := ⟨7,![cycle134_0,cycle134_1,cycle134_2,cycle134_3,cycle134_4,cycle134_5,cycle134_6]⟩
lemma valid134 : data134.Valid src134 dst134 Finset.univ := by decide +kernel
lemma src_eq134 : src134 = src (unkey (representativeKey 134)) := by decide +kernel
lemma dst_eq134 : dst134 = dst (unkey (representativeKey 134)) := by decide +kernel
lemma certificate134 : Certificate 134 := by
  refine ⟨data134,?_,?_⟩
  · rw [← src_eq134,← dst_eq134]
    exact valid134
  · decide +kernel

def src135 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,44,58,32,10,22,58,46,34]
def dst135 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,44,58,32,8,22,58,46,34,10]
def cycle135_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle135_1 : CycleData E W := ⟨3,![2,21,29,28,9],![3,6,46,58,22]⟩
def cycle135_2 : CycleData E W := ⟨2,![3,22,23,17],![6,8,20,44]⟩
def cycle135_3 : CycleData E W := ⟨3,![12,26,4,31,16],![4,32,8,10,34]⟩
def cycle135_4 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle135_5 : CycleData E W := ⟨3,![18,24,25,13,19],![18,44,58,32,30]⟩
def cycle135_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data135 : PartitionData E W := ⟨7,![cycle135_0,cycle135_1,cycle135_2,cycle135_3,cycle135_4,cycle135_5,cycle135_6]⟩
lemma valid135 : data135.Valid src135 dst135 Finset.univ := by decide +kernel
lemma src_eq135 : src135 = src (unkey (representativeKey 135)) := by decide +kernel
lemma dst_eq135 : dst135 = dst (unkey (representativeKey 135)) := by decide +kernel
lemma certificate135 : Certificate 135 := by
  refine ⟨data135,?_,?_⟩
  · rw [← src_eq135,← dst_eq135]
    exact valid135
  · decide +kernel

def src136 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,44,58,32,10,34,22,58,46]
def dst136 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle136_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle136_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle136_2 : CycleData E W := ⟨3,![4,31,20,13,26],![8,10,46,30,32]⟩
def cycle136_3 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle136_4 : CycleData E W := ⟨3,![7,23,18,19,14],![16,20,44,18,30]⟩
def cycle136_5 : CycleData E W := ⟨3,![12,25,29,28,16],![4,32,58,22,34]⟩
def cycle136_6 : CycleData E W := ⟨2,![17,24,30,21],![6,44,58,46]⟩
def data136 : PartitionData E W := ⟨7,![cycle136_0,cycle136_1,cycle136_2,cycle136_3,cycle136_4,cycle136_5,cycle136_6]⟩
lemma valid136 : data136.Valid src136 dst136 Finset.univ := by decide +kernel
lemma src_eq136 : src136 = src (unkey (representativeKey 136)) := by decide +kernel
lemma dst_eq136 : dst136 = dst (unkey (representativeKey 136)) := by decide +kernel
lemma certificate136 : Certificate 136 := by
  refine ⟨data136,?_,?_⟩
  · rw [← src_eq136,← dst_eq136]
    exact valid136
  · decide +kernel

def src137 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,58,32,44,10,34,22,58,46]
def dst137 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,58,32,44,8,34,22,58,46,10]
def cycle137_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle137_1 : CycleData E W := ⟨4,![2,21,20,14,7,8],![3,6,46,30,16,20]⟩
def cycle137_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle137_3 : CycleData E W := ⟨3,![4,31,30,23,22],![8,10,46,58,20]⟩
def cycle137_4 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle137_5 : CycleData E W := ⟨3,![12,24,29,28,16],![4,32,58,22,34]⟩
def cycle137_6 : CycleData E W := ⟨2,![18,25,13,19],![18,44,32,30]⟩
def data137 : PartitionData E W := ⟨7,![cycle137_0,cycle137_1,cycle137_2,cycle137_3,cycle137_4,cycle137_5,cycle137_6]⟩
lemma valid137 : data137.Valid src137 dst137 Finset.univ := by decide +kernel
lemma src_eq137 : src137 = src (unkey (representativeKey 137)) := by decide +kernel
lemma dst_eq137 : dst137 = dst (unkey (representativeKey 137)) := by decide +kernel
lemma certificate137 : Certificate 137 := by
  refine ⟨data137,?_,?_⟩
  · rw [← src_eq137,← dst_eq137]
    exact valid137
  · decide +kernel

def src138 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,58,44,32,10,22,58,34,46]
def dst138 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle138_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle138_1 : CycleData E W := ⟨3,![2,17,24,28,9],![3,6,44,58,22]⟩
def cycle138_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle138_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle138_4 : CycleData E W := ⟨4,![12,26,22,23,29,16],![4,32,8,20,58,34]⟩
def cycle138_5 : CycleData E W := ⟨2,![18,25,13,19],![18,44,32,30]⟩
def cycle138_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data138 : PartitionData E W := ⟨7,![cycle138_0,cycle138_1,cycle138_2,cycle138_3,cycle138_4,cycle138_5,cycle138_6]⟩
lemma valid138 : data138.Valid src138 dst138 Finset.univ := by decide +kernel
lemma src_eq138 : src138 = src (unkey (representativeKey 138)) := by decide +kernel
lemma dst_eq138 : dst138 = dst (unkey (representativeKey 138)) := by decide +kernel
lemma certificate138 : Certificate 138 := by
  refine ⟨data138,?_,?_⟩
  · rw [← src_eq138,← dst_eq138]
    exact valid138
  · decide +kernel

def src139 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,20,58,44,32,10,34,22,58,46]
def dst139 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle139_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle139_1 : CycleData E W := ⟨2,![2,3,22,8],![3,6,8,20]⟩
def cycle139_2 : CycleData E W := ⟨3,![12,26,4,27,16],![4,32,8,10,34]⟩
def cycle139_3 : CycleData E W := ⟨3,![5,31,20,14,6],![2,10,46,30,16]⟩
def cycle139_4 : CycleData E W := ⟨3,![7,23,29,28,15],![16,20,58,22,34]⟩
def cycle139_5 : CycleData E W := ⟨2,![18,25,13,19],![18,44,32,30]⟩
def cycle139_6 : CycleData E W := ⟨2,![17,24,30,21],![6,44,58,46]⟩
def data139 : PartitionData E W := ⟨7,![cycle139_0,cycle139_1,cycle139_2,cycle139_3,cycle139_4,cycle139_5,cycle139_6]⟩
lemma valid139 : data139.Valid src139 dst139 Finset.univ := by decide +kernel
lemma src_eq139 : src139 = src (unkey (representativeKey 139)) := by decide +kernel
lemma dst_eq139 : dst139 = dst (unkey (representativeKey 139)) := by decide +kernel
lemma certificate139 : Certificate 139 := by
  refine ⟨data139,?_,?_⟩
  · rw [← src_eq139,← dst_eq139]
    exact valid139
  · decide +kernel

def src140 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,32,58,20,44,10,22,58,34,46]
def dst140 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,32,58,20,44,8,22,58,34,46,10]
def cycle140_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle140_1 : CycleData E W := ⟨4,![2,17,25,24,28,9],![3,6,44,20,58,22]⟩
def cycle140_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle140_3 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle140_4 : CycleData E W := ⟨2,![12,23,29,16],![4,32,58,34]⟩
def cycle140_5 : CycleData E W := ⟨3,![22,13,19,18,26],![8,32,30,18,44]⟩
def cycle140_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data140 : PartitionData E W := ⟨7,![cycle140_0,cycle140_1,cycle140_2,cycle140_3,cycle140_4,cycle140_5,cycle140_6]⟩
lemma valid140 : data140.Valid src140 dst140 Finset.univ := by decide +kernel
lemma src_eq140 : src140 = src (unkey (representativeKey 140)) := by decide +kernel
lemma dst_eq140 : dst140 = dst (unkey (representativeKey 140)) := by decide +kernel
lemma certificate140 : Certificate 140 := by
  refine ⟨data140,?_,?_⟩
  · rw [← src_eq140,← dst_eq140]
    exact valid140
  · decide +kernel

def src141 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,32,58,20,44,10,22,58,46,34]
def dst141 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,32,58,20,44,8,22,58,46,34,10]
def cycle141_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,20,16]⟩
def cycle141_1 : CycleData E W := ⟨3,![2,21,29,28,9],![3,6,46,58,22]⟩
def cycle141_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle141_3 : CycleData E W := ⟨3,![12,22,4,31,16],![4,32,8,10,34]⟩
def cycle141_4 : CycleData E W := ⟨2,![5,27,10,11],![2,10,22,18]⟩
def cycle141_5 : CycleData E W := ⟨4,![18,25,24,23,13,19],![18,44,20,58,32,30]⟩
def cycle141_6 : CycleData E W := ⟨2,![14,20,30,15],![16,30,46,34]⟩
def data141 : PartitionData E W := ⟨7,![cycle141_0,cycle141_1,cycle141_2,cycle141_3,cycle141_4,cycle141_5,cycle141_6]⟩
lemma valid141 : data141.Valid src141 dst141 Finset.univ := by decide +kernel
lemma src_eq141 : src141 = src (unkey (representativeKey 141)) := by decide +kernel
lemma dst_eq141 : dst141 = dst (unkey (representativeKey 141)) := by decide +kernel
lemma certificate141 : Certificate 141 := by
  refine ⟨data141,?_,?_⟩
  · rw [← src_eq141,← dst_eq141]
    exact valid141
  · decide +kernel

def src142 : E → W := ![2,4,3,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,32,58,20,44,10,34,22,58,46]
def dst142 : E → W := ![4,3,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle142_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,18]⟩
def cycle142_1 : CycleData E W := ⟨2,![2,17,25,8],![3,6,44,20]⟩
def cycle142_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle142_3 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle142_4 : CycleData E W := ⟨3,![7,24,30,20,14],![16,20,58,46,30]⟩
def cycle142_5 : CycleData E W := ⟨3,![12,23,29,28,16],![4,32,58,22,34]⟩
def cycle142_6 : CycleData E W := ⟨3,![22,13,19,18,26],![8,32,30,18,44]⟩
def data142 : PartitionData E W := ⟨7,![cycle142_0,cycle142_1,cycle142_2,cycle142_3,cycle142_4,cycle142_5,cycle142_6]⟩
lemma valid142 : data142.Valid src142 dst142 Finset.univ := by decide +kernel
lemma src_eq142 : src142 = src (unkey (representativeKey 142)) := by decide +kernel
lemma dst_eq142 : dst142 = dst (unkey (representativeKey 142)) := by decide +kernel
lemma certificate142 : Certificate 142 := by
  refine ⟨data142,?_,?_⟩
  · rw [← src_eq142,← dst_eq142]
    exact valid142
  · decide +kernel

def src143 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,16,30,34,32,6,30,44,18,46,8,20,44,58,32,10,34,22,58,46]
def dst143 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,16,30,34,32,4,30,44,18,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle143_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle143_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle143_2 : CycleData E W := ⟨4,![5,4,26,16,12,6],![2,10,8,32,4,16]⟩
def cycle143_3 : CycleData E W := ⟨2,![7,23,18,13],![16,20,44,30]⟩
def cycle143_4 : CycleData E W := ⟨3,![17,14,27,31,21],![6,30,34,10,46]⟩
def cycle143_5 : CycleData E W := ⟨2,![28,15,25,29],![22,34,32,58]⟩
def cycle143_6 : CycleData E W := ⟨2,![19,24,30,20],![18,44,58,46]⟩
def data143 : PartitionData E W := ⟨7,![cycle143_0,cycle143_1,cycle143_2,cycle143_3,cycle143_4,cycle143_5,cycle143_6]⟩
lemma valid143 : data143.Valid src143 dst143 Finset.univ := by decide +kernel
lemma src_eq143 : src143 = src (unkey (representativeKey 143)) := by decide +kernel
lemma dst_eq143 : dst143 = dst (unkey (representativeKey 143)) := by decide +kernel
lemma certificate143 : Certificate 143 := by
  refine ⟨data143,?_,?_⟩
  · rw [← src_eq143,← dst_eq143]
    exact valid143
  · decide +kernel

def src144 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,16,30,34,32,6,30,44,18,46,8,20,44,58,32,10,46,34,22,58]
def dst144 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,16,30,34,32,4,30,44,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle144_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle144_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle144_2 : CycleData E W := ⟨4,![5,4,26,16,12,6],![2,10,8,32,4,16]⟩
def cycle144_3 : CycleData E W := ⟨2,![7,23,18,13],![16,20,44,30]⟩
def cycle144_4 : CycleData E W := ⟨2,![17,14,28,21],![6,30,34,46]⟩
def cycle144_5 : CycleData E W := ⟨2,![29,15,25,30],![22,34,32,58]⟩
def cycle144_6 : CycleData E W := ⟨3,![27,20,19,24,31],![10,46,18,44,58]⟩
def data144 : PartitionData E W := ⟨7,![cycle144_0,cycle144_1,cycle144_2,cycle144_3,cycle144_4,cycle144_5,cycle144_6]⟩
lemma valid144 : data144.Valid src144 dst144 Finset.univ := by decide +kernel
lemma src_eq144 : src144 = src (unkey (representativeKey 144)) := by decide +kernel
lemma dst_eq144 : dst144 = dst (unkey (representativeKey 144)) := by decide +kernel
lemma certificate144 : Certificate 144 := by
  refine ⟨data144,?_,?_⟩
  · rw [← src_eq144,← dst_eq144]
    exact valid144
  · decide +kernel

def src145 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,16,34,30,32,6,30,18,44,46,8,20,44,58,32,10,34,46,22,58]
def dst145 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,16,34,30,32,4,30,18,44,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle145_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle145_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle145_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle145_3 : CycleData E W := ⟨2,![5,27,13,6],![2,10,34,16]⟩
def cycle145_4 : CycleData E W := ⟨5,![12,7,23,19,18,15,16],![4,16,20,44,18,30,32]⟩
def cycle145_5 : CycleData E W := ⟨2,![17,14,28,21],![6,30,34,46]⟩
def cycle145_6 : CycleData E W := ⟨2,![29,20,24,30],![22,46,44,58]⟩
def data145 : PartitionData E W := ⟨7,![cycle145_0,cycle145_1,cycle145_2,cycle145_3,cycle145_4,cycle145_5,cycle145_6]⟩
lemma valid145 : data145.Valid src145 dst145 Finset.univ := by decide +kernel
lemma src_eq145 : src145 = src (unkey (representativeKey 145)) := by decide +kernel
lemma dst_eq145 : dst145 = dst (unkey (representativeKey 145)) := by decide +kernel
lemma certificate145 : Certificate 145 := by
  refine ⟨data145,?_,?_⟩
  · rw [← src_eq145,← dst_eq145]
    exact valid145
  · decide +kernel

def src146 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,16,34,30,32,6,30,44,18,46,8,20,44,58,32,10,34,46,22,58]
def dst146 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,16,34,30,32,4,30,44,18,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle146_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle146_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle146_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle146_3 : CycleData E W := ⟨2,![5,27,13,6],![2,10,34,16]⟩
def cycle146_4 : CycleData E W := ⟨4,![12,7,23,18,15,16],![4,16,20,44,30,32]⟩
def cycle146_5 : CycleData E W := ⟨2,![17,14,28,21],![6,30,34,46]⟩
def cycle146_6 : CycleData E W := ⟨3,![19,24,30,29,20],![18,44,58,22,46]⟩
def data146 : PartitionData E W := ⟨7,![cycle146_0,cycle146_1,cycle146_2,cycle146_3,cycle146_4,cycle146_5,cycle146_6]⟩
lemma valid146 : data146.Valid src146 dst146 Finset.univ := by decide +kernel
lemma src_eq146 : src146 = src (unkey (representativeKey 146)) := by decide +kernel
lemma dst_eq146 : dst146 = dst (unkey (representativeKey 146)) := by decide +kernel
lemma certificate146 : Certificate 146 := by
  refine ⟨data146,?_,?_⟩
  · rw [← src_eq146,← dst_eq146]
    exact valid146
  · decide +kernel

def src147 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,16,34,32,30,6,30,18,44,46,8,20,44,58,32,10,34,46,22,58]
def dst147 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,16,34,32,30,4,30,18,44,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle147_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle147_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle147_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle147_3 : CycleData E W := ⟨2,![5,27,13,6],![2,10,34,16]⟩
def cycle147_4 : CycleData E W := ⟨4,![12,7,23,19,18,16],![4,16,20,44,18,30]⟩
def cycle147_5 : CycleData E W := ⟨3,![17,15,14,28,21],![6,30,32,34,46]⟩
def cycle147_6 : CycleData E W := ⟨2,![29,20,24,30],![22,46,44,58]⟩
def data147 : PartitionData E W := ⟨7,![cycle147_0,cycle147_1,cycle147_2,cycle147_3,cycle147_4,cycle147_5,cycle147_6]⟩
lemma valid147 : data147.Valid src147 dst147 Finset.univ := by decide +kernel
lemma src_eq147 : src147 = src (unkey (representativeKey 147)) := by decide +kernel
lemma dst_eq147 : dst147 = dst (unkey (representativeKey 147)) := by decide +kernel
lemma certificate147 : Certificate 147 := by
  refine ⟨data147,?_,?_⟩
  · rw [← src_eq147,← dst_eq147]
    exact valid147
  · decide +kernel

def src148 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,30,18,44,46,8,20,44,58,32,10,34,46,22,58]
def dst148 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,30,18,44,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle148_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle148_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle148_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle148_3 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle148_4 : CycleData E W := ⟨3,![7,23,19,18,13],![16,20,44,18,30]⟩
def cycle148_5 : CycleData E W := ⟨4,![12,17,21,28,15,16],![4,30,6,46,34,32]⟩
def cycle148_6 : CycleData E W := ⟨2,![29,20,24,30],![22,46,44,58]⟩
def data148 : PartitionData E W := ⟨7,![cycle148_0,cycle148_1,cycle148_2,cycle148_3,cycle148_4,cycle148_5,cycle148_6]⟩
lemma valid148 : data148.Valid src148 dst148 Finset.univ := by decide +kernel
lemma src_eq148 : src148 = src (unkey (representativeKey 148)) := by decide +kernel
lemma dst_eq148 : dst148 = dst (unkey (representativeKey 148)) := by decide +kernel
lemma certificate148 : Certificate 148 := by
  refine ⟨data148,?_,?_⟩
  · rw [← src_eq148,← dst_eq148]
    exact valid148
  · decide +kernel

def src149 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,30,18,44,46,8,20,44,58,32,10,46,34,22,58]
def dst149 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,30,18,44,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle149_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle149_1 : CycleData E W := ⟨4,![1,16,26,22,8,9],![3,4,32,8,20,22]⟩
def cycle149_2 : CycleData E W := ⟨2,![2,17,18,10],![3,6,30,18]⟩
def cycle149_3 : CycleData E W := ⟨2,![3,4,27,21],![6,8,10,46]⟩
def cycle149_4 : CycleData E W := ⟨3,![5,31,24,19,11],![2,10,58,44,18]⟩
def cycle149_5 : CycleData E W := ⟨3,![7,23,20,28,14],![16,20,44,46,34]⟩
def cycle149_6 : CycleData E W := ⟨2,![29,15,25,30],![22,34,32,58]⟩
def data149 : PartitionData E W := ⟨7,![cycle149_0,cycle149_1,cycle149_2,cycle149_3,cycle149_4,cycle149_5,cycle149_6]⟩
lemma valid149 : data149.Valid src149 dst149 Finset.univ := by decide +kernel
lemma src_eq149 : src149 = src (unkey (representativeKey 149)) := by decide +kernel
lemma dst_eq149 : dst149 = dst (unkey (representativeKey 149)) := by decide +kernel
lemma certificate149 : Certificate 149 := by
  refine ⟨data149,?_,?_⟩
  · rw [← src_eq149,← dst_eq149]
    exact valid149
  · decide +kernel
#print axioms certificate149
end Erdos184Work.SixRepresentativeCertificates1

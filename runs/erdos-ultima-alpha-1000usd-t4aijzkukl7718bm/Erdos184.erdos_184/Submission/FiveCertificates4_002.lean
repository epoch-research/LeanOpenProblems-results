import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src100 : E → W := ![2,4,6,3,5,8,2,14,3,18,16,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst100 : E → W := ![4,6,3,5,8,2,14,3,18,16,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle100_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle100_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,6,4,28,14]⟩
def cycle100_2 : CycleData E W := ⟨3,![3,12,19,24,8],![3,5,26,39,18]⟩
def cycle100_3 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle100_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle100_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data100 : PartitionData E W := ⟨6,![cycle100_0,cycle100_1,cycle100_2,cycle100_3,cycle100_4,cycle100_5]⟩
lemma valid_data100 : data100.Valid src100 dst100 Finset.univ := by decide +kernel

def src101 : E → W := ![2,4,6,3,5,8,2,14,3,18,16,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst101 : E → W := ![4,6,3,5,8,2,14,3,18,16,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle101_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle101_1 : CycleData E W := ⟨3,![2,1,15,14,7],![3,6,4,28,14]⟩
def cycle101_2 : CycleData E W := ⟨3,![3,12,17,22,8],![3,5,26,38,18]⟩
def cycle101_3 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle101_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle101_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data101 : PartitionData E W := ⟨6,![cycle101_0,cycle101_1,cycle101_2,cycle101_3,cycle101_4,cycle101_5]⟩
lemma valid_data101 : data101.Valid src101 dst101 Finset.univ := by decide +kernel

def src102 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,38,26,39,8,38,18,28,39]
def dst102 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle102_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle102_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle102_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle102_3 : CycleData E W := ⟨3,![3,12,13,7,8],![3,5,26,14,18]⟩
def cycle102_4 : CycleData E W := ⟨4,![6,14,23,22,17,10],![2,14,28,18,38,16]⟩
def cycle102_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data102 : PartitionData E W := ⟨6,![cycle102_0,cycle102_1,cycle102_2,cycle102_3,cycle102_4,cycle102_5]⟩
lemma valid_data102 : data102.Valid src102 dst102 Finset.univ := by decide +kernel

def src103 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,38,26,39,8,38,28,18,39]
def dst103 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle103_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle103_1 : CycleData E W := ⟨3,![1,16,17,22,15],![4,6,16,38,28]⟩
def cycle103_2 : CycleData E W := ⟨2,![2,20,24,8],![3,6,39,18]⟩
def cycle103_3 : CycleData E W := ⟨4,![6,13,12,3,9,10],![2,14,26,5,3,16]⟩
def cycle103_4 : CycleData E W := ⟨1,![7,23,14],![14,18,28]⟩
def cycle103_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data103 : PartitionData E W := ⟨6,![cycle103_0,cycle103_1,cycle103_2,cycle103_3,cycle103_4,cycle103_5]⟩
lemma valid_data103 : data103.Valid src103 dst103 Finset.univ := by decide +kernel

def src104 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,39,26,38,8,38,18,28,39]
def dst104 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle104_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle104_1 : CycleData E W := ⟨3,![1,20,22,23,15],![4,6,38,18,28]⟩
def cycle104_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle104_3 : CycleData E W := ⟨3,![3,12,13,7,8],![3,5,26,14,18]⟩
def cycle104_4 : CycleData E W := ⟨3,![6,14,24,17,10],![2,14,28,39,16]⟩
def cycle104_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data104 : PartitionData E W := ⟨6,![cycle104_0,cycle104_1,cycle104_2,cycle104_3,cycle104_4,cycle104_5]⟩
lemma valid_data104 : data104.Valid src104 dst104 Finset.univ := by decide +kernel

def src105 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,39,26,38,8,38,28,18,39]
def dst105 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle105_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle105_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,38,28]⟩
def cycle105_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle105_3 : CycleData E W := ⟨3,![3,12,13,7,8],![3,5,26,14,18]⟩
def cycle105_4 : CycleData E W := ⟨4,![6,14,23,24,17,10],![2,14,28,18,39,16]⟩
def cycle105_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data105 : PartitionData E W := ⟨6,![cycle105_0,cycle105_1,cycle105_2,cycle105_3,cycle105_4,cycle105_5]⟩
lemma valid_data105 : data105.Valid src105 dst105 Finset.univ := by decide +kernel

def src106 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,16,26,39,8,18,38,28,39]
def dst106 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle106_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle106_1 : CycleData E W := ⟨2,![1,16,23,15],![4,6,38,28]⟩
def cycle106_2 : CycleData E W := ⟨3,![2,20,19,12,3],![3,6,39,26,5]⟩
def cycle106_3 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle106_4 : CycleData E W := ⟨3,![21,7,14,24,25],![8,18,14,28,39]⟩
def cycle106_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data106 : PartitionData E W := ⟨6,![cycle106_0,cycle106_1,cycle106_2,cycle106_3,cycle106_4,cycle106_5]⟩
lemma valid_data106 : data106.Valid src106 dst106 Finset.univ := by decide +kernel

def src107 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,16,26,39,8,18,39,28,38]
def dst107 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle107_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle107_1 : CycleData E W := ⟨2,![1,20,23,15],![4,6,39,28]⟩
def cycle107_2 : CycleData E W := ⟨2,![2,16,17,9],![3,6,38,16]⟩
def cycle107_3 : CycleData E W := ⟨3,![3,12,19,22,8],![3,5,26,39,18]⟩
def cycle107_4 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle107_5 : CycleData E W := ⟨3,![21,7,14,24,25],![8,18,14,28,38]⟩
def data107 : PartitionData E W := ⟨6,![cycle107_0,cycle107_1,cycle107_2,cycle107_3,cycle107_4,cycle107_5]⟩
lemma valid_data107 : data107.Valid src107 dst107 Finset.univ := by decide +kernel

def src108 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst108 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle108_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle108_1 : CycleData E W := ⟨2,![1,16,22,15],![4,6,38,28]⟩
def cycle108_2 : CycleData E W := ⟨3,![2,20,19,12,3],![3,6,39,26,5]⟩
def cycle108_3 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle108_4 : CycleData E W := ⟨1,![7,23,14],![14,18,28]⟩
def cycle108_5 : CycleData E W := ⟨4,![8,24,25,21,17,9],![3,18,39,8,38,16]⟩
def data108 : PartitionData E W := ⟨6,![cycle108_0,cycle108_1,cycle108_2,cycle108_3,cycle108_4,cycle108_5]⟩
lemma valid_data108 : data108.Valid src108 dst108 Finset.univ := by decide +kernel

def src109 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,26,16,39,8,18,38,28,39]
def dst109 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle109_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle109_1 : CycleData E W := ⟨2,![1,16,23,15],![4,6,38,28]⟩
def cycle109_2 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle109_3 : CycleData E W := ⟨3,![3,12,17,22,8],![3,5,26,38,18]⟩
def cycle109_4 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle109_5 : CycleData E W := ⟨3,![21,7,14,24,25],![8,18,14,28,39]⟩
def data109 : PartitionData E W := ⟨6,![cycle109_0,cycle109_1,cycle109_2,cycle109_3,cycle109_4,cycle109_5]⟩
lemma valid_data109 : data109.Valid src109 dst109 Finset.univ := by decide +kernel

def src110 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,26,16,39,8,18,39,28,38]
def dst110 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle110_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle110_1 : CycleData E W := ⟨2,![1,20,23,15],![4,6,39,28]⟩
def cycle110_2 : CycleData E W := ⟨3,![2,16,17,12,3],![3,6,38,26,5]⟩
def cycle110_3 : CycleData E W := ⟨2,![6,13,18,10],![2,14,26,16]⟩
def cycle110_4 : CycleData E W := ⟨3,![21,7,14,24,25],![8,18,14,28,38]⟩
def cycle110_5 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def data110 : PartitionData E W := ⟨6,![cycle110_0,cycle110_1,cycle110_2,cycle110_3,cycle110_4,cycle110_5]⟩
lemma valid_data110 : data110.Valid src110 dst110 Finset.univ := by decide +kernel

def src111 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst111 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle111_0 : CycleData E W := ⟨2,![0,11,4,5],![2,4,5,8]⟩
def cycle111_1 : CycleData E W := ⟨3,![2,1,15,23,8],![3,6,4,28,18]⟩
def cycle111_2 : CycleData E W := ⟨2,![3,12,18,9],![3,5,26,16]⟩
def cycle111_3 : CycleData E W := ⟨3,![6,14,24,19,10],![2,14,28,39,16]⟩
def cycle111_4 : CycleData E W := ⟨2,![7,22,17,13],![14,18,38,26]⟩
def cycle111_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data111 : PartitionData E W := ⟨6,![cycle111_0,cycle111_1,cycle111_2,cycle111_3,cycle111_4,cycle111_5]⟩
lemma valid_data111 : data111.Valid src111 dst111 Finset.univ := by decide +kernel

def src112 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,26,38,39,8,38,18,28,39]
def dst112 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle112_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle112_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle112_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle112_3 : CycleData E W := ⟨2,![3,14,23,8],![3,5,28,18]⟩
def cycle112_4 : CycleData E W := ⟨3,![5,4,13,17,10],![2,8,5,26,16]⟩
def cycle112_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def cycle112_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data112 : PartitionData E W := ⟨7,![cycle112_0,cycle112_1,cycle112_2,cycle112_3,cycle112_4,cycle112_5,cycle112_6]⟩
lemma valid_data112 : data112.Valid src112 dst112 Finset.univ := by decide +kernel

def src113 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,26,39,38,8,38,28,18,39]
def dst113 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle113_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle113_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,38,28]⟩
def cycle113_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle113_3 : CycleData E W := ⟨2,![3,14,23,8],![3,5,28,18]⟩
def cycle113_4 : CycleData E W := ⟨3,![5,4,13,17,10],![2,8,5,26,16]⟩
def cycle113_5 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def cycle113_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data113 : PartitionData E W := ⟨7,![cycle113_0,cycle113_1,cycle113_2,cycle113_3,cycle113_4,cycle113_5,cycle113_6]⟩
lemma valid_data113 : data113.Valid src113 dst113 Finset.univ := by decide +kernel

def src114 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,28,38,18,39]
def dst114 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle114_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle114_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle114_2 : CycleData E W := ⟨3,![4,21,22,18,13],![5,8,28,38,26]⟩
def cycle114_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle114_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle114_5 : CycleData E W := ⟨2,![8,23,17,9],![3,18,38,16]⟩
def data114 : PartitionData E W := ⟨6,![cycle114_0,cycle114_1,cycle114_2,cycle114_3,cycle114_4,cycle114_5]⟩
lemma valid_data114 : data114.Valid src114 dst114 Finset.univ := by decide +kernel

def src115 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,28,39,18,38]
def dst115 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle115_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle115_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,39,28]⟩
def cycle115_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle115_3 : CycleData E W := ⟨3,![3,13,12,7,8],![3,5,26,14,18]⟩
def cycle115_4 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle115_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle115_6 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data115 : PartitionData E W := ⟨7,![cycle115_0,cycle115_1,cycle115_2,cycle115_3,cycle115_4,cycle115_5,cycle115_6]⟩
lemma valid_data115 : data115.Valid src115 dst115 Finset.univ := by decide +kernel

def src116 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,38,18,28,39]
def dst116 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle116_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle116_1 : CycleData E W := ⟨2,![1,20,24,15],![4,6,39,28]⟩
def cycle116_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle116_3 : CycleData E W := ⟨2,![3,14,23,8],![3,5,28,18]⟩
def cycle116_4 : CycleData E W := ⟨2,![4,25,19,13],![5,8,39,26]⟩
def cycle116_5 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle116_6 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data116 : PartitionData E W := ⟨7,![cycle116_0,cycle116_1,cycle116_2,cycle116_3,cycle116_4,cycle116_5,cycle116_6]⟩
lemma valid_data116 : data116.Valid src116 dst116 Finset.univ := by decide +kernel

def src117 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,38,28,18,39]
def dst117 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle117_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle117_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle117_2 : CycleData E W := ⟨2,![4,21,18,13],![5,8,38,26]⟩
def cycle117_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle117_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle117_5 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def data117 : PartitionData E W := ⟨6,![cycle117_0,cycle117_1,cycle117_2,cycle117_3,cycle117_4,cycle117_5]⟩
lemma valid_data117 : data117.Valid src117 dst117 Finset.univ := by decide +kernel

def src118 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,39,26,8,38,28,18,39]
def dst118 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle118_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle118_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle118_2 : CycleData E W := ⟨4,![5,4,13,20,16,10],![2,8,5,26,6,16]⟩
def cycle118_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle118_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle118_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data118 : PartitionData E W := ⟨6,![cycle118_0,cycle118_1,cycle118_2,cycle118_3,cycle118_4,cycle118_5]⟩
lemma valid_data118 : data118.Valid src118 dst118 Finset.univ := by decide +kernel

def src119 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,28,38,18,39]
def dst119 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle119_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle119_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,38,28]⟩
def cycle119_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle119_3 : CycleData E W := ⟨3,![3,13,12,7,8],![3,5,26,14,18]⟩
def cycle119_4 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle119_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle119_6 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data119 : PartitionData E W := ⟨7,![cycle119_0,cycle119_1,cycle119_2,cycle119_3,cycle119_4,cycle119_5,cycle119_6]⟩
lemma valid_data119 : data119.Valid src119 dst119 Finset.univ := by decide +kernel

def src120 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,28,39,18,38]
def dst120 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle120_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle120_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle120_2 : CycleData E W := ⟨3,![4,21,22,18,13],![5,8,28,39,26]⟩
def cycle120_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,38,6,16]⟩
def cycle120_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,38,26]⟩
def cycle120_5 : CycleData E W := ⟨2,![8,23,17,9],![3,18,39,16]⟩
def data120 : PartitionData E W := ⟨6,![cycle120_0,cycle120_1,cycle120_2,cycle120_3,cycle120_4,cycle120_5]⟩
lemma valid_data120 : data120.Valid src120 dst120 Finset.univ := by decide +kernel

def src121 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,38,18,28,39]
def dst121 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle121_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle121_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle121_2 : CycleData E W := ⟨2,![4,21,19,13],![5,8,38,26]⟩
def cycle121_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle121_4 : CycleData E W := ⟨3,![7,23,24,18,12],![14,18,28,39,26]⟩
def cycle121_5 : CycleData E W := ⟨3,![8,22,20,16,9],![3,18,38,6,16]⟩
def data121 : PartitionData E W := ⟨6,![cycle121_0,cycle121_1,cycle121_2,cycle121_3,cycle121_4,cycle121_5]⟩
lemma valid_data121 : data121.Valid src121 dst121 Finset.univ := by decide +kernel

def src122 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,38,28,18,39]
def dst122 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle122_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle122_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,38,28]⟩
def cycle122_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle122_3 : CycleData E W := ⟨2,![3,14,23,8],![3,5,28,18]⟩
def cycle122_4 : CycleData E W := ⟨2,![4,21,19,13],![5,8,38,26]⟩
def cycle122_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle122_6 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def data122 : PartitionData E W := ⟨7,![cycle122_0,cycle122_1,cycle122_2,cycle122_3,cycle122_4,cycle122_5,cycle122_6]⟩
lemma valid_data122 : data122.Valid src122 dst122 Finset.univ := by decide +kernel

def src123 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,38,26,8,38,18,28,39]
def dst123 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle123_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle123_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle123_2 : CycleData E W := ⟨4,![5,4,13,20,16,10],![2,8,5,26,6,16]⟩
def cycle123_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,38,26]⟩
def cycle123_4 : CycleData E W := ⟨3,![8,23,24,17,9],![3,18,28,39,16]⟩
def cycle123_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data123 : PartitionData E W := ⟨6,![cycle123_0,cycle123_1,cycle123_2,cycle123_3,cycle123_4,cycle123_5]⟩
lemma valid_data123 : data123.Valid src123 dst123 Finset.univ := by decide +kernel

def src124 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,16,38,39,8,38,28,18,39]
def dst124 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle124_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle124_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle124_2 : CycleData E W := ⟨3,![5,4,13,17,10],![2,8,5,26,16]⟩
def cycle124_3 : CycleData E W := ⟨3,![16,12,7,24,20],![6,26,14,18,39]⟩
def cycle124_4 : CycleData E W := ⟨3,![8,23,22,18,9],![3,18,28,38,16]⟩
def cycle124_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data124 : PartitionData E W := ⟨6,![cycle124_0,cycle124_1,cycle124_2,cycle124_3,cycle124_4,cycle124_5]⟩
lemma valid_data124 : data124.Valid src124 dst124 Finset.univ := by decide +kernel

def src125 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,16,39,38,8,38,18,28,39]
def dst125 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle125_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle125_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle125_2 : CycleData E W := ⟨3,![5,4,13,17,10],![2,8,5,26,16]⟩
def cycle125_3 : CycleData E W := ⟨3,![16,12,7,22,20],![6,26,14,18,38]⟩
def cycle125_4 : CycleData E W := ⟨3,![8,23,24,18,9],![3,18,28,39,16]⟩
def cycle125_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data125 : PartitionData E W := ⟨6,![cycle125_0,cycle125_1,cycle125_2,cycle125_3,cycle125_4,cycle125_5]⟩
lemma valid_data125 : data125.Valid src125 dst125 Finset.univ := by decide +kernel

def src126 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,18,38,28,39]
def dst126 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle126_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle126_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle126_2 : CycleData E W := ⟨3,![4,21,7,12,13],![5,8,18,14,26]⟩
def cycle126_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle126_4 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def cycle126_5 : CycleData E W := ⟨3,![16,17,23,24,20],![6,26,38,28,39]⟩
def data126 : PartitionData E W := ⟨6,![cycle126_0,cycle126_1,cycle126_2,cycle126_3,cycle126_4,cycle126_5]⟩
lemma valid_data126 : data126.Valid src126 dst126 Finset.univ := by decide +kernel

def src127 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,18,39,28,38]
def dst127 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle127_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle127_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle127_2 : CycleData E W := ⟨3,![4,21,7,12,13],![5,8,18,14,26]⟩
def cycle127_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,38,16]⟩
def cycle127_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle127_5 : CycleData E W := ⟨3,![16,17,24,23,20],![6,26,38,28,39]⟩
def data127 : PartitionData E W := ⟨6,![cycle127_0,cycle127_1,cycle127_2,cycle127_3,cycle127_4,cycle127_5]⟩
lemma valid_data127 : data127.Valid src127 dst127 Finset.univ := by decide +kernel

def src128 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst128 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle128_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle128_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle128_2 : CycleData E W := ⟨2,![4,21,17,13],![5,8,38,26]⟩
def cycle128_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle128_4 : CycleData E W := ⟨4,![16,12,7,23,24,20],![6,26,14,18,28,39]⟩
def cycle128_5 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def data128 : PartitionData E W := ⟨6,![cycle128_0,cycle128_1,cycle128_2,cycle128_3,cycle128_4,cycle128_5]⟩
lemma valid_data128 : data128.Valid src128 dst128 Finset.univ := by decide +kernel

def src129 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst129 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle129_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle129_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle129_2 : CycleData E W := ⟨2,![4,21,17,13],![5,8,38,26]⟩
def cycle129_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle129_4 : CycleData E W := ⟨3,![16,12,7,24,20],![6,26,14,18,39]⟩
def cycle129_5 : CycleData E W := ⟨3,![8,23,22,18,9],![3,18,28,38,16]⟩
def data129 : PartitionData E W := ⟨6,![cycle129_0,cycle129_1,cycle129_2,cycle129_3,cycle129_4,cycle129_5]⟩
lemma valid_data129 : data129.Valid src129 dst129 Finset.univ := by decide +kernel

def src130 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,18,38,28,39]
def dst130 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle130_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle130_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle130_2 : CycleData E W := ⟨3,![4,21,7,12,13],![5,8,18,14,26]⟩
def cycle130_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle130_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,38,16]⟩
def cycle130_5 : CycleData E W := ⟨3,![16,17,24,23,20],![6,26,39,28,38]⟩
def data130 : PartitionData E W := ⟨6,![cycle130_0,cycle130_1,cycle130_2,cycle130_3,cycle130_4,cycle130_5]⟩
lemma valid_data130 : data130.Valid src130 dst130 Finset.univ := by decide +kernel

def src131 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,18,39,28,38]
def dst131 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle131_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle131_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle131_2 : CycleData E W := ⟨3,![4,21,7,12,13],![5,8,18,14,26]⟩
def cycle131_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,38,16]⟩
def cycle131_4 : CycleData E W := ⟨2,![8,22,18,9],![3,18,39,16]⟩
def cycle131_5 : CycleData E W := ⟨3,![16,17,23,24,20],![6,26,39,28,38]⟩
def data131 : PartitionData E W := ⟨6,![cycle131_0,cycle131_1,cycle131_2,cycle131_3,cycle131_4,cycle131_5]⟩
lemma valid_data131 : data131.Valid src131 dst131 Finset.univ := by decide +kernel

def src132 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst132 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle132_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle132_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle132_2 : CycleData E W := ⟨3,![4,21,20,16,13],![5,8,38,6,26]⟩
def cycle132_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle132_4 : CycleData E W := ⟨3,![7,23,24,17,12],![14,18,28,39,26]⟩
def cycle132_5 : CycleData E W := ⟨2,![8,22,19,9],![3,18,38,16]⟩
def data132 : PartitionData E W := ⟨6,![cycle132_0,cycle132_1,cycle132_2,cycle132_3,cycle132_4,cycle132_5]⟩
lemma valid_data132 : data132.Valid src132 dst132 Finset.univ := by decide +kernel

def src133 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst133 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle133_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle133_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle133_2 : CycleData E W := ⟨3,![4,21,20,16,13],![5,8,38,6,26]⟩
def cycle133_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle133_4 : CycleData E W := ⟨2,![7,24,17,12],![14,18,39,26]⟩
def cycle133_5 : CycleData E W := ⟨3,![8,23,22,19,9],![3,18,28,38,16]⟩
def data133 : PartitionData E W := ⟨6,![cycle133_0,cycle133_1,cycle133_2,cycle133_3,cycle133_4,cycle133_5]⟩
lemma valid_data133 : data133.Valid src133 dst133 Finset.univ := by decide +kernel

def src134 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,28,38,39]
def dst134 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle134_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,16]⟩
def cycle134_1 : CycleData E W := ⟨2,![3,4,21,8],![3,5,8,18]⟩
def cycle134_2 : CycleData E W := ⟨3,![5,25,19,12,6],![2,8,39,26,14]⟩
def cycle134_3 : CycleData E W := ⟨2,![11,7,22,15],![4,14,18,28]⟩
def cycle134_4 : CycleData E W := ⟨3,![13,18,17,23,14],![5,26,16,38,28]⟩
def cycle134_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data134 : PartitionData E W := ⟨6,![cycle134_0,cycle134_1,cycle134_2,cycle134_3,cycle134_4,cycle134_5]⟩
lemma valid_data134 : data134.Valid src134 dst134 Finset.univ := by decide +kernel

def src135 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,38,28,39]
def dst135 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle135_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle135_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle135_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle135_3 : CycleData E W := ⟨3,![21,7,12,19,25],![8,18,14,26,39]⟩
def cycle135_4 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def cycle135_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data135 : PartitionData E W := ⟨6,![cycle135_0,cycle135_1,cycle135_2,cycle135_3,cycle135_4,cycle135_5]⟩
lemma valid_data135 : data135.Valid src135 dst135 Finset.univ := by decide +kernel

def src136 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,39,28,38]
def dst136 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle136_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle136_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle136_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle136_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle136_4 : CycleData E W := ⟨3,![8,21,25,17,9],![3,18,8,38,16]⟩
def cycle136_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data136 : PartitionData E W := ⟨6,![cycle136_0,cycle136_1,cycle136_2,cycle136_3,cycle136_4,cycle136_5]⟩
lemma valid_data136 : data136.Valid src136 dst136 Finset.univ := by decide +kernel

def src137 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,39,38,28]
def dst137 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle137_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,16]⟩
def cycle137_1 : CycleData E W := ⟨2,![3,4,21,8],![3,5,8,18]⟩
def cycle137_2 : CycleData E W := ⟨3,![5,25,15,11,6],![2,8,28,4,14]⟩
def cycle137_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle137_4 : CycleData E W := ⟨3,![13,18,17,24,14],![5,26,16,38,28]⟩
def cycle137_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data137 : PartitionData E W := ⟨6,![cycle137_0,cycle137_1,cycle137_2,cycle137_3,cycle137_4,cycle137_5]⟩
lemma valid_data137 : data137.Valid src137 dst137 Finset.univ := by decide +kernel

def src138 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,28,18,39,38]
def dst138 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle138_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle138_1 : CycleData E W := ⟨3,![2,1,15,22,8],![3,6,4,28,18]⟩
def cycle138_2 : CycleData E W := ⟨2,![3,13,18,9],![3,5,26,16]⟩
def cycle138_3 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle138_4 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle138_5 : CycleData E W := ⟨2,![7,23,19,12],![14,18,39,26]⟩
def cycle138_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data138 : PartitionData E W := ⟨7,![cycle138_0,cycle138_1,cycle138_2,cycle138_3,cycle138_4,cycle138_5,cycle138_6]⟩
lemma valid_data138 : data138.Valid src138 dst138 Finset.univ := by decide +kernel

def src139 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst139 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle139_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle139_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle139_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle139_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle139_4 : CycleData E W := ⟨2,![8,23,17,9],![3,18,38,16]⟩
def cycle139_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,28,8,39]⟩
def data139 : PartitionData E W := ⟨6,![cycle139_0,cycle139_1,cycle139_2,cycle139_3,cycle139_4,cycle139_5]⟩
lemma valid_data139 : data139.Valid src139 dst139 Finset.univ := by decide +kernel

def src140 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst140 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle140_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle140_1 : CycleData E W := ⟨2,![1,20,22,15],![4,6,39,28]⟩
def cycle140_2 : CycleData E W := ⟨2,![2,16,24,8],![3,6,38,18]⟩
def cycle140_3 : CycleData E W := ⟨2,![3,13,18,9],![3,5,26,16]⟩
def cycle140_4 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle140_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle140_6 : CycleData E W := ⟨2,![7,23,19,12],![14,18,39,26]⟩
def data140 : PartitionData E W := ⟨7,![cycle140_0,cycle140_1,cycle140_2,cycle140_3,cycle140_4,cycle140_5,cycle140_6]⟩
lemma valid_data140 : data140.Valid src140 dst140 Finset.univ := by decide +kernel

def src141 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst141 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle141_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle141_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle141_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle141_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle141_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle141_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data141 : PartitionData E W := ⟨6,![cycle141_0,cycle141_1,cycle141_2,cycle141_3,cycle141_4,cycle141_5]⟩
lemma valid_data141 : data141.Valid src141 dst141 Finset.univ := by decide +kernel

def src142 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,28,39,38]
def dst142 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle142_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,16]⟩
def cycle142_1 : CycleData E W := ⟨2,![3,4,21,8],![3,5,8,18]⟩
def cycle142_2 : CycleData E W := ⟨3,![5,25,17,12,6],![2,8,38,26,14]⟩
def cycle142_3 : CycleData E W := ⟨2,![11,7,22,15],![4,14,18,28]⟩
def cycle142_4 : CycleData E W := ⟨3,![13,18,19,23,14],![5,26,16,39,28]⟩
def cycle142_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data142 : PartitionData E W := ⟨6,![cycle142_0,cycle142_1,cycle142_2,cycle142_3,cycle142_4,cycle142_5]⟩
lemma valid_data142 : data142.Valid src142 dst142 Finset.univ := by decide +kernel

def src143 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,38,28,39]
def dst143 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle143_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle143_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle143_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle143_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle143_4 : CycleData E W := ⟨3,![8,21,25,19,9],![3,18,8,39,16]⟩
def cycle143_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data143 : PartitionData E W := ⟨6,![cycle143_0,cycle143_1,cycle143_2,cycle143_3,cycle143_4,cycle143_5]⟩
lemma valid_data143 : data143.Valid src143 dst143 Finset.univ := by decide +kernel

def src144 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,38,39,28]
def dst144 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle144_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,4,6,3,16]⟩
def cycle144_1 : CycleData E W := ⟨2,![3,4,21,8],![3,5,8,18]⟩
def cycle144_2 : CycleData E W := ⟨3,![5,25,15,11,6],![2,8,28,4,14]⟩
def cycle144_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle144_4 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def cycle144_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data144 : PartitionData E W := ⟨6,![cycle144_0,cycle144_1,cycle144_2,cycle144_3,cycle144_4,cycle144_5]⟩
lemma valid_data144 : data144.Valid src144 dst144 Finset.univ := by decide +kernel

def src145 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,39,28,38]
def dst145 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle145_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle145_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle145_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle145_3 : CycleData E W := ⟨3,![21,7,12,17,25],![8,18,14,26,38]⟩
def cycle145_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle145_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data145 : PartitionData E W := ⟨6,![cycle145_0,cycle145_1,cycle145_2,cycle145_3,cycle145_4,cycle145_5]⟩
lemma valid_data145 : data145.Valid src145 dst145 Finset.univ := by decide +kernel

def src146 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,28,18,38,39]
def dst146 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle146_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle146_1 : CycleData E W := ⟨3,![2,1,15,22,8],![3,6,4,28,18]⟩
def cycle146_2 : CycleData E W := ⟨2,![3,13,18,9],![3,5,26,16]⟩
def cycle146_3 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle146_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle146_5 : CycleData E W := ⟨2,![7,23,17,12],![14,18,38,26]⟩
def cycle146_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data146 : PartitionData E W := ⟨7,![cycle146_0,cycle146_1,cycle146_2,cycle146_3,cycle146_4,cycle146_5,cycle146_6]⟩
lemma valid_data146 : data146.Valid src146 dst146 Finset.univ := by decide +kernel

def src147 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst147 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle147_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle147_1 : CycleData E W := ⟨2,![1,16,22,15],![4,6,38,28]⟩
def cycle147_2 : CycleData E W := ⟨2,![2,20,24,8],![3,6,39,18]⟩
def cycle147_3 : CycleData E W := ⟨2,![3,13,18,9],![3,5,26,16]⟩
def cycle147_4 : CycleData E W := ⟨1,![4,21,14],![5,8,28]⟩
def cycle147_5 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle147_6 : CycleData E W := ⟨2,![7,23,17,12],![14,18,38,26]⟩
def data147 : PartitionData E W := ⟨7,![cycle147_0,cycle147_1,cycle147_2,cycle147_3,cycle147_4,cycle147_5,cycle147_6]⟩
lemma valid_data147 : data147.Valid src147 dst147 Finset.univ := by decide +kernel

def src148 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst148 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle148_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle148_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle148_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle148_3 : CycleData E W := ⟨2,![7,24,17,12],![14,18,38,26]⟩
def cycle148_4 : CycleData E W := ⟨2,![8,23,19,9],![3,18,39,16]⟩
def cycle148_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,28,39]⟩
def data148 : PartitionData E W := ⟨6,![cycle148_0,cycle148_1,cycle148_2,cycle148_3,cycle148_4,cycle148_5]⟩
lemma valid_data148 : data148.Valid src148 dst148 Finset.univ := by decide +kernel

def src149 : E → W := ![2,4,6,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst149 : E → W := ![4,6,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle149_0 : CycleData E W := ⟨1,![0,11,6],![2,4,14]⟩
def cycle149_1 : CycleData E W := ⟨3,![2,1,15,14,3],![3,6,4,28,5]⟩
def cycle149_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle149_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle149_4 : CycleData E W := ⟨3,![8,23,24,19,9],![3,18,28,39,16]⟩
def cycle149_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data149 : PartitionData E W := ⟨6,![cycle149_0,cycle149_1,cycle149_2,cycle149_3,cycle149_4,cycle149_5]⟩
lemma valid_data149 : data149.Valid src149 dst149 Finset.univ := by decide +kernel

def lookupB2 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data100 else (if j < 2 then data101 else data102)) else (if j < 4 then data103 else (if j < 5 then data104 else data105))) else (if j < 9 then (if j < 7 then data106 else (if j < 8 then data107 else data108)) else (if j < 10 then data109 else (if j < 11 then data110 else data111)))) else (if j < 18 then (if j < 15 then (if j < 13 then data112 else (if j < 14 then data113 else data114)) else (if j < 16 then data115 else (if j < 17 then data116 else data117))) else (if j < 21 then (if j < 19 then data118 else (if j < 20 then data119 else data120)) else (if j < 23 then (if j < 22 then data121 else data122) else (if j < 24 then data123 else data124))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data125 else (if j < 27 then data126 else data127)) else (if j < 29 then data128 else (if j < 30 then data129 else data130))) else (if j < 34 then (if j < 32 then data131 else (if j < 33 then data132 else data133)) else (if j < 35 then data134 else (if j < 36 then data135 else data136)))) else (if j < 43 then (if j < 40 then (if j < 38 then data137 else (if j < 39 then data138 else data139)) else (if j < 41 then data140 else (if j < 42 then data141 else data142))) else (if j < 46 then (if j < 44 then data143 else (if j < 45 then data144 else data145)) else (if j < 48 then (if j < 47 then data146 else data147) else (if j < 49 then data148 else data149))))))

def srcTableB2 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src100 else (if j < 2 then src101 else src102)) else (if j < 4 then src103 else (if j < 5 then src104 else src105))) else (if j < 9 then (if j < 7 then src106 else (if j < 8 then src107 else src108)) else (if j < 10 then src109 else (if j < 11 then src110 else src111)))) else (if j < 18 then (if j < 15 then (if j < 13 then src112 else (if j < 14 then src113 else src114)) else (if j < 16 then src115 else (if j < 17 then src116 else src117))) else (if j < 21 then (if j < 19 then src118 else (if j < 20 then src119 else src120)) else (if j < 23 then (if j < 22 then src121 else src122) else (if j < 24 then src123 else src124))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src125 else (if j < 27 then src126 else src127)) else (if j < 29 then src128 else (if j < 30 then src129 else src130))) else (if j < 34 then (if j < 32 then src131 else (if j < 33 then src132 else src133)) else (if j < 35 then src134 else (if j < 36 then src135 else src136)))) else (if j < 43 then (if j < 40 then (if j < 38 then src137 else (if j < 39 then src138 else src139)) else (if j < 41 then src140 else (if j < 42 then src141 else src142))) else (if j < 46 then (if j < 44 then src143 else (if j < 45 then src144 else src145)) else (if j < 48 then (if j < 47 then src146 else src147) else (if j < 49 then src148 else src149))))))

def dstTableB2 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst100 else (if j < 2 then dst101 else dst102)) else (if j < 4 then dst103 else (if j < 5 then dst104 else dst105))) else (if j < 9 then (if j < 7 then dst106 else (if j < 8 then dst107 else dst108)) else (if j < 10 then dst109 else (if j < 11 then dst110 else dst111)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst112 else (if j < 14 then dst113 else dst114)) else (if j < 16 then dst115 else (if j < 17 then dst116 else dst117))) else (if j < 21 then (if j < 19 then dst118 else (if j < 20 then dst119 else dst120)) else (if j < 23 then (if j < 22 then dst121 else dst122) else (if j < 24 then dst123 else dst124))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst125 else (if j < 27 then dst126 else dst127)) else (if j < 29 then dst128 else (if j < 30 then dst129 else dst130))) else (if j < 34 then (if j < 32 then dst131 else (if j < 33 then dst132 else dst133)) else (if j < 35 then dst134 else (if j < 36 then dst135 else dst136)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst137 else (if j < 39 then dst138 else dst139)) else (if j < 41 then dst140 else (if j < 42 then dst141 else dst142))) else (if j < 46 then (if j < 44 then dst143 else (if j < 45 then dst144 else dst145)) else (if j < 48 then (if j < 47 then dst146 else dst147) else (if j < 49 then dst148 else dst149))))))

def caseB2 (i : Fin 50) : Cases := ⟨100 + i.val,by have := i.isLt; omega⟩
lemma tableB2_valid (i : Fin 50) :
    (lookupB2 i.val).Valid (srcTableB2 i.val) (dstTableB2 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data100
  · exact valid_data101
  · exact valid_data102
  · exact valid_data103
  · exact valid_data104
  · exact valid_data105
  · exact valid_data106
  · exact valid_data107
  · exact valid_data108
  · exact valid_data109
  · exact valid_data110
  · exact valid_data111
  · exact valid_data112
  · exact valid_data113
  · exact valid_data114
  · exact valid_data115
  · exact valid_data116
  · exact valid_data117
  · exact valid_data118
  · exact valid_data119
  · exact valid_data120
  · exact valid_data121
  · exact valid_data122
  · exact valid_data123
  · exact valid_data124
  · exact valid_data125
  · exact valid_data126
  · exact valid_data127
  · exact valid_data128
  · exact valid_data129
  · exact valid_data130
  · exact valid_data131
  · exact valid_data132
  · exact valid_data133
  · exact valid_data134
  · exact valid_data135
  · exact valid_data136
  · exact valid_data137
  · exact valid_data138
  · exact valid_data139
  · exact valid_data140
  · exact valid_data141
  · exact valid_data142
  · exact valid_data143
  · exact valid_data144
  · exact valid_data145
  · exact valid_data146
  · exact valid_data147
  · exact valid_data148
  · exact valid_data149

lemma srcB2_row : ∀ (i : Fin 50) (e : E),
    srcTableB2 i.val e = caseSource (caseB2 i) e := by decide +kernel

lemma dstB2_row : ∀ (i : Fin 50) (e : E),
    dstTableB2 i.val e = caseTarget (caseB2 i) e := by decide +kernel

lemma sizeB2 : ∀ i : Fin 50, (lookupB2 i.val).size ≤ 5 →
    (lookupB2 i.val).size = 2 ∧
      (⟨caseKey (caseB2 i),caseKey_lt (caseB2 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB2 (i : Fin 50) : Certificate (caseB2 i) := by
  refine ⟨lookupB2 i.val,?_,sizeB2 i⟩
  have hv := tableB2_valid i
  rw [funext (srcB2_row i),funext (dstB2_row i)] at hv
  exact hv
lemma certificateInterval2 : FiniteIntervals.Covers CertificateAt 100 150 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 100 50 (fun i _ => certificateB2 i)
#print axioms certificateInterval2
end Erdos184Work.FiveRows4

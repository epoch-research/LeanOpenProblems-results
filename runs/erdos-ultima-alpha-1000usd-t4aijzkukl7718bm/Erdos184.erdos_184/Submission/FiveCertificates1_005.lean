import Submission.FiveCertificates1Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1000 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1000 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1000_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1000_1 : CycleData E W := ⟨3,![1,13,12,15,8],![3,4,28,26,16]⟩
def cycle1000_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1000_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle1000_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1000_5 : CycleData E W := ⟨2,![6,19,16,11],![14,18,38,26]⟩
def data1000 : PartitionData E W := ⟨6,![cycle1000_0,cycle1000_1,cycle1000_2,cycle1000_3,cycle1000_4,cycle1000_5]⟩
lemma valid_data1000 : data1000.Valid src1000 dst1000 Finset.univ := by decide +kernel

def src1001 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1001 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1001_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1001_1 : CycleData E W := ⟨3,![1,13,12,15,8],![3,4,28,26,16]⟩
def cycle1001_2 : CycleData E W := ⟨2,![2,18,19,7],![3,8,28,18]⟩
def cycle1001_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1001_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1001_5 : CycleData E W := ⟨2,![6,20,16,11],![14,18,38,26]⟩
def data1001 : PartitionData E W := ⟨6,![cycle1001_0,cycle1001_1,cycle1001_2,cycle1001_3,cycle1001_4,cycle1001_5]⟩
lemma valid_data1001 : data1001.Valid src1001 dst1001 Finset.univ := by decide +kernel

def src1002 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1002 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1002_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1002_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1002_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle1002_3 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle1002_4 : CycleData E W := ⟨2,![10,6,19,13],![4,14,18,28]⟩
def cycle1002_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1002 : PartitionData E W := ⟨6,![cycle1002_0,cycle1002_1,cycle1002_2,cycle1002_3,cycle1002_4,cycle1002_5]⟩
lemma valid_data1002 : data1002.Valid src1002 dst1002 Finset.univ := by decide +kernel

def src1003 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1003 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1003_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1003_1 : CycleData E W := ⟨3,![1,13,20,15,8],![3,4,28,38,16]⟩
def cycle1003_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1003_3 : CycleData E W := ⟨2,![3,21,12,17],![6,8,28,26]⟩
def cycle1003_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1003_5 : CycleData E W := ⟨2,![6,19,16,11],![14,18,38,26]⟩
def data1003 : PartitionData E W := ⟨6,![cycle1003_0,cycle1003_1,cycle1003_2,cycle1003_3,cycle1003_4,cycle1003_5]⟩
lemma valid_data1003 : data1003.Valid src1003 dst1003 Finset.univ := by decide +kernel

def src1004 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1004 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1004_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1004_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1004_2 : CycleData E W := ⟨2,![3,21,16,17],![6,8,38,26]⟩
def cycle1004_3 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1004_4 : CycleData E W := ⟨2,![6,19,12,11],![14,18,28,26]⟩
def cycle1004_5 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def data1004 : PartitionData E W := ⟨6,![cycle1004_0,cycle1004_1,cycle1004_2,cycle1004_3,cycle1004_4,cycle1004_5]⟩
lemma valid_data1004 : data1004.Valid src1004 dst1004 Finset.univ := by decide +kernel

def src1005 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1005 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1005_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1005_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1005_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1005_3 : CycleData E W := ⟨2,![4,14,11,5],![2,6,26,14]⟩
def cycle1005_4 : CycleData E W := ⟨2,![10,6,19,13],![4,14,18,28]⟩
def cycle1005_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1005 : PartitionData E W := ⟨6,![cycle1005_0,cycle1005_1,cycle1005_2,cycle1005_3,cycle1005_4,cycle1005_5]⟩
lemma valid_data1005 : data1005.Valid src1005 dst1005 Finset.univ := by decide +kernel

def src1006 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1006 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1006_0 : CycleData E W := ⟨9,![0,13,12,11,6,18,2,8,16,17,4],![2,4,28,26,14,18,8,3,16,38,6]⟩
def cycle1006_1 : CycleData E W := ⟨9,![5,10,1,7,19,20,21,3,14,15,9],![2,14,4,3,18,38,28,8,6,26,16]⟩
def data1006 : PartitionData E W := ⟨2,![cycle1006_0,cycle1006_1]⟩
lemma valid_data1006 : data1006.Valid src1006 dst1006 Finset.univ := by decide +kernel

def src1007 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1007 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1007_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1007_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1007_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1007_3 : CycleData E W := ⟨2,![4,14,15,9],![2,6,26,16]⟩
def cycle1007_4 : CycleData E W := ⟨2,![6,19,12,11],![14,18,28,26]⟩
def cycle1007_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data1007 : PartitionData E W := ⟨6,![cycle1007_0,cycle1007_1,cycle1007_2,cycle1007_3,cycle1007_4,cycle1007_5]⟩
lemma valid_data1007 : data1007.Valid src1007 dst1007 Finset.univ := by decide +kernel

def src1008 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1008 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1008_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1008_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle1008_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1008_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1008_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1008_5 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1008_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1008 : PartitionData E W := ⟨7,![cycle1008_0,cycle1008_1,cycle1008_2,cycle1008_3,cycle1008_4,cycle1008_5,cycle1008_6]⟩
lemma valid_data1008 : data1008.Valid src1008 dst1008 Finset.univ := by decide +kernel

def src1009 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1009 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1009_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1009_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle1009_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1009_3 : CycleData E W := ⟨3,![3,21,12,16,17],![6,8,28,26,38]⟩
def cycle1009_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1009_5 : CycleData E W := ⟨2,![6,19,20,11],![14,18,38,28]⟩
def data1009 : PartitionData E W := ⟨6,![cycle1009_0,cycle1009_1,cycle1009_2,cycle1009_3,cycle1009_4,cycle1009_5]⟩
lemma valid_data1009 : data1009.Valid src1009 dst1009 Finset.univ := by decide +kernel

def src1010 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1010 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1010_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1010_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle1010_2 : CycleData E W := ⟨3,![2,18,11,6,7],![3,8,28,14,18]⟩
def cycle1010_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1010_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1010_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1010 : PartitionData E W := ⟨6,![cycle1010_0,cycle1010_1,cycle1010_2,cycle1010_3,cycle1010_4,cycle1010_5]⟩
lemma valid_data1010 : data1010.Valid src1010 dst1010 Finset.univ := by decide +kernel

def src1011 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1011 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1011_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1011_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1011_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle1011_3 : CycleData E W := ⟨3,![4,17,13,10,5],![2,6,26,4,14]⟩
def cycle1011_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1011_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1011 : PartitionData E W := ⟨6,![cycle1011_0,cycle1011_1,cycle1011_2,cycle1011_3,cycle1011_4,cycle1011_5]⟩
lemma valid_data1011 : data1011.Valid src1011 dst1011 Finset.univ := by decide +kernel

def src1012 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1012 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1012_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1012_1 : CycleData E W := ⟨3,![1,13,16,15,8],![3,4,26,38,16]⟩
def cycle1012_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1012_3 : CycleData E W := ⟨2,![3,21,12,17],![6,8,28,26]⟩
def cycle1012_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1012_5 : CycleData E W := ⟨2,![6,19,20,11],![14,18,38,28]⟩
def data1012 : PartitionData E W := ⟨6,![cycle1012_0,cycle1012_1,cycle1012_2,cycle1012_3,cycle1012_4,cycle1012_5]⟩
lemma valid_data1012 : data1012.Valid src1012 dst1012 Finset.univ := by decide +kernel

def src1013 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1013 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1013_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1013_1 : CycleData E W := ⟨3,![1,13,16,15,8],![3,4,26,38,16]⟩
def cycle1013_2 : CycleData E W := ⟨2,![2,21,20,7],![3,8,38,18]⟩
def cycle1013_3 : CycleData E W := ⟨2,![3,18,12,17],![6,8,28,26]⟩
def cycle1013_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1013_5 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def data1013 : PartitionData E W := ⟨6,![cycle1013_0,cycle1013_1,cycle1013_2,cycle1013_3,cycle1013_4,cycle1013_5]⟩
lemma valid_data1013 : data1013.Valid src1013 dst1013 Finset.univ := by decide +kernel

def src1014 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1014 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1014_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1014_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1014_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1014_3 : CycleData E W := ⟨3,![4,14,13,10,5],![2,6,26,4,14]⟩
def cycle1014_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1014_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1014 : PartitionData E W := ⟨6,![cycle1014_0,cycle1014_1,cycle1014_2,cycle1014_3,cycle1014_4,cycle1014_5]⟩
lemma valid_data1014 : data1014.Valid src1014 dst1014 Finset.univ := by decide +kernel

def src1015 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1015 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1015_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1015_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle1015_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1015_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle1015_4 : CycleData E W := ⟨2,![4,17,16,9],![2,6,38,16]⟩
def cycle1015_5 : CycleData E W := ⟨2,![6,19,20,11],![14,18,38,28]⟩
def data1015 : PartitionData E W := ⟨6,![cycle1015_0,cycle1015_1,cycle1015_2,cycle1015_3,cycle1015_4,cycle1015_5]⟩
lemma valid_data1015 : data1015.Valid src1015 dst1015 Finset.univ := by decide +kernel

def src1016 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1016 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1016_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1016_1 : CycleData E W := ⟨2,![1,13,15,8],![3,4,26,16]⟩
def cycle1016_2 : CycleData E W := ⟨2,![2,21,20,7],![3,8,38,18]⟩
def cycle1016_3 : CycleData E W := ⟨2,![3,18,12,14],![6,8,28,26]⟩
def cycle1016_4 : CycleData E W := ⟨2,![4,17,16,9],![2,6,38,16]⟩
def cycle1016_5 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def data1016 : PartitionData E W := ⟨6,![cycle1016_0,cycle1016_1,cycle1016_2,cycle1016_3,cycle1016_4,cycle1016_5]⟩
lemma valid_data1016 : data1016.Valid src1016 dst1016 Finset.univ := by decide +kernel

def src1017 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1017 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1017_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1017_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1017_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1017_3 : CycleData E W := ⟨3,![4,14,15,11,5],![2,6,16,26,14]⟩
def cycle1017_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1017_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1017 : PartitionData E W := ⟨6,![cycle1017_0,cycle1017_1,cycle1017_2,cycle1017_3,cycle1017_4,cycle1017_5]⟩
lemma valid_data1017 : data1017.Valid src1017 dst1017 Finset.univ := by decide +kernel

def src1018 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1018 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1018_0 : CycleData E W := ⟨2,![0,13,12,5],![2,4,28,14]⟩
def cycle1018_1 : CycleData E W := ⟨2,![1,10,15,8],![3,4,26,16]⟩
def cycle1018_2 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1018_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle1018_4 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1018_5 : CycleData E W := ⟨2,![6,19,16,11],![14,18,38,26]⟩
def data1018 : PartitionData E W := ⟨6,![cycle1018_0,cycle1018_1,cycle1018_2,cycle1018_3,cycle1018_4,cycle1018_5]⟩
lemma valid_data1018 : data1018.Valid src1018 dst1018 Finset.univ := by decide +kernel

def src1019 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1019 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1019_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1019_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1019_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1019_3 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1019_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1019_5 : CycleData E W := ⟨3,![7,20,16,15,8],![3,18,38,26,16]⟩
def data1019 : PartitionData E W := ⟨6,![cycle1019_0,cycle1019_1,cycle1019_2,cycle1019_3,cycle1019_4,cycle1019_5]⟩
lemma valid_data1019 : data1019.Valid src1019 dst1019 Finset.univ := by decide +kernel

def src1020 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1020 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1020_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1020_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1020_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle1020_3 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle1020_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1020_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1020 : PartitionData E W := ⟨6,![cycle1020_0,cycle1020_1,cycle1020_2,cycle1020_3,cycle1020_4,cycle1020_5]⟩
lemma valid_data1020 : data1020.Valid src1020 dst1020 Finset.univ := by decide +kernel

def src1021 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1021 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1021_0 : CycleData E W := ⟨9,![4,3,18,7,8,15,16,10,13,12,5],![2,6,8,18,3,16,38,26,4,28,14]⟩
def cycle1021_1 : CycleData E W := ⟨9,![0,1,2,21,20,19,6,11,17,14,9],![2,4,3,8,28,38,18,14,26,6,16]⟩
def data1021 : PartitionData E W := ⟨2,![cycle1021_0,cycle1021_1]⟩
lemma valid_data1021 : data1021.Valid src1021 dst1021 Finset.univ := by decide +kernel

def src1022 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1022 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1022_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1022_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1022_2 : CycleData E W := ⟨2,![3,21,16,17],![6,8,38,26]⟩
def cycle1022_3 : CycleData E W := ⟨1,![4,14,9],![2,6,16]⟩
def cycle1022_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1022_5 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def data1022 : PartitionData E W := ⟨6,![cycle1022_0,cycle1022_1,cycle1022_2,cycle1022_3,cycle1022_4,cycle1022_5]⟩
lemma valid_data1022 : data1022.Valid src1022 dst1022 Finset.univ := by decide +kernel

def src1023 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1023 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1023_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1023_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle1023_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1023_3 : CycleData E W := ⟨2,![4,14,11,5],![2,6,26,14]⟩
def cycle1023_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1023_5 : CycleData E W := ⟨3,![10,15,16,20,13],![4,26,16,38,28]⟩
def data1023 : PartitionData E W := ⟨6,![cycle1023_0,cycle1023_1,cycle1023_2,cycle1023_3,cycle1023_4,cycle1023_5]⟩
lemma valid_data1023 : data1023.Valid src1023 dst1023 Finset.univ := by decide +kernel

def src1024 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1024 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1024_0 : CycleData E W := ⟨9,![5,12,13,10,14,3,2,7,19,16,9],![2,14,28,4,26,6,8,3,18,38,16]⟩
def cycle1024_1 : CycleData E W := ⟨9,![0,1,8,15,11,6,18,21,20,17,4],![2,4,3,16,26,14,18,8,28,38,6]⟩
def data1024 : PartitionData E W := ⟨2,![cycle1024_0,cycle1024_1]⟩
lemma valid_data1024 : data1024.Valid src1024 dst1024 Finset.univ := by decide +kernel

def src1025 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1025 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1025_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1025_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1025_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1025_3 : CycleData E W := ⟨2,![4,14,15,9],![2,6,26,16]⟩
def cycle1025_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1025_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data1025 : PartitionData E W := ⟨6,![cycle1025_0,cycle1025_1,cycle1025_2,cycle1025_3,cycle1025_4,cycle1025_5]⟩
lemma valid_data1025 : data1025.Valid src1025 dst1025 Finset.univ := by decide +kernel

def src1026 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1026 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1026_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1026_1 : CycleData E W := ⟨3,![1,13,19,18,2],![3,4,28,18,8]⟩
def cycle1026_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1026_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1026_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1026_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1026 : PartitionData E W := ⟨6,![cycle1026_0,cycle1026_1,cycle1026_2,cycle1026_3,cycle1026_4,cycle1026_5]⟩
lemma valid_data1026 : data1026.Valid src1026 dst1026 Finset.univ := by decide +kernel

def src1027 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1027 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1027_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1027_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle1027_2 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle1027_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1027_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1027_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1027 : PartitionData E W := ⟨6,![cycle1027_0,cycle1027_1,cycle1027_2,cycle1027_3,cycle1027_4,cycle1027_5]⟩
lemma valid_data1027 : data1027.Valid src1027 dst1027 Finset.univ := by decide +kernel

def src1028 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1028 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1028_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1028_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1028_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1028_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1028_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1028_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1028 : PartitionData E W := ⟨6,![cycle1028_0,cycle1028_1,cycle1028_2,cycle1028_3,cycle1028_4,cycle1028_5]⟩
lemma valid_data1028 : data1028.Valid src1028 dst1028 Finset.univ := by decide +kernel

def src1029 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1029 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1029_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1029_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1029_2 : CycleData E W := ⟨2,![2,21,15,6],![3,8,38,16]⟩
def cycle1029_3 : CycleData E W := ⟨3,![3,18,8,11,17],![6,8,18,14,26]⟩
def cycle1029_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1029_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1029 : PartitionData E W := ⟨6,![cycle1029_0,cycle1029_1,cycle1029_2,cycle1029_3,cycle1029_4,cycle1029_5]⟩
lemma valid_data1029 : data1029.Valid src1029 dst1029 Finset.univ := by decide +kernel

def src1030 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1030 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1030_0 : CycleData E W := ⟨9,![4,3,18,8,7,1,13,12,16,15,5],![2,6,8,18,14,3,4,28,26,38,16]⟩
def cycle1030_1 : CycleData E W := ⟨9,![0,10,11,17,14,6,2,21,20,19,9],![2,4,14,26,6,16,3,8,28,38,18]⟩
def data1030 : PartitionData E W := ⟨2,![cycle1030_0,cycle1030_1]⟩
lemma valid_data1030 : data1030.Valid src1030 dst1030 Finset.univ := by decide +kernel

def src1031 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1031 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1031_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1031_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1031_2 : CycleData E W := ⟨2,![2,21,15,6],![3,8,38,16]⟩
def cycle1031_3 : CycleData E W := ⟨2,![3,18,12,17],![6,8,28,26]⟩
def cycle1031_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1031_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data1031 : PartitionData E W := ⟨6,![cycle1031_0,cycle1031_1,cycle1031_2,cycle1031_3,cycle1031_4,cycle1031_5]⟩
lemma valid_data1031 : data1031.Valid src1031 dst1031 Finset.univ := by decide +kernel

def src1032 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1032 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1032_0 : CycleData E W := ⟨9,![5,16,17,14,12,13,10,7,2,18,9],![2,16,38,6,26,28,4,14,3,8,18]⟩
def cycle1032_1 : CycleData E W := ⟨9,![0,1,6,15,11,8,19,20,21,3,4],![2,4,3,16,26,14,18,28,38,8,6]⟩
def data1032 : PartitionData E W := ⟨2,![cycle1032_0,cycle1032_1]⟩
lemma valid_data1032 : data1032.Valid src1032 dst1032 Finset.univ := by decide +kernel

def src1033 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1033 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1033_0 : CycleData E W := ⟨9,![5,16,17,14,12,13,10,7,2,18,9],![2,16,38,6,26,28,4,14,3,8,18]⟩
def cycle1033_1 : CycleData E W := ⟨9,![0,1,6,15,11,8,19,20,21,3,4],![2,4,3,16,26,14,18,38,28,8,6]⟩
def data1033 : PartitionData E W := ⟨2,![cycle1033_0,cycle1033_1]⟩
lemma valid_data1033 : data1033.Valid src1033 dst1033 Finset.univ := by decide +kernel

def src1034 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1034 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1034_0 : CycleData E W := ⟨9,![4,17,16,15,12,18,2,1,10,8,9],![2,6,38,16,26,28,8,3,4,14,18]⟩
def cycle1034_1 : CycleData E W := ⟨9,![0,13,19,20,21,3,14,11,7,6,5],![2,4,28,18,38,8,6,26,14,3,16]⟩
def data1034 : PartitionData E W := ⟨2,![cycle1034_0,cycle1034_1]⟩
lemma valid_data1034 : data1034.Valid src1034 dst1034 Finset.univ := by decide +kernel

def src1035 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1035 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1035_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1035_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle1035_2 : CycleData E W := ⟨3,![2,18,19,11,7],![3,8,18,28,14]⟩
def cycle1035_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1035_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1035_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1035 : PartitionData E W := ⟨6,![cycle1035_0,cycle1035_1,cycle1035_2,cycle1035_3,cycle1035_4,cycle1035_5]⟩
lemma valid_data1035 : data1035.Valid src1035 dst1035 Finset.univ := by decide +kernel

def src1036 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1036 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1036_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1036_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle1036_2 : CycleData E W := ⟨2,![2,21,11,7],![3,8,28,14]⟩
def cycle1036_3 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle1036_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1036_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1036 : PartitionData E W := ⟨6,![cycle1036_0,cycle1036_1,cycle1036_2,cycle1036_3,cycle1036_4,cycle1036_5]⟩
lemma valid_data1036 : data1036.Valid src1036 dst1036 Finset.univ := by decide +kernel

def src1037 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1037 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1037_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1037_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle1037_2 : CycleData E W := ⟨2,![2,18,11,7],![3,8,28,14]⟩
def cycle1037_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1037_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1037_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1037 : PartitionData E W := ⟨6,![cycle1037_0,cycle1037_1,cycle1037_2,cycle1037_3,cycle1037_4,cycle1037_5]⟩
lemma valid_data1037 : data1037.Valid src1037 dst1037 Finset.univ := by decide +kernel

def src1038 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1038 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1038_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle1038_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1038_2 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle1038_3 : CycleData E W := ⟨3,![5,15,21,18,9],![2,16,38,8,18]⟩
def cycle1038_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1038_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1038 : PartitionData E W := ⟨6,![cycle1038_0,cycle1038_1,cycle1038_2,cycle1038_3,cycle1038_4,cycle1038_5]⟩
lemma valid_data1038 : data1038.Valid src1038 dst1038 Finset.univ := by decide +kernel

def src1039 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1039 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1039_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle1039_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1039_2 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle1039_3 : CycleData E W := ⟨2,![5,15,19,9],![2,16,38,18]⟩
def cycle1039_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1039_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1039 : PartitionData E W := ⟨6,![cycle1039_0,cycle1039_1,cycle1039_2,cycle1039_3,cycle1039_4,cycle1039_5]⟩
lemma valid_data1039 : data1039.Valid src1039 dst1039 Finset.univ := by decide +kernel

def src1040 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1040 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1040_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle1040_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1040_2 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle1040_3 : CycleData E W := ⟨2,![5,15,20,9],![2,16,38,18]⟩
def cycle1040_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1040_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1040 : PartitionData E W := ⟨6,![cycle1040_0,cycle1040_1,cycle1040_2,cycle1040_3,cycle1040_4,cycle1040_5]⟩
lemma valid_data1040 : data1040.Valid src1040 dst1040 Finset.univ := by decide +kernel

def src1041 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1041 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1041_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle1041_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1041_2 : CycleData E W := ⟨3,![5,6,2,18,9],![2,16,3,8,18]⟩
def cycle1041_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1041_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1041_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1041 : PartitionData E W := ⟨6,![cycle1041_0,cycle1041_1,cycle1041_2,cycle1041_3,cycle1041_4,cycle1041_5]⟩
lemma valid_data1041 : data1041.Valid src1041 dst1041 Finset.univ := by decide +kernel

def src1042 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1042 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1042_0 : CycleData E W := ⟨9,![5,16,17,14,12,11,10,1,2,18,9],![2,16,38,6,26,28,14,4,3,8,18]⟩
def cycle1042_1 : CycleData E W := ⟨9,![0,13,15,6,7,8,19,20,21,3,4],![2,4,26,16,3,14,18,38,28,8,6]⟩
def data1042 : PartitionData E W := ⟨2,![cycle1042_0,cycle1042_1]⟩
lemma valid_data1042 : data1042.Valid src1042 dst1042 Finset.univ := by decide +kernel

def src1043 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1043 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1043_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle1043_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1043_2 : CycleData E W := ⟨3,![2,18,12,15,6],![3,8,28,26,16]⟩
def cycle1043_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1043_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle1043_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data1043 : PartitionData E W := ⟨6,![cycle1043_0,cycle1043_1,cycle1043_2,cycle1043_3,cycle1043_4,cycle1043_5]⟩
lemma valid_data1043 : data1043.Valid src1043 dst1043 Finset.univ := by decide +kernel

def src1044 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1044 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1044_0 : CycleData E W := ⟨3,![0,1,2,18,9],![2,4,3,8,18]⟩
def cycle1044_1 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1044_2 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1044_3 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1044_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle1044_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1044 : PartitionData E W := ⟨6,![cycle1044_0,cycle1044_1,cycle1044_2,cycle1044_3,cycle1044_4,cycle1044_5]⟩
lemma valid_data1044 : data1044.Valid src1044 dst1044 Finset.univ := by decide +kernel

def src1045 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1045 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1045_0 : CycleData E W := ⟨9,![4,17,16,10,13,12,8,18,2,6,5],![2,6,38,26,4,28,14,18,8,3,16]⟩
def cycle1045_1 : CycleData E W := ⟨9,![0,1,7,11,15,14,3,21,20,19,9],![2,4,3,14,26,16,6,8,28,38,18]⟩
def data1045 : PartitionData E W := ⟨2,![cycle1045_0,cycle1045_1]⟩
lemma valid_data1045 : data1045.Valid src1045 dst1045 Finset.univ := by decide +kernel

def src1046 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1046 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1046_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1046_1 : CycleData E W := ⟨2,![1,10,15,6],![3,4,26,16]⟩
def cycle1046_2 : CycleData E W := ⟨2,![2,18,12,7],![3,8,28,14]⟩
def cycle1046_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1046_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1046_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data1046 : PartitionData E W := ⟨6,![cycle1046_0,cycle1046_1,cycle1046_2,cycle1046_3,cycle1046_4,cycle1046_5]⟩
lemma valid_data1046 : data1046.Valid src1046 dst1046 Finset.univ := by decide +kernel

def src1047 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1047 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1047_0 : CycleData E W := ⟨9,![4,14,15,16,11,12,13,1,2,18,9],![2,6,16,38,26,14,28,4,3,8,18]⟩
def cycle1047_1 : CycleData E W := ⟨9,![0,10,17,3,21,20,19,8,7,6,5],![2,4,26,6,8,38,28,18,14,3,16]⟩
def data1047 : PartitionData E W := ⟨2,![cycle1047_0,cycle1047_1]⟩
lemma valid_data1047 : data1047.Valid src1047 dst1047 Finset.univ := by decide +kernel

def src1048 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1048 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1048_0 : CycleData E W := ⟨9,![4,14,15,16,11,12,13,1,2,18,9],![2,6,16,38,26,14,28,4,3,8,18]⟩
def cycle1048_1 : CycleData E W := ⟨9,![0,10,17,3,21,20,19,8,7,6,5],![2,4,26,6,8,28,38,18,14,3,16]⟩
def data1048 : PartitionData E W := ⟨2,![cycle1048_0,cycle1048_1]⟩
lemma valid_data1048 : data1048.Valid src1048 dst1048 Finset.univ := by decide +kernel

def src1049 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1049 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1049_0 : CycleData E W := ⟨9,![4,3,18,13,10,16,15,6,7,8,9],![2,6,8,28,4,26,38,16,3,14,18]⟩
def cycle1049_1 : CycleData E W := ⟨9,![0,1,2,21,20,19,12,11,17,14,5],![2,4,3,8,38,18,28,14,26,6,16]⟩
def data1049 : PartitionData E W := ⟨2,![cycle1049_0,cycle1049_1]⟩
lemma valid_data1049 : data1049.Valid src1049 dst1049 Finset.univ := by decide +kernel

def src1050 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1050 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1050_0 : CycleData E W := ⟨9,![5,16,17,14,10,13,12,7,2,18,9],![2,16,38,6,26,4,28,14,3,8,18]⟩
def cycle1050_1 : CycleData E W := ⟨9,![0,1,6,15,11,8,19,20,21,3,4],![2,4,3,16,26,14,18,28,38,8,6]⟩
def data1050 : PartitionData E W := ⟨2,![cycle1050_0,cycle1050_1]⟩
lemma valid_data1050 : data1050.Valid src1050 dst1050 Finset.univ := by decide +kernel

def src1051 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1051 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1051_0 : CycleData E W := ⟨9,![5,16,17,14,10,13,12,7,2,18,9],![2,16,38,6,26,4,28,14,3,8,18]⟩
def cycle1051_1 : CycleData E W := ⟨9,![0,1,6,15,11,8,19,20,21,3,4],![2,4,3,16,26,14,18,38,28,8,6]⟩
def data1051 : PartitionData E W := ⟨2,![cycle1051_0,cycle1051_1]⟩
lemma valid_data1051 : data1051.Valid src1051 dst1051 Finset.univ := by decide +kernel

def src1052 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1052 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1052_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle1052_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle1052_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1052_3 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle1052_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1052_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1052 : PartitionData E W := ⟨6,![cycle1052_0,cycle1052_1,cycle1052_2,cycle1052_3,cycle1052_4,cycle1052_5]⟩
lemma valid_data1052 : data1052.Valid src1052 dst1052 Finset.univ := by decide +kernel

def src1053 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1053 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1053_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1053_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1053_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1053_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1053_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1053_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1053_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1053 : PartitionData E W := ⟨7,![cycle1053_0,cycle1053_1,cycle1053_2,cycle1053_3,cycle1053_4,cycle1053_5,cycle1053_6]⟩
lemma valid_data1053 : data1053.Valid src1053 dst1053 Finset.univ := by decide +kernel

def src1054 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1054 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1054_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1054_1 : CycleData E W := ⟨3,![2,21,13,10,7],![3,8,28,4,14]⟩
def cycle1054_2 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle1054_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1054_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1054_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1054 : PartitionData E W := ⟨6,![cycle1054_0,cycle1054_1,cycle1054_2,cycle1054_3,cycle1054_4,cycle1054_5]⟩
lemma valid_data1054 : data1054.Valid src1054 dst1054 Finset.univ := by decide +kernel

def src1055 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1055 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1055_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1055_1 : CycleData E W := ⟨3,![2,18,13,10,7],![3,8,28,4,14]⟩
def cycle1055_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1055_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1055_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1055_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1055 : PartitionData E W := ⟨6,![cycle1055_0,cycle1055_1,cycle1055_2,cycle1055_3,cycle1055_4,cycle1055_5]⟩
lemma valid_data1055 : data1055.Valid src1055 dst1055 Finset.univ := by decide +kernel

def src1056 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1056 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1056_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1056_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1056_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1056_3 : CycleData E W := ⟨3,![4,3,21,15,5],![2,6,8,38,16]⟩
def cycle1056_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1056_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1056 : PartitionData E W := ⟨6,![cycle1056_0,cycle1056_1,cycle1056_2,cycle1056_3,cycle1056_4,cycle1056_5]⟩
lemma valid_data1056 : data1056.Valid src1056 dst1056 Finset.univ := by decide +kernel

def src1057 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1057 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1057_0 : CycleData E W := ⟨3,![0,13,20,19,9],![2,4,28,38,18]⟩
def cycle1057_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1057_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1057_3 : CycleData E W := ⟨2,![3,21,12,17],![6,8,28,26]⟩
def cycle1057_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1057_5 : CycleData E W := ⟨2,![6,15,16,11],![14,16,38,26]⟩
def data1057 : PartitionData E W := ⟨6,![cycle1057_0,cycle1057_1,cycle1057_2,cycle1057_3,cycle1057_4,cycle1057_5]⟩
lemma valid_data1057 : data1057.Valid src1057 dst1057 Finset.univ := by decide +kernel

def src1058 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1058 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1058_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1058_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1058_2 : CycleData E W := ⟨2,![2,21,20,8],![3,8,38,18]⟩
def cycle1058_3 : CycleData E W := ⟨2,![3,18,12,17],![6,8,28,26]⟩
def cycle1058_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1058_5 : CycleData E W := ⟨2,![6,15,16,11],![14,16,38,26]⟩
def data1058 : PartitionData E W := ⟨6,![cycle1058_0,cycle1058_1,cycle1058_2,cycle1058_3,cycle1058_4,cycle1058_5]⟩
lemma valid_data1058 : data1058.Valid src1058 dst1058 Finset.univ := by decide +kernel

def src1059 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1059 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1059_0 : CycleData E W := ⟨3,![0,13,12,14,4],![2,4,28,26,6]⟩
def cycle1059_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1059_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1059_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1059_4 : CycleData E W := ⟨3,![5,16,20,19,9],![2,16,38,28,18]⟩
def cycle1059_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1059 : PartitionData E W := ⟨6,![cycle1059_0,cycle1059_1,cycle1059_2,cycle1059_3,cycle1059_4,cycle1059_5]⟩
lemma valid_data1059 : data1059.Valid src1059 dst1059 Finset.univ := by decide +kernel

def src1060 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1060 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1060_0 : CycleData E W := ⟨3,![0,13,12,14,4],![2,4,28,26,6]⟩
def cycle1060_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1060_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1060_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle1060_4 : CycleData E W := ⟨2,![5,16,19,9],![2,16,38,18]⟩
def cycle1060_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1060 : PartitionData E W := ⟨6,![cycle1060_0,cycle1060_1,cycle1060_2,cycle1060_3,cycle1060_4,cycle1060_5]⟩
lemma valid_data1060 : data1060.Valid src1060 dst1060 Finset.univ := by decide +kernel

def src1061 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1061 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1061_0 : CycleData E W := ⟨3,![0,13,12,14,4],![2,4,28,26,6]⟩
def cycle1061_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1061_2 : CycleData E W := ⟨2,![2,18,19,8],![3,8,28,18]⟩
def cycle1061_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1061_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle1061_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1061 : PartitionData E W := ⟨6,![cycle1061_0,cycle1061_1,cycle1061_2,cycle1061_3,cycle1061_4,cycle1061_5]⟩
lemma valid_data1061 : data1061.Valid src1061 dst1061 Finset.univ := by decide +kernel

def src1062 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1062 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1062_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1062_1 : CycleData E W := ⟨3,![2,18,19,11,7],![3,8,18,28,14]⟩
def cycle1062_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1062_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1062_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1062_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1062 : PartitionData E W := ⟨6,![cycle1062_0,cycle1062_1,cycle1062_2,cycle1062_3,cycle1062_4,cycle1062_5]⟩
lemma valid_data1062 : data1062.Valid src1062 dst1062 Finset.univ := by decide +kernel

def src1063 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1063 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1063_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1063_1 : CycleData E W := ⟨2,![2,21,11,7],![3,8,28,14]⟩
def cycle1063_2 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle1063_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1063_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1063_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1063 : PartitionData E W := ⟨6,![cycle1063_0,cycle1063_1,cycle1063_2,cycle1063_3,cycle1063_4,cycle1063_5]⟩
lemma valid_data1063 : data1063.Valid src1063 dst1063 Finset.univ := by decide +kernel

def src1064 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1064 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1064_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1064_1 : CycleData E W := ⟨2,![2,18,11,7],![3,8,28,14]⟩
def cycle1064_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1064_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1064_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1064_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1064 : PartitionData E W := ⟨6,![cycle1064_0,cycle1064_1,cycle1064_2,cycle1064_3,cycle1064_4,cycle1064_5]⟩
lemma valid_data1064 : data1064.Valid src1064 dst1064 Finset.univ := by decide +kernel

def src1065 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1065 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1065_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle1065_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1065_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1065_3 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle1065_4 : CycleData E W := ⟨3,![5,6,11,19,9],![2,16,14,28,18]⟩
def cycle1065_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1065 : PartitionData E W := ⟨6,![cycle1065_0,cycle1065_1,cycle1065_2,cycle1065_3,cycle1065_4,cycle1065_5]⟩
lemma valid_data1065 : data1065.Valid src1065 dst1065 Finset.univ := by decide +kernel

def src1066 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1066 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1066_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle1066_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1066_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1066_3 : CycleData E W := ⟨3,![3,21,11,6,14],![6,8,28,14,16]⟩
def cycle1066_4 : CycleData E W := ⟨2,![5,15,19,9],![2,16,38,18]⟩
def cycle1066_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1066 : PartitionData E W := ⟨6,![cycle1066_0,cycle1066_1,cycle1066_2,cycle1066_3,cycle1066_4,cycle1066_5]⟩
lemma valid_data1066 : data1066.Valid src1066 dst1066 Finset.univ := by decide +kernel

def src1067 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1067 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1067_0 : CycleData E W := ⟨9,![4,3,18,11,6,15,16,13,1,8,9],![2,6,8,28,14,16,38,26,4,3,18]⟩
def cycle1067_1 : CycleData E W := ⟨9,![0,10,7,2,21,20,19,12,17,14,5],![2,4,14,3,8,38,18,28,26,6,16]⟩
def data1067 : PartitionData E W := ⟨2,![cycle1067_0,cycle1067_1]⟩
lemma valid_data1067 : data1067.Valid src1067 dst1067 Finset.univ := by decide +kernel

def src1068 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1068 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1068_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle1068_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1068_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1068_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1068_4 : CycleData E W := ⟨3,![5,6,11,19,9],![2,16,14,28,18]⟩
def cycle1068_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1068 : PartitionData E W := ⟨6,![cycle1068_0,cycle1068_1,cycle1068_2,cycle1068_3,cycle1068_4,cycle1068_5]⟩
lemma valid_data1068 : data1068.Valid src1068 dst1068 Finset.univ := by decide +kernel

def src1069 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1069 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1069_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle1069_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1069_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1069_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle1069_4 : CycleData E W := ⟨2,![5,16,19,9],![2,16,38,18]⟩
def cycle1069_5 : CycleData E W := ⟨2,![6,15,12,11],![14,16,26,28]⟩
def data1069 : PartitionData E W := ⟨6,![cycle1069_0,cycle1069_1,cycle1069_2,cycle1069_3,cycle1069_4,cycle1069_5]⟩
lemma valid_data1069 : data1069.Valid src1069 dst1069 Finset.univ := by decide +kernel

def src1070 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1070 : E → W := ![4,3,8,6,2,16,14,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1070_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle1070_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1070_2 : CycleData E W := ⟨2,![2,18,19,8],![3,8,28,18]⟩
def cycle1070_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1070_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle1070_5 : CycleData E W := ⟨2,![6,15,12,11],![14,16,26,28]⟩
def data1070 : PartitionData E W := ⟨6,![cycle1070_0,cycle1070_1,cycle1070_2,cycle1070_3,cycle1070_4,cycle1070_5]⟩
lemma valid_data1070 : data1070.Valid src1070 dst1070 Finset.univ := by decide +kernel

def src1071 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1071 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1071_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1071_1 : CycleData E W := ⟨3,![2,18,19,12,7],![3,8,18,28,14]⟩
def cycle1071_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1071_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1071_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1071_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1071 : PartitionData E W := ⟨6,![cycle1071_0,cycle1071_1,cycle1071_2,cycle1071_3,cycle1071_4,cycle1071_5]⟩
lemma valid_data1071 : data1071.Valid src1071 dst1071 Finset.univ := by decide +kernel

def src1072 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1072 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1072_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1072_1 : CycleData E W := ⟨2,![2,21,12,7],![3,8,28,14]⟩
def cycle1072_2 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle1072_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1072_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1072_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1072 : PartitionData E W := ⟨6,![cycle1072_0,cycle1072_1,cycle1072_2,cycle1072_3,cycle1072_4,cycle1072_5]⟩
lemma valid_data1072 : data1072.Valid src1072 dst1072 Finset.univ := by decide +kernel

def src1073 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1073 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1073_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle1073_1 : CycleData E W := ⟨2,![2,18,12,7],![3,8,28,14]⟩
def cycle1073_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1073_3 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1073_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1073_5 : CycleData E W := ⟨3,![10,16,20,19,13],![4,26,38,18,28]⟩
def data1073 : PartitionData E W := ⟨6,![cycle1073_0,cycle1073_1,cycle1073_2,cycle1073_3,cycle1073_4,cycle1073_5]⟩
lemma valid_data1073 : data1073.Valid src1073 dst1073 Finset.univ := by decide +kernel

def src1074 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1074 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1074_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1074_1 : CycleData E W := ⟨2,![1,10,11,7],![3,4,26,14]⟩
def cycle1074_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1074_3 : CycleData E W := ⟨2,![3,21,16,17],![6,8,38,26]⟩
def cycle1074_4 : CycleData E W := ⟨1,![4,14,5],![2,6,16]⟩
def cycle1074_5 : CycleData E W := ⟨2,![6,15,20,12],![14,16,38,28]⟩
def data1074 : PartitionData E W := ⟨6,![cycle1074_0,cycle1074_1,cycle1074_2,cycle1074_3,cycle1074_4,cycle1074_5]⟩
lemma valid_data1074 : data1074.Valid src1074 dst1074 Finset.univ := by decide +kernel

def src1075 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1075 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1075_0 : CycleData E W := ⟨9,![4,3,18,8,1,13,12,11,16,15,5],![2,6,8,18,3,4,28,14,26,38,16]⟩
def cycle1075_1 : CycleData E W := ⟨9,![0,10,17,14,6,7,2,21,20,19,9],![2,4,26,6,16,14,3,8,28,38,18]⟩
def data1075 : PartitionData E W := ⟨2,![cycle1075_0,cycle1075_1]⟩
lemma valid_data1075 : data1075.Valid src1075 dst1075 Finset.univ := by decide +kernel

def src1076 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1076 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1076_0 : CycleData E W := ⟨9,![4,3,18,12,6,15,16,10,1,8,9],![2,6,8,28,14,16,38,26,4,3,18]⟩
def cycle1076_1 : CycleData E W := ⟨9,![0,13,19,20,21,2,7,11,17,14,5],![2,4,28,18,38,8,3,14,26,6,16]⟩
def data1076 : PartitionData E W := ⟨2,![cycle1076_0,cycle1076_1]⟩
lemma valid_data1076 : data1076.Valid src1076 dst1076 Finset.univ := by decide +kernel

def src1077 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1077 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1077_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle1077_1 : CycleData E W := ⟨2,![1,13,12,7],![3,4,28,14]⟩
def cycle1077_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1077_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1077_4 : CycleData E W := ⟨3,![5,16,20,19,9],![2,16,38,28,18]⟩
def cycle1077_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1077 : PartitionData E W := ⟨6,![cycle1077_0,cycle1077_1,cycle1077_2,cycle1077_3,cycle1077_4,cycle1077_5]⟩
lemma valid_data1077 : data1077.Valid src1077 dst1077 Finset.univ := by decide +kernel

def src1078 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1078 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1078_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle1078_1 : CycleData E W := ⟨2,![1,13,12,7],![3,4,28,14]⟩
def cycle1078_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle1078_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle1078_4 : CycleData E W := ⟨2,![5,16,19,9],![2,16,38,18]⟩
def cycle1078_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1078 : PartitionData E W := ⟨6,![cycle1078_0,cycle1078_1,cycle1078_2,cycle1078_3,cycle1078_4,cycle1078_5]⟩
lemma valid_data1078 : data1078.Valid src1078 dst1078 Finset.univ := by decide +kernel

def src1079 : E → W := ![2,4,3,8,6,2,16,14,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1079 : E → W := ![4,3,8,6,2,16,14,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1079_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle1079_1 : CycleData E W := ⟨2,![1,13,12,7],![3,4,28,14]⟩
def cycle1079_2 : CycleData E W := ⟨2,![2,18,19,8],![3,8,28,18]⟩
def cycle1079_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle1079_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle1079_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1079 : PartitionData E W := ⟨6,![cycle1079_0,cycle1079_1,cycle1079_2,cycle1079_3,cycle1079_4,cycle1079_5]⟩
lemma valid_data1079 : data1079.Valid src1079 dst1079 Finset.univ := by decide +kernel

def src1080 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1080 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1080_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1080_1 : CycleData E W := ⟨3,![1,14,8,19,13],![4,6,16,18,28]⟩
def cycle1080_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1080_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1080_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1080_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1080 : PartitionData E W := ⟨6,![cycle1080_0,cycle1080_1,cycle1080_2,cycle1080_3,cycle1080_4,cycle1080_5]⟩
lemma valid_data1080 : data1080.Valid src1080 dst1080 Finset.univ := by decide +kernel

def src1081 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1081 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1081_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1081_1 : CycleData E W := ⟨3,![3,21,13,10,6],![3,8,28,4,14]⟩
def cycle1081_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1081_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1081_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1081_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1081 : PartitionData E W := ⟨6,![cycle1081_0,cycle1081_1,cycle1081_2,cycle1081_3,cycle1081_4,cycle1081_5]⟩
lemma valid_data1081 : data1081.Valid src1081 dst1081 Finset.univ := by decide +kernel

def src1082 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1082 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1082_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1082_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1082_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1082_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1082_4 : CycleData E W := ⟨2,![14,8,20,17],![6,16,18,38]⟩
def cycle1082_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1082 : PartitionData E W := ⟨6,![cycle1082_0,cycle1082_1,cycle1082_2,cycle1082_3,cycle1082_4,cycle1082_5]⟩
lemma valid_data1082 : data1082.Valid src1082 dst1082 Finset.univ := by decide +kernel

def src1083 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1083 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1083_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1083_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1083_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1083_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1083_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1083_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1083 : PartitionData E W := ⟨6,![cycle1083_0,cycle1083_1,cycle1083_2,cycle1083_3,cycle1083_4,cycle1083_5]⟩
lemma valid_data1083 : data1083.Valid src1083 dst1083 Finset.univ := by decide +kernel

def src1084 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1084 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1084_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1084_1 : CycleData E W := ⟨3,![3,21,13,10,6],![3,8,28,4,14]⟩
def cycle1084_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1084_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1084_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1084_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1084 : PartitionData E W := ⟨6,![cycle1084_0,cycle1084_1,cycle1084_2,cycle1084_3,cycle1084_4,cycle1084_5]⟩
lemma valid_data1084 : data1084.Valid src1084 dst1084 Finset.univ := by decide +kernel

def src1085 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1085 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1085_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1085_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1085_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1085_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1085_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1085_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1085 : PartitionData E W := ⟨6,![cycle1085_0,cycle1085_1,cycle1085_2,cycle1085_3,cycle1085_4,cycle1085_5]⟩
lemma valid_data1085 : data1085.Valid src1085 dst1085 Finset.univ := by decide +kernel

def src1086 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1086 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1086_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1086_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1086_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1086_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1086_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1086_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1086 : PartitionData E W := ⟨6,![cycle1086_0,cycle1086_1,cycle1086_2,cycle1086_3,cycle1086_4,cycle1086_5]⟩
lemma valid_data1086 : data1086.Valid src1086 dst1086 Finset.univ := by decide +kernel

def src1087 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1087 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1087_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1087_1 : CycleData E W := ⟨3,![3,21,13,10,6],![3,8,28,4,14]⟩
def cycle1087_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1087_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1087_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1087_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1087 : PartitionData E W := ⟨6,![cycle1087_0,cycle1087_1,cycle1087_2,cycle1087_3,cycle1087_4,cycle1087_5]⟩
lemma valid_data1087 : data1087.Valid src1087 dst1087 Finset.univ := by decide +kernel

def src1088 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1088 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1088_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1088_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1088_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1088_3 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1088_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1088_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1088 : PartitionData E W := ⟨6,![cycle1088_0,cycle1088_1,cycle1088_2,cycle1088_3,cycle1088_4,cycle1088_5]⟩
lemma valid_data1088 : data1088.Valid src1088 dst1088 Finset.univ := by decide +kernel

def src1089 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1089 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1089_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1089_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1089_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1089_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1089_4 : CycleData E W := ⟨2,![7,8,19,11],![14,16,18,28]⟩
def cycle1089_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1089 : PartitionData E W := ⟨6,![cycle1089_0,cycle1089_1,cycle1089_2,cycle1089_3,cycle1089_4,cycle1089_5]⟩
lemma valid_data1089 : data1089.Valid src1089 dst1089 Finset.univ := by decide +kernel

def src1090 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1090 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1090_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1090_1 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1090_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1090_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1090_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1090_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1090 : PartitionData E W := ⟨6,![cycle1090_0,cycle1090_1,cycle1090_2,cycle1090_3,cycle1090_4,cycle1090_5]⟩
lemma valid_data1090 : data1090.Valid src1090 dst1090 Finset.univ := by decide +kernel

def src1091 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1091 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1091_0 : CycleData E W := ⟨9,![0,1,17,16,12,18,3,6,7,8,9],![2,4,6,38,26,28,8,3,14,16,18]⟩
def cycle1091_1 : CycleData E W := ⟨9,![4,21,20,19,11,10,13,15,14,2,5],![2,8,38,18,28,14,4,26,16,6,3]⟩
def data1091 : PartitionData E W := ⟨2,![cycle1091_0,cycle1091_1]⟩
lemma valid_data1091 : data1091.Valid src1091 dst1091 Finset.univ := by decide +kernel

def src1092 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1092 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1092_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1092_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1092_2 : CycleData E W := ⟨3,![2,14,15,21,3],![3,6,16,38,8]⟩
def cycle1092_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1092_4 : CycleData E W := ⟨2,![7,8,19,11],![14,16,18,28]⟩
def cycle1092_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1092 : PartitionData E W := ⟨6,![cycle1092_0,cycle1092_1,cycle1092_2,cycle1092_3,cycle1092_4,cycle1092_5]⟩
lemma valid_data1092 : data1092.Valid src1092 dst1092 Finset.univ := by decide +kernel

def src1093 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1093 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1093_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1093_1 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1093_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1093_3 : CycleData E W := ⟨3,![10,7,14,17,13],![4,14,16,6,26]⟩
def cycle1093_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1093_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1093 : PartitionData E W := ⟨6,![cycle1093_0,cycle1093_1,cycle1093_2,cycle1093_3,cycle1093_4,cycle1093_5]⟩
lemma valid_data1093 : data1093.Valid src1093 dst1093 Finset.univ := by decide +kernel

def src1094 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1094 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1094_0 : CycleData E W := ⟨3,![0,10,11,19,9],![2,4,14,28,18]⟩
def cycle1094_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1094_2 : CycleData E W := ⟨2,![2,14,7,6],![3,6,16,14]⟩
def cycle1094_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1094_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1094_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1094 : PartitionData E W := ⟨6,![cycle1094_0,cycle1094_1,cycle1094_2,cycle1094_3,cycle1094_4,cycle1094_5]⟩
lemma valid_data1094 : data1094.Valid src1094 dst1094 Finset.univ := by decide +kernel

def src1095 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1095 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1095_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1095_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1095_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1095_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1095_4 : CycleData E W := ⟨2,![7,15,12,11],![14,16,26,28]⟩
def cycle1095_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1095 : PartitionData E W := ⟨6,![cycle1095_0,cycle1095_1,cycle1095_2,cycle1095_3,cycle1095_4,cycle1095_5]⟩
lemma valid_data1095 : data1095.Valid src1095 dst1095 Finset.univ := by decide +kernel

def src1096 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1096 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1096_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1096_1 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1096_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1096_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1096_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1096_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1096 : PartitionData E W := ⟨6,![cycle1096_0,cycle1096_1,cycle1096_2,cycle1096_3,cycle1096_4,cycle1096_5]⟩
lemma valid_data1096 : data1096.Valid src1096 dst1096 Finset.univ := by decide +kernel

def src1097 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1097 : E → W := ![4,6,3,8,2,3,14,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1097_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1097_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1097_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1097_3 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1097_4 : CycleData E W := ⟨2,![7,15,12,11],![14,16,26,28]⟩
def cycle1097_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1097 : PartitionData E W := ⟨6,![cycle1097_0,cycle1097_1,cycle1097_2,cycle1097_3,cycle1097_4,cycle1097_5]⟩
lemma valid_data1097 : data1097.Valid src1097 dst1097 Finset.univ := by decide +kernel

def src1098 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1098 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1098_0 : CycleData E W := ⟨9,![4,18,8,7,12,13,10,16,17,2,5],![2,8,18,16,14,28,4,26,38,6,3]⟩
def cycle1098_1 : CycleData E W := ⟨9,![0,1,14,15,11,6,3,21,20,19,9],![2,4,6,16,26,14,3,8,38,28,18]⟩
def data1098 : PartitionData E W := ⟨2,![cycle1098_0,cycle1098_1]⟩
lemma valid_data1098 : data1098.Valid src1098 dst1098 Finset.univ := by decide +kernel

def src1099 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1099 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1099_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1099_1 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1099_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1099_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1099_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1099_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1099 : PartitionData E W := ⟨6,![cycle1099_0,cycle1099_1,cycle1099_2,cycle1099_3,cycle1099_4,cycle1099_5]⟩
lemma valid_data1099 : data1099.Valid src1099 dst1099 Finset.univ := by decide +kernel

def src1100 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1100 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1100_0 : CycleData E W := ⟨9,![0,10,16,17,2,3,18,12,7,8,9],![2,4,26,38,6,3,8,28,14,16,18]⟩
def cycle1100_1 : CycleData E W := ⟨9,![4,21,20,19,13,1,14,15,11,6,5],![2,8,38,18,28,4,6,16,26,14,3]⟩
def data1100 : PartitionData E W := ⟨2,![cycle1100_0,cycle1100_1]⟩
lemma valid_data1100 : data1100.Valid src1100 dst1100 Finset.univ := by decide +kernel

def src1101 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1101 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1101_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1101_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1101_2 : CycleData E W := ⟨2,![2,14,7,6],![3,6,16,14]⟩
def cycle1101_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1101_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1101_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1101 : PartitionData E W := ⟨6,![cycle1101_0,cycle1101_1,cycle1101_2,cycle1101_3,cycle1101_4,cycle1101_5]⟩
lemma valid_data1101 : data1101.Valid src1101 dst1101 Finset.univ := by decide +kernel

def src1102 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1102 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1102_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1102_1 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1102_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1102_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1102_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1102_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1102 : PartitionData E W := ⟨6,![cycle1102_0,cycle1102_1,cycle1102_2,cycle1102_3,cycle1102_4,cycle1102_5]⟩
lemma valid_data1102 : data1102.Valid src1102 dst1102 Finset.univ := by decide +kernel

def src1103 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1103 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1103_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle1103_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1103_2 : CycleData E W := ⟨2,![2,14,7,6],![3,6,16,14]⟩
def cycle1103_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1103_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1103_5 : CycleData E W := ⟨3,![18,12,11,16,21],![8,28,14,26,38]⟩
def data1103 : PartitionData E W := ⟨6,![cycle1103_0,cycle1103_1,cycle1103_2,cycle1103_3,cycle1103_4,cycle1103_5]⟩
lemma valid_data1103 : data1103.Valid src1103 dst1103 Finset.univ := by decide +kernel

def src1104 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1104 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1104_0 : CycleData E W := ⟨3,![0,13,12,6,5],![2,4,28,14,3]⟩
def cycle1104_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1104_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1104_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1104_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1104_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1104 : PartitionData E W := ⟨6,![cycle1104_0,cycle1104_1,cycle1104_2,cycle1104_3,cycle1104_4,cycle1104_5]⟩
lemma valid_data1104 : data1104.Valid src1104 dst1104 Finset.univ := by decide +kernel

def src1105 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1105 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1105_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1105_1 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1105_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1105_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1105_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1105_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data1105 : PartitionData E W := ⟨6,![cycle1105_0,cycle1105_1,cycle1105_2,cycle1105_3,cycle1105_4,cycle1105_5]⟩
lemma valid_data1105 : data1105.Valid src1105 dst1105 Finset.univ := by decide +kernel

def src1106 : E → W := ![2,4,6,3,8,2,3,14,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1106 : E → W := ![4,6,3,8,2,3,14,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1106_0 : CycleData E W := ⟨3,![0,13,12,6,5],![2,4,28,14,3]⟩
def cycle1106_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1106_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1106_3 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1106_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1106_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1106 : PartitionData E W := ⟨6,![cycle1106_0,cycle1106_1,cycle1106_2,cycle1106_3,cycle1106_4,cycle1106_5]⟩
lemma valid_data1106 : data1106.Valid src1106 dst1106 Finset.univ := by decide +kernel

def src1107 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1107 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1107_0 : CycleData E W := ⟨9,![4,18,8,14,17,16,12,13,10,6,5],![2,8,18,16,6,38,26,28,4,14,3]⟩
def cycle1107_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,11,15,9],![2,4,6,3,8,38,28,18,14,26,16]⟩
def data1107 : PartitionData E W := ⟨2,![cycle1107_0,cycle1107_1]⟩
lemma valid_data1107 : data1107.Valid src1107 dst1107 Finset.univ := by decide +kernel

def src1108 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1108 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1108_0 : CycleData E W := ⟨9,![4,18,8,14,17,16,12,13,10,6,5],![2,8,18,16,6,38,26,28,4,14,3]⟩
def cycle1108_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,11,15,9],![2,4,6,3,8,28,38,18,14,26,16]⟩
def data1108 : PartitionData E W := ⟨2,![cycle1108_0,cycle1108_1]⟩
lemma valid_data1108 : data1108.Valid src1108 dst1108 Finset.univ := by decide +kernel

def src1109 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1109 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1109_0 : CycleData E W := ⟨9,![0,1,17,16,12,18,3,6,7,8,9],![2,4,6,38,26,28,8,3,14,18,16]⟩
def cycle1109_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,11,15,14,2,5],![2,8,38,18,28,4,14,26,16,6,3]⟩
def data1109 : PartitionData E W := ⟨2,![cycle1109_0,cycle1109_1]⟩
lemma valid_data1109 : data1109.Valid src1109 dst1109 Finset.univ := by decide +kernel

def src1110 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1110 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1110_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1110_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1110_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1110_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1110_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1110_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1110 : PartitionData E W := ⟨6,![cycle1110_0,cycle1110_1,cycle1110_2,cycle1110_3,cycle1110_4,cycle1110_5]⟩
lemma valid_data1110 : data1110.Valid src1110 dst1110 Finset.univ := by decide +kernel

def src1111 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1111 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1111_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1111_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1111_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1111_3 : CycleData E W := ⟨3,![10,7,18,21,13],![4,14,18,8,28]⟩
def cycle1111_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1111_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1111 : PartitionData E W := ⟨6,![cycle1111_0,cycle1111_1,cycle1111_2,cycle1111_3,cycle1111_4,cycle1111_5]⟩
lemma valid_data1111 : data1111.Valid src1111 dst1111 Finset.univ := by decide +kernel

def src1112 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1112 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1112_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1112_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1112_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1112_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1112_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1112_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1112 : PartitionData E W := ⟨6,![cycle1112_0,cycle1112_1,cycle1112_2,cycle1112_3,cycle1112_4,cycle1112_5]⟩
lemma valid_data1112 : data1112.Valid src1112 dst1112 Finset.univ := by decide +kernel

def src1113 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1113 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1113_0 : CycleData E W := ⟨9,![0,13,12,11,6,2,17,16,8,18,4],![2,4,28,26,14,3,6,38,16,18,8]⟩
def cycle1113_1 : CycleData E W := ⟨9,![5,3,21,20,19,7,10,1,14,15,9],![2,3,8,38,28,18,14,4,6,26,16]⟩
def data1113 : PartitionData E W := ⟨2,![cycle1113_0,cycle1113_1]⟩
lemma valid_data1113 : data1113.Valid src1113 dst1113 Finset.univ := by decide +kernel

def src1114 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1114 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1114_0 : CycleData E W := ⟨9,![0,13,12,11,6,2,17,16,8,18,4],![2,4,28,26,14,3,6,38,16,18,8]⟩
def cycle1114_1 : CycleData E W := ⟨9,![5,3,21,20,19,7,10,1,14,15,9],![2,3,8,28,38,18,14,4,6,26,16]⟩
def data1114 : PartitionData E W := ⟨2,![cycle1114_0,cycle1114_1]⟩
lemma valid_data1114 : data1114.Valid src1114 dst1114 Finset.univ := by decide +kernel

def src1115 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1115 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1115_0 : CycleData E W := ⟨9,![0,1,17,16,8,7,11,12,18,3,5],![2,4,6,38,16,18,14,26,28,8,3]⟩
def cycle1115_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,6,2,14,15,9],![2,8,38,18,28,4,14,3,6,26,16]⟩
def data1115 : PartitionData E W := ⟨2,![cycle1115_0,cycle1115_1]⟩
lemma valid_data1115 : data1115.Valid src1115 dst1115 Finset.univ := by decide +kernel

def src1116 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1116 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1116_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1116_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1116_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1116_3 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle1116_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1116_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1116 : PartitionData E W := ⟨6,![cycle1116_0,cycle1116_1,cycle1116_2,cycle1116_3,cycle1116_4,cycle1116_5]⟩
lemma valid_data1116 : data1116.Valid src1116 dst1116 Finset.univ := by decide +kernel

def src1117 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1117 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1117_0 : CycleData E W := ⟨2,![0,13,15,9],![2,4,26,16]⟩
def cycle1117_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1117_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1117_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1117_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1117_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1117 : PartitionData E W := ⟨6,![cycle1117_0,cycle1117_1,cycle1117_2,cycle1117_3,cycle1117_4,cycle1117_5]⟩
lemma valid_data1117 : data1117.Valid src1117 dst1117 Finset.univ := by decide +kernel

def src1118 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1118 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1118_0 : CycleData E W := ⟨2,![0,13,15,9],![2,4,26,16]⟩
def cycle1118_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1118_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1118_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1118_4 : CycleData E W := ⟨2,![14,8,20,17],![6,16,18,38]⟩
def cycle1118_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1118 : PartitionData E W := ⟨6,![cycle1118_0,cycle1118_1,cycle1118_2,cycle1118_3,cycle1118_4,cycle1118_5]⟩
lemma valid_data1118 : data1118.Valid src1118 dst1118 Finset.univ := by decide +kernel

def src1119 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1119 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1119_0 : CycleData E W := ⟨3,![0,10,6,3,4],![2,4,14,3,8]⟩
def cycle1119_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1119_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1119_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1119_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1119_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1119 : PartitionData E W := ⟨6,![cycle1119_0,cycle1119_1,cycle1119_2,cycle1119_3,cycle1119_4,cycle1119_5]⟩
lemma valid_data1119 : data1119.Valid src1119 dst1119 Finset.univ := by decide +kernel

def src1120 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1120 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1120_0 : CycleData E W := ⟨3,![0,10,6,3,4],![2,4,14,3,8]⟩
def cycle1120_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1120_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1120_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1120_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1120_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1120 : PartitionData E W := ⟨6,![cycle1120_0,cycle1120_1,cycle1120_2,cycle1120_3,cycle1120_4,cycle1120_5]⟩
lemma valid_data1120 : data1120.Valid src1120 dst1120 Finset.univ := by decide +kernel

def src1121 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1121 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1121_0 : CycleData E W := ⟨3,![0,10,6,3,4],![2,4,14,3,8]⟩
def cycle1121_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1121_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1121_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1121_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1121_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1121 : PartitionData E W := ⟨6,![cycle1121_0,cycle1121_1,cycle1121_2,cycle1121_3,cycle1121_4,cycle1121_5]⟩
lemma valid_data1121 : data1121.Valid src1121 dst1121 Finset.univ := by decide +kernel

def src1122 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1122 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1122_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1122_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1122_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1122_3 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle1122_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1122_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1122 : PartitionData E W := ⟨6,![cycle1122_0,cycle1122_1,cycle1122_2,cycle1122_3,cycle1122_4,cycle1122_5]⟩
lemma valid_data1122 : data1122.Valid src1122 dst1122 Finset.univ := by decide +kernel

def src1123 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1123 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1123_0 : CycleData E W := ⟨2,![0,13,15,9],![2,4,26,16]⟩
def cycle1123_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1123_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1123_3 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1123_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1123_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1123 : PartitionData E W := ⟨6,![cycle1123_0,cycle1123_1,cycle1123_2,cycle1123_3,cycle1123_4,cycle1123_5]⟩
lemma valid_data1123 : data1123.Valid src1123 dst1123 Finset.univ := by decide +kernel

def src1124 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1124 : E → W := ![4,6,3,8,2,3,14,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1124_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,3]⟩
def cycle1124_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1124_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1124_3 : CycleData E W := ⟨3,![4,18,12,15,9],![2,8,28,26,16]⟩
def cycle1124_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1124_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1124 : PartitionData E W := ⟨6,![cycle1124_0,cycle1124_1,cycle1124_2,cycle1124_3,cycle1124_4,cycle1124_5]⟩
lemma valid_data1124 : data1124.Valid src1124 dst1124 Finset.univ := by decide +kernel

def src1125 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1125 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1125_0 : CycleData E W := ⟨9,![4,18,8,14,17,16,10,13,12,6,5],![2,8,18,16,6,38,26,4,28,14,3]⟩
def cycle1125_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,11,15,9],![2,4,6,3,8,38,28,18,14,26,16]⟩
def data1125 : PartitionData E W := ⟨2,![cycle1125_0,cycle1125_1]⟩
lemma valid_data1125 : data1125.Valid src1125 dst1125 Finset.univ := by decide +kernel

def src1126 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1126 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1126_0 : CycleData E W := ⟨9,![4,18,8,14,17,16,10,13,12,6,5],![2,8,18,16,6,38,26,4,28,14,3]⟩
def cycle1126_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,11,15,9],![2,4,6,3,8,28,38,18,14,26,16]⟩
def data1126 : PartitionData E W := ⟨2,![cycle1126_0,cycle1126_1]⟩
lemma valid_data1126 : data1126.Valid src1126 dst1126 Finset.univ := by decide +kernel

def src1127 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1127 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1127_0 : CycleData E W := ⟨9,![0,10,16,17,2,3,18,12,7,8,9],![2,4,26,38,6,3,8,28,14,18,16]⟩
def cycle1127_1 : CycleData E W := ⟨9,![4,21,20,19,13,1,14,15,11,6,5],![2,8,38,18,28,4,6,16,26,14,3]⟩
def data1127 : PartitionData E W := ⟨2,![cycle1127_0,cycle1127_1]⟩
lemma valid_data1127 : data1127.Valid src1127 dst1127 Finset.univ := by decide +kernel

def src1128 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1128 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1128_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1128_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1128_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1128_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1128_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1128_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1128 : PartitionData E W := ⟨6,![cycle1128_0,cycle1128_1,cycle1128_2,cycle1128_3,cycle1128_4,cycle1128_5]⟩
lemma valid_data1128 : data1128.Valid src1128 dst1128 Finset.univ := by decide +kernel

def src1129 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1129 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1129_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1129_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1129_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1129_3 : CycleData E W := ⟨2,![18,7,12,21],![8,18,14,28]⟩
def cycle1129_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1129_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1129 : PartitionData E W := ⟨6,![cycle1129_0,cycle1129_1,cycle1129_2,cycle1129_3,cycle1129_4,cycle1129_5]⟩
lemma valid_data1129 : data1129.Valid src1129 dst1129 Finset.univ := by decide +kernel

def src1130 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1130 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1130_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1130_1 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1130_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1130_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1130_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1130_5 : CycleData E W := ⟨3,![10,16,21,18,13],![4,26,38,8,28]⟩
def data1130 : PartitionData E W := ⟨6,![cycle1130_0,cycle1130_1,cycle1130_2,cycle1130_3,cycle1130_4,cycle1130_5]⟩
lemma valid_data1130 : data1130.Valid src1130 dst1130 Finset.univ := by decide +kernel

def src1131 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1131 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1131_0 : CycleData E W := ⟨2,![0,10,15,9],![2,4,26,16]⟩
def cycle1131_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1131_2 : CycleData E W := ⟨2,![2,14,11,6],![3,6,26,14]⟩
def cycle1131_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1131_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1131_5 : CycleData E W := ⟨2,![18,8,16,21],![8,18,16,38]⟩
def data1131 : PartitionData E W := ⟨6,![cycle1131_0,cycle1131_1,cycle1131_2,cycle1131_3,cycle1131_4,cycle1131_5]⟩
lemma valid_data1131 : data1131.Valid src1131 dst1131 Finset.univ := by decide +kernel

def src1132 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1132 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1132_0 : CycleData E W := ⟨2,![0,10,15,9],![2,4,26,16]⟩
def cycle1132_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1132_2 : CycleData E W := ⟨2,![2,14,11,6],![3,6,26,14]⟩
def cycle1132_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1132_4 : CycleData E W := ⟨2,![18,7,12,21],![8,18,14,28]⟩
def cycle1132_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1132 : PartitionData E W := ⟨6,![cycle1132_0,cycle1132_1,cycle1132_2,cycle1132_3,cycle1132_4,cycle1132_5]⟩
lemma valid_data1132 : data1132.Valid src1132 dst1132 Finset.univ := by decide +kernel

def src1133 : E → W := ![2,4,6,3,8,2,3,14,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1133 : E → W := ![4,6,3,8,2,3,14,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1133_0 : CycleData E W := ⟨2,![0,10,15,9],![2,4,26,16]⟩
def cycle1133_1 : CycleData E W := ⟨3,![1,17,21,18,13],![4,6,38,8,28]⟩
def cycle1133_2 : CycleData E W := ⟨2,![2,14,11,6],![3,6,26,14]⟩
def cycle1133_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1133_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1133_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1133 : PartitionData E W := ⟨6,![cycle1133_0,cycle1133_1,cycle1133_2,cycle1133_3,cycle1133_4,cycle1133_5]⟩
lemma valid_data1133 : data1133.Valid src1133 dst1133 Finset.univ := by decide +kernel

def src1134 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1134 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1134_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1134_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1134_2 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle1134_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1134_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1134_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1134 : PartitionData E W := ⟨6,![cycle1134_0,cycle1134_1,cycle1134_2,cycle1134_3,cycle1134_4,cycle1134_5]⟩
lemma valid_data1134 : data1134.Valid src1134 dst1134 Finset.univ := by decide +kernel

def src1135 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1135 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1135_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1135_1 : CycleData E W := ⟨2,![2,17,19,6],![3,6,38,18]⟩
def cycle1135_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1135_3 : CycleData E W := ⟨3,![10,7,18,21,13],![4,14,18,8,28]⟩
def cycle1135_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1135_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1135 : PartitionData E W := ⟨6,![cycle1135_0,cycle1135_1,cycle1135_2,cycle1135_3,cycle1135_4,cycle1135_5]⟩
lemma valid_data1135 : data1135.Valid src1135 dst1135 Finset.univ := by decide +kernel

def src1136 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1136 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1136_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1136_1 : CycleData E W := ⟨2,![2,17,20,6],![3,6,38,18]⟩
def cycle1136_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1136_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1136_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1136_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1136 : PartitionData E W := ⟨6,![cycle1136_0,cycle1136_1,cycle1136_2,cycle1136_3,cycle1136_4,cycle1136_5]⟩
lemma valid_data1136 : data1136.Valid src1136 dst1136 Finset.univ := by decide +kernel

def src1137 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1137 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1137_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1137_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1137_2 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1137_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1137_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1137_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1137 : PartitionData E W := ⟨6,![cycle1137_0,cycle1137_1,cycle1137_2,cycle1137_3,cycle1137_4,cycle1137_5]⟩
lemma valid_data1137 : data1137.Valid src1137 dst1137 Finset.univ := by decide +kernel

def src1138 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1138 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1138_0 : CycleData E W := ⟨2,![0,13,21,4],![2,4,28,8]⟩
def cycle1138_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1138_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1138_3 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1138_4 : CycleData E W := ⟨2,![7,19,15,8],![14,18,38,16]⟩
def cycle1138_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1138 : PartitionData E W := ⟨6,![cycle1138_0,cycle1138_1,cycle1138_2,cycle1138_3,cycle1138_4,cycle1138_5]⟩
lemma valid_data1138 : data1138.Valid src1138 dst1138 Finset.univ := by decide +kernel

def src1139 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1139 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1139_0 : CycleData E W := ⟨9,![0,1,2,6,7,8,15,16,12,18,4],![2,4,6,3,18,14,16,38,26,28,8]⟩
def cycle1139_1 : CycleData E W := ⟨9,![5,3,21,20,19,13,10,11,17,14,9],![2,3,8,38,18,28,4,14,26,6,16]⟩
def data1139 : PartitionData E W := ⟨2,![cycle1139_0,cycle1139_1]⟩
lemma valid_data1139 : data1139.Valid src1139 dst1139 Finset.univ := by decide +kernel

def src1140 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1140 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1140_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1140_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1140_2 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1140_3 : CycleData E W := ⟨2,![10,7,19,13],![4,14,18,28]⟩
def cycle1140_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1140_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1140 : PartitionData E W := ⟨6,![cycle1140_0,cycle1140_1,cycle1140_2,cycle1140_3,cycle1140_4,cycle1140_5]⟩
lemma valid_data1140 : data1140.Valid src1140 dst1140 Finset.univ := by decide +kernel

def src1141 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1141 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1141_0 : CycleData E W := ⟨9,![0,13,12,11,8,16,17,2,6,18,4],![2,4,28,26,14,16,38,6,3,18,8]⟩
def cycle1141_1 : CycleData E W := ⟨9,![5,3,21,20,19,7,10,1,14,15,9],![2,3,8,28,38,18,14,4,6,26,16]⟩
def data1141 : PartitionData E W := ⟨2,![cycle1141_0,cycle1141_1]⟩
lemma valid_data1141 : data1141.Valid src1141 dst1141 Finset.univ := by decide +kernel

def src1142 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1142 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1142_0 : CycleData E W := ⟨9,![0,13,18,3,6,7,11,14,17,16,9],![2,4,28,8,3,18,14,26,6,38,16]⟩
def cycle1142_1 : CycleData E W := ⟨9,![4,21,20,19,12,15,8,10,1,2,5],![2,8,38,18,28,26,16,14,4,6,3]⟩
def data1142 : PartitionData E W := ⟨2,![cycle1142_0,cycle1142_1]⟩
lemma valid_data1142 : data1142.Valid src1142 dst1142 Finset.univ := by decide +kernel

def src1143 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1143 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1143_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1143_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1143_2 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle1143_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1143_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle1143_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1143 : PartitionData E W := ⟨6,![cycle1143_0,cycle1143_1,cycle1143_2,cycle1143_3,cycle1143_4,cycle1143_5]⟩
lemma valid_data1143 : data1143.Valid src1143 dst1143 Finset.univ := by decide +kernel

def src1144 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1144 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1144_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1144_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1144_2 : CycleData E W := ⟨2,![2,17,19,6],![3,6,38,18]⟩
def cycle1144_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1144_4 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1144_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1144 : PartitionData E W := ⟨6,![cycle1144_0,cycle1144_1,cycle1144_2,cycle1144_3,cycle1144_4,cycle1144_5]⟩
lemma valid_data1144 : data1144.Valid src1144 dst1144 Finset.univ := by decide +kernel

def src1145 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1145 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1145_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1145_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1145_2 : CycleData E W := ⟨2,![2,17,20,6],![3,6,38,18]⟩
def cycle1145_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1145_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1145_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1145 : PartitionData E W := ⟨6,![cycle1145_0,cycle1145_1,cycle1145_2,cycle1145_3,cycle1145_4,cycle1145_5]⟩
lemma valid_data1145 : data1145.Valid src1145 dst1145 Finset.univ := by decide +kernel

def src1146 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1146 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1146_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1146_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1146_2 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1146_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1146_4 : CycleData E W := ⟨3,![10,8,14,17,13],![4,14,16,6,26]⟩
def cycle1146_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1146 : PartitionData E W := ⟨6,![cycle1146_0,cycle1146_1,cycle1146_2,cycle1146_3,cycle1146_4,cycle1146_5]⟩
lemma valid_data1146 : data1146.Valid src1146 dst1146 Finset.univ := by decide +kernel

def src1147 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1147 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1147_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1147_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1147_2 : CycleData E W := ⟨3,![2,14,15,19,6],![3,6,16,38,18]⟩
def cycle1147_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1147_4 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1147_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1147 : PartitionData E W := ⟨6,![cycle1147_0,cycle1147_1,cycle1147_2,cycle1147_3,cycle1147_4,cycle1147_5]⟩
lemma valid_data1147 : data1147.Valid src1147 dst1147 Finset.univ := by decide +kernel

def src1148 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1148 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1148_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1148_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1148_2 : CycleData E W := ⟨3,![2,14,15,20,6],![3,6,16,38,18]⟩
def cycle1148_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1148_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1148_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1148 : PartitionData E W := ⟨6,![cycle1148_0,cycle1148_1,cycle1148_2,cycle1148_3,cycle1148_4,cycle1148_5]⟩
lemma valid_data1148 : data1148.Valid src1148 dst1148 Finset.univ := by decide +kernel

def src1149 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1149 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1149_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1149_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1149_2 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1149_3 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1149_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle1149_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1149 : PartitionData E W := ⟨6,![cycle1149_0,cycle1149_1,cycle1149_2,cycle1149_3,cycle1149_4,cycle1149_5]⟩
lemma valid_data1149 : data1149.Valid src1149 dst1149 Finset.univ := by decide +kernel

def src1150 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1150 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1150_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1150_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1150_2 : CycleData E W := ⟨2,![2,17,19,6],![3,6,38,18]⟩
def cycle1150_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1150_4 : CycleData E W := ⟨2,![18,7,11,21],![8,18,14,28]⟩
def cycle1150_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1150 : PartitionData E W := ⟨6,![cycle1150_0,cycle1150_1,cycle1150_2,cycle1150_3,cycle1150_4,cycle1150_5]⟩
lemma valid_data1150 : data1150.Valid src1150 dst1150 Finset.univ := by decide +kernel

def src1151 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1151 : E → W := ![4,6,3,8,2,3,18,14,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1151_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,16]⟩
def cycle1151_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1151_2 : CycleData E W := ⟨2,![2,17,20,6],![3,6,38,18]⟩
def cycle1151_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1151_4 : CycleData E W := ⟨1,![7,19,11],![14,18,28]⟩
def cycle1151_5 : CycleData E W := ⟨3,![18,12,15,16,21],![8,28,26,16,38]⟩
def data1151 : PartitionData E W := ⟨6,![cycle1151_0,cycle1151_1,cycle1151_2,cycle1151_3,cycle1151_4,cycle1151_5]⟩
lemma valid_data1151 : data1151.Valid src1151 dst1151 Finset.univ := by decide +kernel

def src1152 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1152 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1152_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1152_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1152_2 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle1152_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1152_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1152_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1152 : PartitionData E W := ⟨6,![cycle1152_0,cycle1152_1,cycle1152_2,cycle1152_3,cycle1152_4,cycle1152_5]⟩
lemma valid_data1152 : data1152.Valid src1152 dst1152 Finset.univ := by decide +kernel

def src1153 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1153 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1153_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1153_1 : CycleData E W := ⟨2,![2,17,19,6],![3,6,38,18]⟩
def cycle1153_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1153_3 : CycleData E W := ⟨2,![18,7,12,21],![8,18,14,28]⟩
def cycle1153_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1153_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1153 : PartitionData E W := ⟨6,![cycle1153_0,cycle1153_1,cycle1153_2,cycle1153_3,cycle1153_4,cycle1153_5]⟩
lemma valid_data1153 : data1153.Valid src1153 dst1153 Finset.univ := by decide +kernel

def src1154 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1154 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1154_0 : CycleData E W := ⟨2,![0,1,14,9],![2,4,6,16]⟩
def cycle1154_1 : CycleData E W := ⟨2,![2,17,20,6],![3,6,38,18]⟩
def cycle1154_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1154_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1154_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1154_5 : CycleData E W := ⟨3,![10,16,21,18,13],![4,26,38,8,28]⟩
def data1154 : PartitionData E W := ⟨6,![cycle1154_0,cycle1154_1,cycle1154_2,cycle1154_3,cycle1154_4,cycle1154_5]⟩
lemma valid_data1154 : data1154.Valid src1154 dst1154 Finset.univ := by decide +kernel

def src1155 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1155 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1155_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1155_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1155_2 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1155_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1155_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1155_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1155 : PartitionData E W := ⟨6,![cycle1155_0,cycle1155_1,cycle1155_2,cycle1155_3,cycle1155_4,cycle1155_5]⟩
lemma valid_data1155 : data1155.Valid src1155 dst1155 Finset.univ := by decide +kernel

def src1156 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1156 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1156_0 : CycleData E W := ⟨2,![0,13,21,4],![2,4,28,8]⟩
def cycle1156_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1156_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1156_3 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1156_4 : CycleData E W := ⟨2,![7,19,15,8],![14,18,38,16]⟩
def cycle1156_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1156 : PartitionData E W := ⟨6,![cycle1156_0,cycle1156_1,cycle1156_2,cycle1156_3,cycle1156_4,cycle1156_5]⟩
lemma valid_data1156 : data1156.Valid src1156 dst1156 Finset.univ := by decide +kernel

def src1157 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1157 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1157_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle1157_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1157_2 : CycleData E W := ⟨2,![5,2,14,9],![2,3,6,16]⟩
def cycle1157_3 : CycleData E W := ⟨2,![3,21,20,6],![3,8,38,18]⟩
def cycle1157_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1157_5 : CycleData E W := ⟨2,![8,15,16,11],![14,16,38,26]⟩
def data1157 : PartitionData E W := ⟨6,![cycle1157_0,cycle1157_1,cycle1157_2,cycle1157_3,cycle1157_4,cycle1157_5]⟩
lemma valid_data1157 : data1157.Valid src1157 dst1157 Finset.univ := by decide +kernel

def src1158 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1158 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1158_0 : CycleData E W := ⟨2,![0,1,2,5],![2,4,6,3]⟩
def cycle1158_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1158_2 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1158_3 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1158_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1158_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data1158 : PartitionData E W := ⟨6,![cycle1158_0,cycle1158_1,cycle1158_2,cycle1158_3,cycle1158_4,cycle1158_5]⟩
lemma valid_data1158 : data1158.Valid src1158 dst1158 Finset.univ := by decide +kernel

def src1159 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1159 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1159_0 : CycleData E W := ⟨3,![0,13,20,16,9],![2,4,28,38,16]⟩
def cycle1159_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1159_2 : CycleData E W := ⟨2,![2,17,19,6],![3,6,38,18]⟩
def cycle1159_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1159_4 : CycleData E W := ⟨2,![18,7,12,21],![8,18,14,28]⟩
def cycle1159_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data1159 : PartitionData E W := ⟨6,![cycle1159_0,cycle1159_1,cycle1159_2,cycle1159_3,cycle1159_4,cycle1159_5]⟩
lemma valid_data1159 : data1159.Valid src1159 dst1159 Finset.univ := by decide +kernel

def src1160 : E → W := ![2,4,6,3,8,2,3,18,14,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1160 : E → W := ![4,6,3,8,2,3,18,14,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1160_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle1160_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1160_2 : CycleData E W := ⟨3,![5,2,17,16,9],![2,3,6,38,16]⟩
def cycle1160_3 : CycleData E W := ⟨2,![3,21,20,6],![3,8,38,18]⟩
def cycle1160_4 : CycleData E W := ⟨1,![7,19,12],![14,18,28]⟩
def cycle1160_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data1160 : PartitionData E W := ⟨6,![cycle1160_0,cycle1160_1,cycle1160_2,cycle1160_3,cycle1160_4,cycle1160_5]⟩
lemma valid_data1160 : data1160.Valid src1160 dst1160 Finset.univ := by decide +kernel

def src1161 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1161 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1161_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1161_1 : CycleData E W := ⟨3,![1,14,8,19,13],![4,6,16,18,28]⟩
def cycle1161_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1161_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1161_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1161_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1161 : PartitionData E W := ⟨6,![cycle1161_0,cycle1161_1,cycle1161_2,cycle1161_3,cycle1161_4,cycle1161_5]⟩
lemma valid_data1161 : data1161.Valid src1161 dst1161 Finset.univ := by decide +kernel

def src1162 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1162 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1162_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1162_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1162_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1162_3 : CycleData E W := ⟨3,![3,21,12,11,6],![3,8,28,26,14]⟩
def cycle1162_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1162_5 : CycleData E W := ⟨2,![8,19,16,15],![16,18,38,26]⟩
def data1162 : PartitionData E W := ⟨6,![cycle1162_0,cycle1162_1,cycle1162_2,cycle1162_3,cycle1162_4,cycle1162_5]⟩
lemma valid_data1162 : data1162.Valid src1162 dst1162 Finset.univ := by decide +kernel

def src1163 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1163 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1163_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,10,6,7,8,9],![2,8,28,26,38,6,4,14,3,16,18]⟩
def cycle1163_1 : CycleData E W := ⟨9,![0,13,19,20,21,3,2,14,15,11,5],![2,4,28,18,38,8,3,6,16,26,14]⟩
def data1163 : PartitionData E W := ⟨2,![cycle1163_0,cycle1163_1]⟩
lemma valid_data1163 : data1163.Valid src1163 dst1163 Finset.univ := by decide +kernel

def src1164 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1164 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1164_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1164_1 : CycleData E W := ⟨2,![1,17,12,13],![4,6,26,28]⟩
def cycle1164_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1164_3 : CycleData E W := ⟨3,![3,21,16,11,6],![3,8,38,26,14]⟩
def cycle1164_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1164_5 : CycleData E W := ⟨2,![8,19,20,15],![16,18,28,38]⟩
def data1164 : PartitionData E W := ⟨6,![cycle1164_0,cycle1164_1,cycle1164_2,cycle1164_3,cycle1164_4,cycle1164_5]⟩
lemma valid_data1164 : data1164.Valid src1164 dst1164 Finset.univ := by decide +kernel

def src1165 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1165 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1165_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1165_1 : CycleData E W := ⟨2,![1,17,12,13],![4,6,26,28]⟩
def cycle1165_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1165_3 : CycleData E W := ⟨4,![3,21,20,16,11,6],![3,8,28,38,26,14]⟩
def cycle1165_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1165_5 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def data1165 : PartitionData E W := ⟨6,![cycle1165_0,cycle1165_1,cycle1165_2,cycle1165_3,cycle1165_4,cycle1165_5]⟩
lemma valid_data1165 : data1165.Valid src1165 dst1165 Finset.univ := by decide +kernel

def src1166 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1166 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1166_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1166_1 : CycleData E W := ⟨2,![1,17,12,13],![4,6,26,28]⟩
def cycle1166_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1166_3 : CycleData E W := ⟨3,![3,21,16,11,6],![3,8,38,26,14]⟩
def cycle1166_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1166_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1166 : PartitionData E W := ⟨6,![cycle1166_0,cycle1166_1,cycle1166_2,cycle1166_3,cycle1166_4,cycle1166_5]⟩
lemma valid_data1166 : data1166.Valid src1166 dst1166 Finset.univ := by decide +kernel

def src1167 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1167 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1167_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1167_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1167_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1167_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1167_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1167_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1167 : PartitionData E W := ⟨6,![cycle1167_0,cycle1167_1,cycle1167_2,cycle1167_3,cycle1167_4,cycle1167_5]⟩
lemma valid_data1167 : data1167.Valid src1167 dst1167 Finset.univ := by decide +kernel

def src1168 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1168 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1168_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1168_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1168_2 : CycleData E W := ⟨3,![2,17,20,21,3],![3,6,38,28,8]⟩
def cycle1168_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1168_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1168_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1168 : PartitionData E W := ⟨6,![cycle1168_0,cycle1168_1,cycle1168_2,cycle1168_3,cycle1168_4,cycle1168_5]⟩
lemma valid_data1168 : data1168.Valid src1168 dst1168 Finset.univ := by decide +kernel

def src1169 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1169 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1169_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1169_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1169_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1169_3 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1169_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1169_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1169 : PartitionData E W := ⟨6,![cycle1169_0,cycle1169_1,cycle1169_2,cycle1169_3,cycle1169_4,cycle1169_5]⟩
lemma valid_data1169 : data1169.Valid src1169 dst1169 Finset.univ := by decide +kernel

def src1170 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1170 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1170_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1170_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1170_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1170_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1170_4 : CycleData E W := ⟨3,![6,11,19,8,7],![3,14,28,18,16]⟩
def cycle1170_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1170 : PartitionData E W := ⟨6,![cycle1170_0,cycle1170_1,cycle1170_2,cycle1170_3,cycle1170_4,cycle1170_5]⟩
lemma valid_data1170 : data1170.Valid src1170 dst1170 Finset.univ := by decide +kernel

def src1171 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1171 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1171_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1171_1 : CycleData E W := ⟨3,![2,1,13,15,7],![3,6,4,26,16]⟩
def cycle1171_2 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1171_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1171_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1171_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1171 : PartitionData E W := ⟨6,![cycle1171_0,cycle1171_1,cycle1171_2,cycle1171_3,cycle1171_4,cycle1171_5]⟩
lemma valid_data1171 : data1171.Valid src1171 dst1171 Finset.univ := by decide +kernel

def src1172 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1172 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1172_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1172_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1172_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1172_3 : CycleData E W := ⟨2,![3,18,11,6],![3,8,28,14]⟩
def cycle1172_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1172_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1172 : PartitionData E W := ⟨6,![cycle1172_0,cycle1172_1,cycle1172_2,cycle1172_3,cycle1172_4,cycle1172_5]⟩
lemma valid_data1172 : data1172.Valid src1172 dst1172 Finset.univ := by decide +kernel

def src1173 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1173 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1173_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1173_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1173_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1173_3 : CycleData E W := ⟨4,![4,3,6,11,19,9],![2,8,3,14,28,18]⟩
def cycle1173_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1173_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1173 : PartitionData E W := ⟨6,![cycle1173_0,cycle1173_1,cycle1173_2,cycle1173_3,cycle1173_4,cycle1173_5]⟩
lemma valid_data1173 : data1173.Valid src1173 dst1173 Finset.univ := by decide +kernel

def src1174 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1174 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1174_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1174_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1174_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1174_3 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1174_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1174_5 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1174_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1174 : PartitionData E W := ⟨7,![cycle1174_0,cycle1174_1,cycle1174_2,cycle1174_3,cycle1174_4,cycle1174_5,cycle1174_6]⟩
lemma valid_data1174 : data1174.Valid src1174 dst1174 Finset.univ := by decide +kernel

def src1175 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1175 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1175_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1175_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1175_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1175_3 : CycleData E W := ⟨2,![3,18,11,6],![3,8,28,14]⟩
def cycle1175_4 : CycleData E W := ⟨3,![4,21,15,8,9],![2,8,38,16,18]⟩
def cycle1175_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1175 : PartitionData E W := ⟨6,![cycle1175_0,cycle1175_1,cycle1175_2,cycle1175_3,cycle1175_4,cycle1175_5]⟩
lemma valid_data1175 : data1175.Valid src1175 dst1175 Finset.univ := by decide +kernel

def src1176 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1176 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1176_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1176_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1176_2 : CycleData E W := ⟨2,![2,17,16,7],![3,6,38,16]⟩
def cycle1176_3 : CycleData E W := ⟨3,![3,21,20,11,6],![3,8,38,28,14]⟩
def cycle1176_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1176_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1176 : PartitionData E W := ⟨6,![cycle1176_0,cycle1176_1,cycle1176_2,cycle1176_3,cycle1176_4,cycle1176_5]⟩
lemma valid_data1176 : data1176.Valid src1176 dst1176 Finset.univ := by decide +kernel

def src1177 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1177 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1177_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1177_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1177_2 : CycleData E W := ⟨2,![2,17,16,7],![3,6,38,16]⟩
def cycle1177_3 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1177_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1177_5 : CycleData E W := ⟨3,![8,19,20,12,15],![16,18,38,28,26]⟩
def data1177 : PartitionData E W := ⟨6,![cycle1177_0,cycle1177_1,cycle1177_2,cycle1177_3,cycle1177_4,cycle1177_5]⟩
lemma valid_data1177 : data1177.Valid src1177 dst1177 Finset.univ := by decide +kernel

def src1178 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1178 : E → W := ![4,6,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1178_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1178_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1178_2 : CycleData E W := ⟨2,![2,17,16,7],![3,6,38,16]⟩
def cycle1178_3 : CycleData E W := ⟨2,![3,18,11,6],![3,8,28,14]⟩
def cycle1178_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1178_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1178 : PartitionData E W := ⟨6,![cycle1178_0,cycle1178_1,cycle1178_2,cycle1178_3,cycle1178_4,cycle1178_5]⟩
lemma valid_data1178 : data1178.Valid src1178 dst1178 Finset.univ := by decide +kernel

def src1179 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1179 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1179_0 : CycleData E W := ⟨9,![4,18,8,7,2,17,16,10,13,12,5],![2,8,18,16,3,6,38,26,4,28,14]⟩
def cycle1179_1 : CycleData E W := ⟨9,![0,1,14,15,11,6,3,21,20,19,9],![2,4,6,16,26,14,3,8,38,28,18]⟩
def data1179 : PartitionData E W := ⟨2,![cycle1179_0,cycle1179_1]⟩
lemma valid_data1179 : data1179.Valid src1179 dst1179 Finset.univ := by decide +kernel

def src1180 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1180 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1180_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1180_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1180_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1180_3 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1180_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1180_5 : CycleData E W := ⟨2,![8,19,16,15],![16,18,38,26]⟩
def data1180 : PartitionData E W := ⟨6,![cycle1180_0,cycle1180_1,cycle1180_2,cycle1180_3,cycle1180_4,cycle1180_5]⟩
lemma valid_data1180 : data1180.Valid src1180 dst1180 Finset.univ := by decide +kernel

def src1181 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1181 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1181_0 : CycleData E W := ⟨9,![0,1,17,16,11,12,18,3,7,8,9],![2,4,6,38,26,14,28,8,3,16,18]⟩
def cycle1181_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,15,14,2,6,5],![2,8,38,18,28,4,26,16,6,3,14]⟩
def data1181 : PartitionData E W := ⟨2,![cycle1181_0,cycle1181_1]⟩
lemma valid_data1181 : data1181.Valid src1181 dst1181 Finset.univ := by decide +kernel

def src1182 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1182 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1182_0 : CycleData E W := ⟨2,![0,13,12,5],![2,4,28,14]⟩
def cycle1182_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1182_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1182_3 : CycleData E W := ⟨3,![3,21,16,11,6],![3,8,38,26,14]⟩
def cycle1182_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1182_5 : CycleData E W := ⟨2,![8,19,20,15],![16,18,28,38]⟩
def data1182 : PartitionData E W := ⟨6,![cycle1182_0,cycle1182_1,cycle1182_2,cycle1182_3,cycle1182_4,cycle1182_5]⟩
lemma valid_data1182 : data1182.Valid src1182 dst1182 Finset.univ := by decide +kernel

def src1183 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1183 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1183_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1183_1 : CycleData E W := ⟨3,![1,17,16,20,13],![4,6,26,38,28]⟩
def cycle1183_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1183_3 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1183_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1183_5 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def data1183 : PartitionData E W := ⟨6,![cycle1183_0,cycle1183_1,cycle1183_2,cycle1183_3,cycle1183_4,cycle1183_5]⟩
lemma valid_data1183 : data1183.Valid src1183 dst1183 Finset.univ := by decide +kernel

def src1184 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1184 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1184_0 : CycleData E W := ⟨2,![0,13,12,5],![2,4,28,14]⟩
def cycle1184_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1184_2 : CycleData E W := ⟨1,![2,14,7],![3,6,16]⟩
def cycle1184_3 : CycleData E W := ⟨3,![3,21,16,11,6],![3,8,38,26,14]⟩
def cycle1184_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1184_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1184 : PartitionData E W := ⟨6,![cycle1184_0,cycle1184_1,cycle1184_2,cycle1184_3,cycle1184_4,cycle1184_5]⟩
lemma valid_data1184 : data1184.Valid src1184 dst1184 Finset.univ := by decide +kernel

def src1185 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1185 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1185_0 : CycleData E W := ⟨2,![0,13,12,5],![2,4,28,14]⟩
def cycle1185_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1185_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1185_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1185_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1185_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1185 : PartitionData E W := ⟨6,![cycle1185_0,cycle1185_1,cycle1185_2,cycle1185_3,cycle1185_4,cycle1185_5]⟩
lemma valid_data1185 : data1185.Valid src1185 dst1185 Finset.univ := by decide +kernel

def src1186 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1186 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1186_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1186_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1186_2 : CycleData E W := ⟨2,![2,14,15,7],![3,6,26,16]⟩
def cycle1186_3 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1186_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1186_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1186 : PartitionData E W := ⟨6,![cycle1186_0,cycle1186_1,cycle1186_2,cycle1186_3,cycle1186_4,cycle1186_5]⟩
lemma valid_data1186 : data1186.Valid src1186 dst1186 Finset.univ := by decide +kernel

def src1187 : E → W := ![2,4,6,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1187 : E → W := ![4,6,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1187_0 : CycleData E W := ⟨2,![0,13,12,5],![2,4,28,14]⟩
def cycle1187_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1187_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1187_3 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1187_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1187_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1187 : PartitionData E W := ⟨6,![cycle1187_0,cycle1187_1,cycle1187_2,cycle1187_3,cycle1187_4,cycle1187_5]⟩
lemma valid_data1187 : data1187.Valid src1187 dst1187 Finset.univ := by decide +kernel

def src1188 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1188 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1188_0 : CycleData E W := ⟨9,![5,10,13,12,16,17,2,3,18,8,9],![2,14,4,28,26,38,6,3,8,18,16]⟩
def cycle1188_1 : CycleData E W := ⟨9,![0,1,14,15,11,6,7,19,20,21,4],![2,4,6,16,26,14,3,18,28,38,8]⟩
def data1188 : PartitionData E W := ⟨2,![cycle1188_0,cycle1188_1]⟩
lemma valid_data1188 : data1188.Valid src1188 dst1188 Finset.univ := by decide +kernel

def src1189 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1189 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1189_0 : CycleData E W := ⟨2,![0,13,21,4],![2,4,28,8]⟩
def cycle1189_1 : CycleData E W := ⟨2,![2,1,10,6],![3,6,4,14]⟩
def cycle1189_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1189_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1189_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1189_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1189 : PartitionData E W := ⟨6,![cycle1189_0,cycle1189_1,cycle1189_2,cycle1189_3,cycle1189_4,cycle1189_5]⟩
lemma valid_data1189 : data1189.Valid src1189 dst1189 Finset.univ := by decide +kernel

def src1190 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1190 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1190_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,10,6,7,8,9],![2,8,28,26,38,6,4,14,3,18,16]⟩
def cycle1190_1 : CycleData E W := ⟨9,![0,13,19,20,21,3,2,14,15,11,5],![2,4,28,18,38,8,3,6,16,26,14]⟩
def data1190 : PartitionData E W := ⟨2,![cycle1190_0,cycle1190_1]⟩
lemma valid_data1190 : data1190.Valid src1190 dst1190 Finset.univ := by decide +kernel

def src1191 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1191 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1191_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1191_1 : CycleData E W := ⟨3,![1,14,8,19,13],![4,6,16,18,28]⟩
def cycle1191_2 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1191_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1191_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1191_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1191 : PartitionData E W := ⟨6,![cycle1191_0,cycle1191_1,cycle1191_2,cycle1191_3,cycle1191_4,cycle1191_5]⟩
lemma valid_data1191 : data1191.Valid src1191 dst1191 Finset.univ := by decide +kernel

def src1192 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1192 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1192_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1192_1 : CycleData E W := ⟨4,![4,21,13,1,14,9],![2,8,28,4,6,16]⟩
def cycle1192_2 : CycleData E W := ⟨2,![2,17,11,6],![3,6,26,14]⟩
def cycle1192_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1192_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1192_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1192 : PartitionData E W := ⟨6,![cycle1192_0,cycle1192_1,cycle1192_2,cycle1192_3,cycle1192_4,cycle1192_5]⟩
lemma valid_data1192 : data1192.Valid src1192 dst1192 Finset.univ := by decide +kernel

def src1193 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1193 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1193_0 : CycleData E W := ⟨9,![4,18,12,16,15,8,7,2,1,10,5],![2,8,28,26,38,16,18,3,6,4,14]⟩
def cycle1193_1 : CycleData E W := ⟨9,![0,13,19,20,21,3,6,11,17,14,9],![2,4,28,18,38,8,3,14,26,6,16]⟩
def data1193 : PartitionData E W := ⟨2,![cycle1193_0,cycle1193_1]⟩
lemma valid_data1193 : data1193.Valid src1193 dst1193 Finset.univ := by decide +kernel

def src1194 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1194 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1194_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1194_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1194_2 : CycleData E W := ⟨2,![2,14,11,6],![3,6,26,14]⟩
def cycle1194_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1194_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1194_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1194 : PartitionData E W := ⟨6,![cycle1194_0,cycle1194_1,cycle1194_2,cycle1194_3,cycle1194_4,cycle1194_5]⟩
lemma valid_data1194 : data1194.Valid src1194 dst1194 Finset.univ := by decide +kernel

def src1195 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1195 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1195_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1195_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1195_2 : CycleData E W := ⟨2,![2,14,11,6],![3,6,26,14]⟩
def cycle1195_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1195_4 : CycleData E W := ⟨3,![4,21,12,15,9],![2,8,28,26,16]⟩
def cycle1195_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1195 : PartitionData E W := ⟨6,![cycle1195_0,cycle1195_1,cycle1195_2,cycle1195_3,cycle1195_4,cycle1195_5]⟩
lemma valid_data1195 : data1195.Valid src1195 dst1195 Finset.univ := by decide +kernel

def src1196 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1196 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1196_0 : CycleData E W := ⟨9,![0,1,17,16,8,7,3,18,12,11,5],![2,4,6,38,16,18,3,8,28,26,14]⟩
def cycle1196_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,6,2,14,15,9],![2,8,38,18,28,4,14,3,6,26,16]⟩
def data1196 : PartitionData E W := ⟨2,![cycle1196_0,cycle1196_1]⟩
lemma valid_data1196 : data1196.Valid src1196 dst1196 Finset.univ := by decide +kernel

def src1197 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1197 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1197_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1197_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1197_2 : CycleData E W := ⟨2,![2,17,21,3],![3,6,38,8]⟩
def cycle1197_3 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle1197_4 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle1197_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1197 : PartitionData E W := ⟨6,![cycle1197_0,cycle1197_1,cycle1197_2,cycle1197_3,cycle1197_4,cycle1197_5]⟩
lemma valid_data1197 : data1197.Valid src1197 dst1197 Finset.univ := by decide +kernel

def src1198 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1198 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1198_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1198_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1198_2 : CycleData E W := ⟨2,![2,17,19,7],![3,6,38,18]⟩
def cycle1198_3 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1198_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle1198_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1198 : PartitionData E W := ⟨6,![cycle1198_0,cycle1198_1,cycle1198_2,cycle1198_3,cycle1198_4,cycle1198_5]⟩
lemma valid_data1198 : data1198.Valid src1198 dst1198 Finset.univ := by decide +kernel

def src1199 : E → W := ![2,4,6,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1199 : E → W := ![4,6,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1199_0 : CycleData E W := ⟨9,![5,10,1,17,16,12,18,3,7,8,9],![2,14,4,6,38,26,28,8,3,18,16]⟩
def cycle1199_1 : CycleData E W := ⟨9,![0,13,15,14,2,6,11,19,20,21,4],![2,4,26,16,6,3,14,28,18,38,8]⟩
def data1199 : PartitionData E W := ⟨2,![cycle1199_0,cycle1199_1]⟩
lemma valid_data1199 : data1199.Valid src1199 dst1199 Finset.univ := by decide +kernel

def lookupB5 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data1000 else (if j < 2 then data1001 else data1002)) else (if j < 4 then data1003 else (if j < 5 then data1004 else data1005))) else (if j < 9 then (if j < 7 then data1006 else (if j < 8 then data1007 else data1008)) else (if j < 10 then data1009 else (if j < 11 then data1010 else data1011)))) else (if j < 18 then (if j < 15 then (if j < 13 then data1012 else (if j < 14 then data1013 else data1014)) else (if j < 16 then data1015 else (if j < 17 then data1016 else data1017))) else (if j < 21 then (if j < 19 then data1018 else (if j < 20 then data1019 else data1020)) else (if j < 23 then (if j < 22 then data1021 else data1022) else (if j < 24 then data1023 else data1024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data1025 else (if j < 27 then data1026 else data1027)) else (if j < 29 then data1028 else (if j < 30 then data1029 else data1030))) else (if j < 34 then (if j < 32 then data1031 else (if j < 33 then data1032 else data1033)) else (if j < 35 then data1034 else (if j < 36 then data1035 else data1036)))) else (if j < 43 then (if j < 40 then (if j < 38 then data1037 else (if j < 39 then data1038 else data1039)) else (if j < 41 then data1040 else (if j < 42 then data1041 else data1042))) else (if j < 46 then (if j < 44 then data1043 else (if j < 45 then data1044 else data1045)) else (if j < 48 then (if j < 47 then data1046 else data1047) else (if j < 49 then data1048 else data1049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data1050 else (if j < 52 then data1051 else data1052)) else (if j < 54 then data1053 else (if j < 55 then data1054 else data1055))) else (if j < 59 then (if j < 57 then data1056 else (if j < 58 then data1057 else data1058)) else (if j < 60 then data1059 else (if j < 61 then data1060 else data1061)))) else (if j < 68 then (if j < 65 then (if j < 63 then data1062 else (if j < 64 then data1063 else data1064)) else (if j < 66 then data1065 else (if j < 67 then data1066 else data1067))) else (if j < 71 then (if j < 69 then data1068 else (if j < 70 then data1069 else data1070)) else (if j < 73 then (if j < 72 then data1071 else data1072) else (if j < 74 then data1073 else data1074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data1075 else (if j < 77 then data1076 else data1077)) else (if j < 79 then data1078 else (if j < 80 then data1079 else data1080))) else (if j < 84 then (if j < 82 then data1081 else (if j < 83 then data1082 else data1083)) else (if j < 85 then data1084 else (if j < 86 then data1085 else data1086)))) else (if j < 93 then (if j < 90 then (if j < 88 then data1087 else (if j < 89 then data1088 else data1089)) else (if j < 91 then data1090 else (if j < 92 then data1091 else data1092))) else (if j < 96 then (if j < 94 then data1093 else (if j < 95 then data1094 else data1095)) else (if j < 98 then (if j < 97 then data1096 else data1097) else (if j < 99 then data1098 else data1099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data1100 else (if j < 102 then data1101 else data1102)) else (if j < 104 then data1103 else (if j < 105 then data1104 else data1105))) else (if j < 109 then (if j < 107 then data1106 else (if j < 108 then data1107 else data1108)) else (if j < 110 then data1109 else (if j < 111 then data1110 else data1111)))) else (if j < 118 then (if j < 115 then (if j < 113 then data1112 else (if j < 114 then data1113 else data1114)) else (if j < 116 then data1115 else (if j < 117 then data1116 else data1117))) else (if j < 121 then (if j < 119 then data1118 else (if j < 120 then data1119 else data1120)) else (if j < 123 then (if j < 122 then data1121 else data1122) else (if j < 124 then data1123 else data1124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data1125 else (if j < 127 then data1126 else data1127)) else (if j < 129 then data1128 else (if j < 130 then data1129 else data1130))) else (if j < 134 then (if j < 132 then data1131 else (if j < 133 then data1132 else data1133)) else (if j < 135 then data1134 else (if j < 136 then data1135 else data1136)))) else (if j < 143 then (if j < 140 then (if j < 138 then data1137 else (if j < 139 then data1138 else data1139)) else (if j < 141 then data1140 else (if j < 142 then data1141 else data1142))) else (if j < 146 then (if j < 144 then data1143 else (if j < 145 then data1144 else data1145)) else (if j < 148 then (if j < 147 then data1146 else data1147) else (if j < 149 then data1148 else data1149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data1150 else (if j < 152 then data1151 else data1152)) else (if j < 154 then data1153 else (if j < 155 then data1154 else data1155))) else (if j < 159 then (if j < 157 then data1156 else (if j < 158 then data1157 else data1158)) else (if j < 160 then data1159 else (if j < 161 then data1160 else data1161)))) else (if j < 168 then (if j < 165 then (if j < 163 then data1162 else (if j < 164 then data1163 else data1164)) else (if j < 166 then data1165 else (if j < 167 then data1166 else data1167))) else (if j < 171 then (if j < 169 then data1168 else (if j < 170 then data1169 else data1170)) else (if j < 173 then (if j < 172 then data1171 else data1172) else (if j < 174 then data1173 else data1174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data1175 else (if j < 177 then data1176 else data1177)) else (if j < 179 then data1178 else (if j < 180 then data1179 else data1180))) else (if j < 184 then (if j < 182 then data1181 else (if j < 183 then data1182 else data1183)) else (if j < 185 then data1184 else (if j < 186 then data1185 else data1186)))) else (if j < 193 then (if j < 190 then (if j < 188 then data1187 else (if j < 189 then data1188 else data1189)) else (if j < 191 then data1190 else (if j < 192 then data1191 else data1192))) else (if j < 196 then (if j < 194 then data1193 else (if j < 195 then data1194 else data1195)) else (if j < 198 then (if j < 197 then data1196 else data1197) else (if j < 199 then data1198 else data1199))))))))

def srcTableB5 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src1000 else (if j < 2 then src1001 else src1002)) else (if j < 4 then src1003 else (if j < 5 then src1004 else src1005))) else (if j < 9 then (if j < 7 then src1006 else (if j < 8 then src1007 else src1008)) else (if j < 10 then src1009 else (if j < 11 then src1010 else src1011)))) else (if j < 18 then (if j < 15 then (if j < 13 then src1012 else (if j < 14 then src1013 else src1014)) else (if j < 16 then src1015 else (if j < 17 then src1016 else src1017))) else (if j < 21 then (if j < 19 then src1018 else (if j < 20 then src1019 else src1020)) else (if j < 23 then (if j < 22 then src1021 else src1022) else (if j < 24 then src1023 else src1024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src1025 else (if j < 27 then src1026 else src1027)) else (if j < 29 then src1028 else (if j < 30 then src1029 else src1030))) else (if j < 34 then (if j < 32 then src1031 else (if j < 33 then src1032 else src1033)) else (if j < 35 then src1034 else (if j < 36 then src1035 else src1036)))) else (if j < 43 then (if j < 40 then (if j < 38 then src1037 else (if j < 39 then src1038 else src1039)) else (if j < 41 then src1040 else (if j < 42 then src1041 else src1042))) else (if j < 46 then (if j < 44 then src1043 else (if j < 45 then src1044 else src1045)) else (if j < 48 then (if j < 47 then src1046 else src1047) else (if j < 49 then src1048 else src1049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src1050 else (if j < 52 then src1051 else src1052)) else (if j < 54 then src1053 else (if j < 55 then src1054 else src1055))) else (if j < 59 then (if j < 57 then src1056 else (if j < 58 then src1057 else src1058)) else (if j < 60 then src1059 else (if j < 61 then src1060 else src1061)))) else (if j < 68 then (if j < 65 then (if j < 63 then src1062 else (if j < 64 then src1063 else src1064)) else (if j < 66 then src1065 else (if j < 67 then src1066 else src1067))) else (if j < 71 then (if j < 69 then src1068 else (if j < 70 then src1069 else src1070)) else (if j < 73 then (if j < 72 then src1071 else src1072) else (if j < 74 then src1073 else src1074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src1075 else (if j < 77 then src1076 else src1077)) else (if j < 79 then src1078 else (if j < 80 then src1079 else src1080))) else (if j < 84 then (if j < 82 then src1081 else (if j < 83 then src1082 else src1083)) else (if j < 85 then src1084 else (if j < 86 then src1085 else src1086)))) else (if j < 93 then (if j < 90 then (if j < 88 then src1087 else (if j < 89 then src1088 else src1089)) else (if j < 91 then src1090 else (if j < 92 then src1091 else src1092))) else (if j < 96 then (if j < 94 then src1093 else (if j < 95 then src1094 else src1095)) else (if j < 98 then (if j < 97 then src1096 else src1097) else (if j < 99 then src1098 else src1099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src1100 else (if j < 102 then src1101 else src1102)) else (if j < 104 then src1103 else (if j < 105 then src1104 else src1105))) else (if j < 109 then (if j < 107 then src1106 else (if j < 108 then src1107 else src1108)) else (if j < 110 then src1109 else (if j < 111 then src1110 else src1111)))) else (if j < 118 then (if j < 115 then (if j < 113 then src1112 else (if j < 114 then src1113 else src1114)) else (if j < 116 then src1115 else (if j < 117 then src1116 else src1117))) else (if j < 121 then (if j < 119 then src1118 else (if j < 120 then src1119 else src1120)) else (if j < 123 then (if j < 122 then src1121 else src1122) else (if j < 124 then src1123 else src1124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src1125 else (if j < 127 then src1126 else src1127)) else (if j < 129 then src1128 else (if j < 130 then src1129 else src1130))) else (if j < 134 then (if j < 132 then src1131 else (if j < 133 then src1132 else src1133)) else (if j < 135 then src1134 else (if j < 136 then src1135 else src1136)))) else (if j < 143 then (if j < 140 then (if j < 138 then src1137 else (if j < 139 then src1138 else src1139)) else (if j < 141 then src1140 else (if j < 142 then src1141 else src1142))) else (if j < 146 then (if j < 144 then src1143 else (if j < 145 then src1144 else src1145)) else (if j < 148 then (if j < 147 then src1146 else src1147) else (if j < 149 then src1148 else src1149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src1150 else (if j < 152 then src1151 else src1152)) else (if j < 154 then src1153 else (if j < 155 then src1154 else src1155))) else (if j < 159 then (if j < 157 then src1156 else (if j < 158 then src1157 else src1158)) else (if j < 160 then src1159 else (if j < 161 then src1160 else src1161)))) else (if j < 168 then (if j < 165 then (if j < 163 then src1162 else (if j < 164 then src1163 else src1164)) else (if j < 166 then src1165 else (if j < 167 then src1166 else src1167))) else (if j < 171 then (if j < 169 then src1168 else (if j < 170 then src1169 else src1170)) else (if j < 173 then (if j < 172 then src1171 else src1172) else (if j < 174 then src1173 else src1174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src1175 else (if j < 177 then src1176 else src1177)) else (if j < 179 then src1178 else (if j < 180 then src1179 else src1180))) else (if j < 184 then (if j < 182 then src1181 else (if j < 183 then src1182 else src1183)) else (if j < 185 then src1184 else (if j < 186 then src1185 else src1186)))) else (if j < 193 then (if j < 190 then (if j < 188 then src1187 else (if j < 189 then src1188 else src1189)) else (if j < 191 then src1190 else (if j < 192 then src1191 else src1192))) else (if j < 196 then (if j < 194 then src1193 else (if j < 195 then src1194 else src1195)) else (if j < 198 then (if j < 197 then src1196 else src1197) else (if j < 199 then src1198 else src1199))))))))

def dstTableB5 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst1000 else (if j < 2 then dst1001 else dst1002)) else (if j < 4 then dst1003 else (if j < 5 then dst1004 else dst1005))) else (if j < 9 then (if j < 7 then dst1006 else (if j < 8 then dst1007 else dst1008)) else (if j < 10 then dst1009 else (if j < 11 then dst1010 else dst1011)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst1012 else (if j < 14 then dst1013 else dst1014)) else (if j < 16 then dst1015 else (if j < 17 then dst1016 else dst1017))) else (if j < 21 then (if j < 19 then dst1018 else (if j < 20 then dst1019 else dst1020)) else (if j < 23 then (if j < 22 then dst1021 else dst1022) else (if j < 24 then dst1023 else dst1024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst1025 else (if j < 27 then dst1026 else dst1027)) else (if j < 29 then dst1028 else (if j < 30 then dst1029 else dst1030))) else (if j < 34 then (if j < 32 then dst1031 else (if j < 33 then dst1032 else dst1033)) else (if j < 35 then dst1034 else (if j < 36 then dst1035 else dst1036)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst1037 else (if j < 39 then dst1038 else dst1039)) else (if j < 41 then dst1040 else (if j < 42 then dst1041 else dst1042))) else (if j < 46 then (if j < 44 then dst1043 else (if j < 45 then dst1044 else dst1045)) else (if j < 48 then (if j < 47 then dst1046 else dst1047) else (if j < 49 then dst1048 else dst1049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst1050 else (if j < 52 then dst1051 else dst1052)) else (if j < 54 then dst1053 else (if j < 55 then dst1054 else dst1055))) else (if j < 59 then (if j < 57 then dst1056 else (if j < 58 then dst1057 else dst1058)) else (if j < 60 then dst1059 else (if j < 61 then dst1060 else dst1061)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst1062 else (if j < 64 then dst1063 else dst1064)) else (if j < 66 then dst1065 else (if j < 67 then dst1066 else dst1067))) else (if j < 71 then (if j < 69 then dst1068 else (if j < 70 then dst1069 else dst1070)) else (if j < 73 then (if j < 72 then dst1071 else dst1072) else (if j < 74 then dst1073 else dst1074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst1075 else (if j < 77 then dst1076 else dst1077)) else (if j < 79 then dst1078 else (if j < 80 then dst1079 else dst1080))) else (if j < 84 then (if j < 82 then dst1081 else (if j < 83 then dst1082 else dst1083)) else (if j < 85 then dst1084 else (if j < 86 then dst1085 else dst1086)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst1087 else (if j < 89 then dst1088 else dst1089)) else (if j < 91 then dst1090 else (if j < 92 then dst1091 else dst1092))) else (if j < 96 then (if j < 94 then dst1093 else (if j < 95 then dst1094 else dst1095)) else (if j < 98 then (if j < 97 then dst1096 else dst1097) else (if j < 99 then dst1098 else dst1099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst1100 else (if j < 102 then dst1101 else dst1102)) else (if j < 104 then dst1103 else (if j < 105 then dst1104 else dst1105))) else (if j < 109 then (if j < 107 then dst1106 else (if j < 108 then dst1107 else dst1108)) else (if j < 110 then dst1109 else (if j < 111 then dst1110 else dst1111)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst1112 else (if j < 114 then dst1113 else dst1114)) else (if j < 116 then dst1115 else (if j < 117 then dst1116 else dst1117))) else (if j < 121 then (if j < 119 then dst1118 else (if j < 120 then dst1119 else dst1120)) else (if j < 123 then (if j < 122 then dst1121 else dst1122) else (if j < 124 then dst1123 else dst1124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst1125 else (if j < 127 then dst1126 else dst1127)) else (if j < 129 then dst1128 else (if j < 130 then dst1129 else dst1130))) else (if j < 134 then (if j < 132 then dst1131 else (if j < 133 then dst1132 else dst1133)) else (if j < 135 then dst1134 else (if j < 136 then dst1135 else dst1136)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst1137 else (if j < 139 then dst1138 else dst1139)) else (if j < 141 then dst1140 else (if j < 142 then dst1141 else dst1142))) else (if j < 146 then (if j < 144 then dst1143 else (if j < 145 then dst1144 else dst1145)) else (if j < 148 then (if j < 147 then dst1146 else dst1147) else (if j < 149 then dst1148 else dst1149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst1150 else (if j < 152 then dst1151 else dst1152)) else (if j < 154 then dst1153 else (if j < 155 then dst1154 else dst1155))) else (if j < 159 then (if j < 157 then dst1156 else (if j < 158 then dst1157 else dst1158)) else (if j < 160 then dst1159 else (if j < 161 then dst1160 else dst1161)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst1162 else (if j < 164 then dst1163 else dst1164)) else (if j < 166 then dst1165 else (if j < 167 then dst1166 else dst1167))) else (if j < 171 then (if j < 169 then dst1168 else (if j < 170 then dst1169 else dst1170)) else (if j < 173 then (if j < 172 then dst1171 else dst1172) else (if j < 174 then dst1173 else dst1174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst1175 else (if j < 177 then dst1176 else dst1177)) else (if j < 179 then dst1178 else (if j < 180 then dst1179 else dst1180))) else (if j < 184 then (if j < 182 then dst1181 else (if j < 183 then dst1182 else dst1183)) else (if j < 185 then dst1184 else (if j < 186 then dst1185 else dst1186)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst1187 else (if j < 189 then dst1188 else dst1189)) else (if j < 191 then dst1190 else (if j < 192 then dst1191 else dst1192))) else (if j < 196 then (if j < 194 then dst1193 else (if j < 195 then dst1194 else dst1195)) else (if j < 198 then (if j < 197 then dst1196 else dst1197) else (if j < 199 then dst1198 else dst1199))))))))

def caseB5 (i : Fin 200) : Cases := ⟨1000 + i.val,by have := i.isLt; omega⟩
lemma tableB5_valid (i : Fin 200) :
    (lookupB5 i.val).Valid (srcTableB5 i.val) (dstTableB5 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data1000
  · exact valid_data1001
  · exact valid_data1002
  · exact valid_data1003
  · exact valid_data1004
  · exact valid_data1005
  · exact valid_data1006
  · exact valid_data1007
  · exact valid_data1008
  · exact valid_data1009
  · exact valid_data1010
  · exact valid_data1011
  · exact valid_data1012
  · exact valid_data1013
  · exact valid_data1014
  · exact valid_data1015
  · exact valid_data1016
  · exact valid_data1017
  · exact valid_data1018
  · exact valid_data1019
  · exact valid_data1020
  · exact valid_data1021
  · exact valid_data1022
  · exact valid_data1023
  · exact valid_data1024
  · exact valid_data1025
  · exact valid_data1026
  · exact valid_data1027
  · exact valid_data1028
  · exact valid_data1029
  · exact valid_data1030
  · exact valid_data1031
  · exact valid_data1032
  · exact valid_data1033
  · exact valid_data1034
  · exact valid_data1035
  · exact valid_data1036
  · exact valid_data1037
  · exact valid_data1038
  · exact valid_data1039
  · exact valid_data1040
  · exact valid_data1041
  · exact valid_data1042
  · exact valid_data1043
  · exact valid_data1044
  · exact valid_data1045
  · exact valid_data1046
  · exact valid_data1047
  · exact valid_data1048
  · exact valid_data1049
  · exact valid_data1050
  · exact valid_data1051
  · exact valid_data1052
  · exact valid_data1053
  · exact valid_data1054
  · exact valid_data1055
  · exact valid_data1056
  · exact valid_data1057
  · exact valid_data1058
  · exact valid_data1059
  · exact valid_data1060
  · exact valid_data1061
  · exact valid_data1062
  · exact valid_data1063
  · exact valid_data1064
  · exact valid_data1065
  · exact valid_data1066
  · exact valid_data1067
  · exact valid_data1068
  · exact valid_data1069
  · exact valid_data1070
  · exact valid_data1071
  · exact valid_data1072
  · exact valid_data1073
  · exact valid_data1074
  · exact valid_data1075
  · exact valid_data1076
  · exact valid_data1077
  · exact valid_data1078
  · exact valid_data1079
  · exact valid_data1080
  · exact valid_data1081
  · exact valid_data1082
  · exact valid_data1083
  · exact valid_data1084
  · exact valid_data1085
  · exact valid_data1086
  · exact valid_data1087
  · exact valid_data1088
  · exact valid_data1089
  · exact valid_data1090
  · exact valid_data1091
  · exact valid_data1092
  · exact valid_data1093
  · exact valid_data1094
  · exact valid_data1095
  · exact valid_data1096
  · exact valid_data1097
  · exact valid_data1098
  · exact valid_data1099
  · exact valid_data1100
  · exact valid_data1101
  · exact valid_data1102
  · exact valid_data1103
  · exact valid_data1104
  · exact valid_data1105
  · exact valid_data1106
  · exact valid_data1107
  · exact valid_data1108
  · exact valid_data1109
  · exact valid_data1110
  · exact valid_data1111
  · exact valid_data1112
  · exact valid_data1113
  · exact valid_data1114
  · exact valid_data1115
  · exact valid_data1116
  · exact valid_data1117
  · exact valid_data1118
  · exact valid_data1119
  · exact valid_data1120
  · exact valid_data1121
  · exact valid_data1122
  · exact valid_data1123
  · exact valid_data1124
  · exact valid_data1125
  · exact valid_data1126
  · exact valid_data1127
  · exact valid_data1128
  · exact valid_data1129
  · exact valid_data1130
  · exact valid_data1131
  · exact valid_data1132
  · exact valid_data1133
  · exact valid_data1134
  · exact valid_data1135
  · exact valid_data1136
  · exact valid_data1137
  · exact valid_data1138
  · exact valid_data1139
  · exact valid_data1140
  · exact valid_data1141
  · exact valid_data1142
  · exact valid_data1143
  · exact valid_data1144
  · exact valid_data1145
  · exact valid_data1146
  · exact valid_data1147
  · exact valid_data1148
  · exact valid_data1149
  · exact valid_data1150
  · exact valid_data1151
  · exact valid_data1152
  · exact valid_data1153
  · exact valid_data1154
  · exact valid_data1155
  · exact valid_data1156
  · exact valid_data1157
  · exact valid_data1158
  · exact valid_data1159
  · exact valid_data1160
  · exact valid_data1161
  · exact valid_data1162
  · exact valid_data1163
  · exact valid_data1164
  · exact valid_data1165
  · exact valid_data1166
  · exact valid_data1167
  · exact valid_data1168
  · exact valid_data1169
  · exact valid_data1170
  · exact valid_data1171
  · exact valid_data1172
  · exact valid_data1173
  · exact valid_data1174
  · exact valid_data1175
  · exact valid_data1176
  · exact valid_data1177
  · exact valid_data1178
  · exact valid_data1179
  · exact valid_data1180
  · exact valid_data1181
  · exact valid_data1182
  · exact valid_data1183
  · exact valid_data1184
  · exact valid_data1185
  · exact valid_data1186
  · exact valid_data1187
  · exact valid_data1188
  · exact valid_data1189
  · exact valid_data1190
  · exact valid_data1191
  · exact valid_data1192
  · exact valid_data1193
  · exact valid_data1194
  · exact valid_data1195
  · exact valid_data1196
  · exact valid_data1197
  · exact valid_data1198
  · exact valid_data1199

lemma srcB5_row : ∀ (i : Fin 200) (e : E),
    srcTableB5 i.val e = caseSource (caseB5 i) e := by decide +kernel

lemma dstB5_row : ∀ (i : Fin 200) (e : E),
    dstTableB5 i.val e = caseTarget (caseB5 i) e := by decide +kernel

lemma sizeB5 : ∀ i : Fin 200, (lookupB5 i.val).size ≤ 5 →
    (lookupB5 i.val).size = 2 ∧
      (⟨caseKey (caseB5 i),caseKey_lt (caseB5 i)⟩ : Fin 3888) ∈ good := by decide +kernel
lemma certificateB5 (i : Fin 200) : Certificate (caseB5 i) := by
  refine ⟨lookupB5 i.val,?_,sizeB5 i⟩
  have hv := tableB5_valid i
  rw [funext (srcB5_row i),funext (dstB5_row i)] at hv
  exact hv
lemma certificateInterval5 : FiniteIntervals.Covers CertificateAt 1000 1200 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1000 200 (fun i _ => certificateB5 i)
#print axioms certificateInterval5
end Erdos184Work.FiveRows1

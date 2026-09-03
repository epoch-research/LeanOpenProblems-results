import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src3000 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst3000 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle3000_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3000_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,26,4]⟩
def cycle3000_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle3000_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,27,16]⟩
def cycle3000_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def cycle3000_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data3000 : PartitionData E W := ⟨6,![cycle3000_0,cycle3000_1,cycle3000_2,cycle3000_3,cycle3000_4,cycle3000_5]⟩
lemma valid_data3000 : data3000.Valid src3000 dst3000 Finset.univ := by decide +kernel

def src3001 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst3001 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle3001_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3001_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle3001_2 : CycleData E W := ⟨3,![2,10,11,17,8],![3,4,14,27,16]⟩
def cycle3001_3 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,26]⟩
def cycle3001_4 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3001_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data3001 : PartitionData E W := ⟨6,![cycle3001_0,cycle3001_1,cycle3001_2,cycle3001_3,cycle3001_4,cycle3001_5]⟩
lemma valid_data3001 : data3001.Valid src3001 dst3001 Finset.univ := by decide +kernel

def src3002 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst3002 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle3002_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle3002_1 : CycleData E W := ⟨2,![1,15,16,8],![3,6,26,16]⟩
def cycle3002_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3002_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,26]⟩
def cycle3002_4 : CycleData E W := ⟨2,![5,11,17,9],![2,14,27,16]⟩
def cycle3002_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data3002 : PartitionData E W := ⟨6,![cycle3002_0,cycle3002_1,cycle3002_2,cycle3002_3,cycle3002_4,cycle3002_5]⟩
lemma valid_data3002 : data3002.Valid src3002 dst3002 Finset.univ := by decide +kernel

def src3003 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst3003 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle3003_0 : CycleData E W := ⟨2,![0,19,11,5],![2,6,27,14]⟩
def cycle3003_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,26,4]⟩
def cycle3003_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle3003_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3003_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def cycle3003_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data3003 : PartitionData E W := ⟨6,![cycle3003_0,cycle3003_1,cycle3003_2,cycle3003_3,cycle3003_4,cycle3003_5]⟩
lemma valid_data3003 : data3003.Valid src3003 dst3003 Finset.univ := by decide +kernel

def src3004 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst3004 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle3004_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3004_1 : CycleData E W := ⟨3,![1,19,11,10,2],![3,6,27,14,4]⟩
def cycle3004_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,26]⟩
def cycle3004_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3004_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle3004_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data3004 : PartitionData E W := ⟨6,![cycle3004_0,cycle3004_1,cycle3004_2,cycle3004_3,cycle3004_4,cycle3004_5]⟩
lemma valid_data3004 : data3004.Valid src3004 dst3004 Finset.univ := by decide +kernel

def src3005 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst3005 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle3005_0 : CycleData E W := ⟨2,![0,19,11,5],![2,6,27,14]⟩
def cycle3005_1 : CycleData E W := ⟨2,![1,15,16,8],![3,6,26,16]⟩
def cycle3005_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3005_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,26]⟩
def cycle3005_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3005_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data3005 : PartitionData E W := ⟨6,![cycle3005_0,cycle3005_1,cycle3005_2,cycle3005_3,cycle3005_4,cycle3005_5]⟩
lemma valid_data3005 : data3005.Valid src3005 dst3005 Finset.univ := by decide +kernel

def src3006 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst3006 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle3006_0 : CycleData E W := ⟨3,![0,15,14,10,5],![2,6,26,4,14]⟩
def cycle3006_1 : CycleData E W := ⟨2,![1,19,18,8],![3,6,27,16]⟩
def cycle3006_2 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3006_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3006_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle3006_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3006 : PartitionData E W := ⟨6,![cycle3006_0,cycle3006_1,cycle3006_2,cycle3006_3,cycle3006_4,cycle3006_5]⟩
lemma valid_data3006 : data3006.Valid src3006 dst3006 Finset.univ := by decide +kernel

def src3007 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst3007 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle3007_0 : CycleData E W := ⟨2,![0,19,11,5],![2,6,27,14]⟩
def cycle3007_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,26,4]⟩
def cycle3007_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle3007_3 : CycleData E W := ⟨3,![4,23,12,18,9],![2,8,28,27,16]⟩
def cycle3007_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle3007_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3007 : PartitionData E W := ⟨6,![cycle3007_0,cycle3007_1,cycle3007_2,cycle3007_3,cycle3007_4,cycle3007_5]⟩
lemma valid_data3007 : data3007.Valid src3007 dst3007 Finset.univ := by decide +kernel

def src3008 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst3008 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle3008_0 : CycleData E W := ⟨2,![0,19,18,9],![2,6,27,16]⟩
def cycle3008_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,26,4]⟩
def cycle3008_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle3008_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle3008_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle3008_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data3008 : PartitionData E W := ⟨6,![cycle3008_0,cycle3008_1,cycle3008_2,cycle3008_3,cycle3008_4,cycle3008_5]⟩
lemma valid_data3008 : data3008.Valid src3008 dst3008 Finset.univ := by decide +kernel

def src3009 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst3009 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle3009_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3009_1 : CycleData E W := ⟨3,![1,19,23,20,7],![3,6,38,8,18]⟩
def cycle3009_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,26,16]⟩
def cycle3009_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle3009_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle3009_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data3009 : PartitionData E W := ⟨6,![cycle3009_0,cycle3009_1,cycle3009_2,cycle3009_3,cycle3009_4,cycle3009_5]⟩
lemma valid_data3009 : data3009.Valid src3009 dst3009 Finset.univ := by decide +kernel

def src3010 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst3010 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle3010_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,27,14]⟩
def cycle3010_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle3010_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,26,16]⟩
def cycle3010_3 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle3010_4 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,27,16]⟩
def cycle3010_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data3010 : PartitionData E W := ⟨6,![cycle3010_0,cycle3010_1,cycle3010_2,cycle3010_3,cycle3010_4,cycle3010_5]⟩
lemma valid_data3010 : data3010.Valid src3010 dst3010 Finset.univ := by decide +kernel

def src3011 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst3011 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle3011_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3011_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3011_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,26,16]⟩
def cycle3011_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle3011_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle3011_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data3011 : PartitionData E W := ⟨6,![cycle3011_0,cycle3011_1,cycle3011_2,cycle3011_3,cycle3011_4,cycle3011_5]⟩
lemma valid_data3011 : data3011.Valid src3011 dst3011 Finset.univ := by decide +kernel

def src3012 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst3012 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle3012_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3012_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3012_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3012_3 : CycleData E W := ⟨3,![4,20,21,11,5],![2,8,18,28,14]⟩
def cycle3012_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle3012_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data3012 : PartitionData E W := ⟨6,![cycle3012_0,cycle3012_1,cycle3012_2,cycle3012_3,cycle3012_4,cycle3012_5]⟩
lemma valid_data3012 : data3012.Valid src3012 dst3012 Finset.univ := by decide +kernel

def src3013 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst3013 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle3013_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3013_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3013_2 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,27]⟩
def cycle3013_3 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle3013_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle3013_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data3013 : PartitionData E W := ⟨6,![cycle3013_0,cycle3013_1,cycle3013_2,cycle3013_3,cycle3013_4,cycle3013_5]⟩
lemma valid_data3013 : data3013.Valid src3013 dst3013 Finset.univ := by decide +kernel

def src3014 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst3014 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle3014_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3014_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3014_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3014_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle3014_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,26,28,18,38]⟩
def cycle3014_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data3014 : PartitionData E W := ⟨6,![cycle3014_0,cycle3014_1,cycle3014_2,cycle3014_3,cycle3014_4,cycle3014_5]⟩
lemma valid_data3014 : data3014.Valid src3014 dst3014 Finset.univ := by decide +kernel

def src3015 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst3015 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle3015_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3015_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3015_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3015_3 : CycleData E W := ⟨3,![4,20,21,11,5],![2,8,18,28,14]⟩
def cycle3015_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle3015_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3015 : PartitionData E W := ⟨6,![cycle3015_0,cycle3015_1,cycle3015_2,cycle3015_3,cycle3015_4,cycle3015_5]⟩
lemma valid_data3015 : data3015.Valid src3015 dst3015 Finset.univ := by decide +kernel

def src3016 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst3016 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle3016_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3016_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3016_2 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,27]⟩
def cycle3016_3 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle3016_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle3016_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3016 : PartitionData E W := ⟨6,![cycle3016_0,cycle3016_1,cycle3016_2,cycle3016_3,cycle3016_4,cycle3016_5]⟩
lemma valid_data3016 : data3016.Valid src3016 dst3016 Finset.univ := by decide +kernel

def src3017 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst3017 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle3017_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3017_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3017_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3017_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle3017_4 : CycleData E W := ⟨3,![16,12,21,22,17],![16,26,28,18,38]⟩
def cycle3017_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3017 : PartitionData E W := ⟨6,![cycle3017_0,cycle3017_1,cycle3017_2,cycle3017_3,cycle3017_4,cycle3017_5]⟩
lemma valid_data3017 : data3017.Valid src3017 dst3017 Finset.univ := by decide +kernel

def src3018 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst3018 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle3018_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3018_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3018_2 : CycleData E W := ⟨2,![3,23,16,14],![4,8,38,26]⟩
def cycle3018_3 : CycleData E W := ⟨3,![4,20,21,11,5],![2,8,18,28,14]⟩
def cycle3018_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle3018_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3018 : PartitionData E W := ⟨6,![cycle3018_0,cycle3018_1,cycle3018_2,cycle3018_3,cycle3018_4,cycle3018_5]⟩
lemma valid_data3018 : data3018.Valid src3018 dst3018 Finset.univ := by decide +kernel

def src3019 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst3019 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle3019_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3019_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3019_2 : CycleData E W := ⟨3,![3,20,21,16,14],![4,8,18,38,26]⟩
def cycle3019_3 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle3019_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle3019_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3019 : PartitionData E W := ⟨6,![cycle3019_0,cycle3019_1,cycle3019_2,cycle3019_3,cycle3019_4,cycle3019_5]⟩
lemma valid_data3019 : data3019.Valid src3019 dst3019 Finset.univ := by decide +kernel

def src3020 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst3020 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle3020_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3020_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3020_2 : CycleData E W := ⟨2,![3,23,16,14],![4,8,38,26]⟩
def cycle3020_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle3020_4 : CycleData E W := ⟨3,![17,22,21,12,18],![16,38,18,28,27]⟩
def cycle3020_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data3020 : PartitionData E W := ⟨6,![cycle3020_0,cycle3020_1,cycle3020_2,cycle3020_3,cycle3020_4,cycle3020_5]⟩
lemma valid_data3020 : data3020.Valid src3020 dst3020 Finset.univ := by decide +kernel

def src3021 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst3021 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle3021_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3021_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3021_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle3021_3 : CycleData E W := ⟨3,![4,20,21,11,5],![2,8,18,28,14]⟩
def cycle3021_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle3021_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data3021 : PartitionData E W := ⟨6,![cycle3021_0,cycle3021_1,cycle3021_2,cycle3021_3,cycle3021_4,cycle3021_5]⟩
lemma valid_data3021 : data3021.Valid src3021 dst3021 Finset.univ := by decide +kernel

def src3022 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst3022 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle3022_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3022_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3022_2 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,26]⟩
def cycle3022_3 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle3022_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle3022_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data3022 : PartitionData E W := ⟨6,![cycle3022_0,cycle3022_1,cycle3022_2,cycle3022_3,cycle3022_4,cycle3022_5]⟩
lemma valid_data3022 : data3022.Valid src3022 dst3022 Finset.univ := by decide +kernel

def src3023 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst3023 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle3023_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3023_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle3023_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle3023_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle3023_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,27,28,18,38]⟩
def cycle3023_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data3023 : PartitionData E W := ⟨6,![cycle3023_0,cycle3023_1,cycle3023_2,cycle3023_3,cycle3023_4,cycle3023_5]⟩
lemma valid_data3023 : data3023.Valid src3023 dst3023 Finset.univ := by decide +kernel

def src3024 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst3024 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle3024_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3024_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3024_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle3024_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3024_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,26,14,27]⟩
def cycle3024_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3024 : PartitionData E W := ⟨6,![cycle3024_0,cycle3024_1,cycle3024_2,cycle3024_3,cycle3024_4,cycle3024_5]⟩
lemma valid_data3024 : data3024.Valid src3024 dst3024 Finset.univ := by decide +kernel

def src3025 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst3025 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle3025_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3025_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,26,38,18]⟩
def cycle3025_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3025_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3025_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,26,14,27]⟩
def cycle3025_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3025 : PartitionData E W := ⟨6,![cycle3025_0,cycle3025_1,cycle3025_2,cycle3025_3,cycle3025_4,cycle3025_5]⟩
lemma valid_data3025 : data3025.Valid src3025 dst3025 Finset.univ := by decide +kernel

def src3026 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst3026 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle3026_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3026_1 : CycleData E W := ⟨3,![1,19,12,6,7],![3,6,27,14,18]⟩
def cycle3026_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3026_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3026_4 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,26,14]⟩
def cycle3026_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data3026 : PartitionData E W := ⟨6,![cycle3026_0,cycle3026_1,cycle3026_2,cycle3026_3,cycle3026_4,cycle3026_5]⟩
lemma valid_data3026 : data3026.Valid src3026 dst3026 Finset.univ := by decide +kernel

def src3027 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst3027 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle3027_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3027_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3027_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3027_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3027_4 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def cycle3027_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,27,28,38]⟩
def data3027 : PartitionData E W := ⟨6,![cycle3027_0,cycle3027_1,cycle3027_2,cycle3027_3,cycle3027_4,cycle3027_5]⟩
lemma valid_data3027 : data3027.Valid src3027 dst3027 Finset.univ := by decide +kernel

def src3028 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst3028 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle3028_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3028_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle3028_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3028_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3028_4 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def cycle3028_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,27,28,38]⟩
def data3028 : PartitionData E W := ⟨6,![cycle3028_0,cycle3028_1,cycle3028_2,cycle3028_3,cycle3028_4,cycle3028_5]⟩
lemma valid_data3028 : data3028.Valid src3028 dst3028 Finset.univ := by decide +kernel

def src3029 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst3029 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle3029_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3029_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,26,4]⟩
def cycle3029_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3029_3 : CycleData E W := ⟨3,![4,23,22,6,5],![2,8,38,18,14]⟩
def cycle3029_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,27,16]⟩
def cycle3029_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data3029 : PartitionData E W := ⟨6,![cycle3029_0,cycle3029_1,cycle3029_2,cycle3029_3,cycle3029_4,cycle3029_5]⟩
lemma valid_data3029 : data3029.Valid src3029 dst3029 Finset.univ := by decide +kernel

def src3030 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst3030 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle3030_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3030_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3030_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3030_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3030_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,27,14,26]⟩
def cycle3030_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data3030 : PartitionData E W := ⟨6,![cycle3030_0,cycle3030_1,cycle3030_2,cycle3030_3,cycle3030_4,cycle3030_5]⟩
lemma valid_data3030 : data3030.Valid src3030 dst3030 Finset.univ := by decide +kernel

def src3031 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst3031 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle3031_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3031_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle3031_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3031_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3031_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,27,14,26]⟩
def cycle3031_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data3031 : PartitionData E W := ⟨6,![cycle3031_0,cycle3031_1,cycle3031_2,cycle3031_3,cycle3031_4,cycle3031_5]⟩
lemma valid_data3031 : data3031.Valid src3031 dst3031 Finset.univ := by decide +kernel

def src3032 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst3032 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle3032_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3032_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle3032_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3032_3 : CycleData E W := ⟨3,![4,23,17,12,5],![2,8,38,27,14]⟩
def cycle3032_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle3032_5 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,27,16]⟩
def data3032 : PartitionData E W := ⟨6,![cycle3032_0,cycle3032_1,cycle3032_2,cycle3032_3,cycle3032_4,cycle3032_5]⟩
lemma valid_data3032 : data3032.Valid src3032 dst3032 Finset.univ := by decide +kernel

def src3033 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst3033 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle3033_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3033_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3033_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle3033_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3033_4 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def cycle3033_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,27]⟩
def data3033 : PartitionData E W := ⟨6,![cycle3033_0,cycle3033_1,cycle3033_2,cycle3033_3,cycle3033_4,cycle3033_5]⟩
lemma valid_data3033 : data3033.Valid src3033 dst3033 Finset.univ := by decide +kernel

def src3034 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst3034 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle3034_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3034_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,26,38,18]⟩
def cycle3034_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3034_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3034_4 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def cycle3034_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,27]⟩
def data3034 : PartitionData E W := ⟨6,![cycle3034_0,cycle3034_1,cycle3034_2,cycle3034_3,cycle3034_4,cycle3034_5]⟩
lemma valid_data3034 : data3034.Valid src3034 dst3034 Finset.univ := by decide +kernel

def src3035 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst3035 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle3035_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3035_1 : CycleData E W := ⟨3,![1,19,13,14,2],![3,6,27,28,4]⟩
def cycle3035_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle3035_3 : CycleData E W := ⟨3,![4,20,21,6,5],![2,8,28,18,14]⟩
def cycle3035_4 : CycleData E W := ⟨2,![7,22,16,8],![3,18,38,16]⟩
def cycle3035_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data3035 : PartitionData E W := ⟨6,![cycle3035_0,cycle3035_1,cycle3035_2,cycle3035_3,cycle3035_4,cycle3035_5]⟩
lemma valid_data3035 : data3035.Valid src3035 dst3035 Finset.univ := by decide +kernel

def src3036 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3036 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3036_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3036_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3036_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3036_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3036_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3036_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3036 : PartitionData E W := ⟨6,![cycle3036_0,cycle3036_1,cycle3036_2,cycle3036_3,cycle3036_4,cycle3036_5]⟩
lemma valid_data3036 : data3036.Valid src3036 dst3036 Finset.univ := by decide +kernel

def src3037 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3037 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3037_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3037_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3037_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3037_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle3037_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3037_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3037 : PartitionData E W := ⟨6,![cycle3037_0,cycle3037_1,cycle3037_2,cycle3037_3,cycle3037_4,cycle3037_5]⟩
lemma valid_data3037 : data3037.Valid src3037 dst3037 Finset.univ := by decide +kernel

def src3038 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3038 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3038_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3038_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3038_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3038_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3038_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3038_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data3038 : PartitionData E W := ⟨6,![cycle3038_0,cycle3038_1,cycle3038_2,cycle3038_3,cycle3038_4,cycle3038_5]⟩
lemma valid_data3038 : data3038.Valid src3038 dst3038 Finset.univ := by decide +kernel

def src3039 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3039 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3039_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3039_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3039_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle3039_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3039_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3039_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3039 : PartitionData E W := ⟨6,![cycle3039_0,cycle3039_1,cycle3039_2,cycle3039_3,cycle3039_4,cycle3039_5]⟩
lemma valid_data3039 : data3039.Valid src3039 dst3039 Finset.univ := by decide +kernel

def src3040 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3040 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3040_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3040_1 : CycleData E W := ⟨3,![2,10,16,21,7],![3,4,26,38,18]⟩
def cycle3040_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3040_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3040_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3040_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3040 : PartitionData E W := ⟨6,![cycle3040_0,cycle3040_1,cycle3040_2,cycle3040_3,cycle3040_4,cycle3040_5]⟩
lemma valid_data3040 : data3040.Valid src3040 dst3040 Finset.univ := by decide +kernel

def src3041 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3041 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3041_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3041_1 : CycleData E W := ⟨2,![1,19,18,8],![3,6,27,16]⟩
def cycle3041_2 : CycleData E W := ⟨3,![2,10,16,22,7],![3,4,26,38,18]⟩
def cycle3041_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3041_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3041_5 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def data3041 : PartitionData E W := ⟨6,![cycle3041_0,cycle3041_1,cycle3041_2,cycle3041_3,cycle3041_4,cycle3041_5]⟩
lemma valid_data3041 : data3041.Valid src3041 dst3041 Finset.univ := by decide +kernel

def src3042 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3042 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3042_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3042_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3042_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3042_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3042_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle3042_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3042 : PartitionData E W := ⟨6,![cycle3042_0,cycle3042_1,cycle3042_2,cycle3042_3,cycle3042_4,cycle3042_5]⟩
lemma valid_data3042 : data3042.Valid src3042 dst3042 Finset.univ := by decide +kernel

def src3043 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3043 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3043_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3043_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle3043_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3043_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3043_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle3043_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3043 : PartitionData E W := ⟨6,![cycle3043_0,cycle3043_1,cycle3043_2,cycle3043_3,cycle3043_4,cycle3043_5]⟩
lemma valid_data3043 : data3043.Valid src3043 dst3043 Finset.univ := by decide +kernel

def src3044 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3044 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3044_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3044_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3044_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3044_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3044_4 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3044_5 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def data3044 : PartitionData E W := ⟨6,![cycle3044_0,cycle3044_1,cycle3044_2,cycle3044_3,cycle3044_4,cycle3044_5]⟩
lemma valid_data3044 : data3044.Valid src3044 dst3044 Finset.univ := by decide +kernel

def src3045 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst3045 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle3045_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3045_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3045_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3045_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle3045_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle3045_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3045 : PartitionData E W := ⟨6,![cycle3045_0,cycle3045_1,cycle3045_2,cycle3045_3,cycle3045_4,cycle3045_5]⟩
lemma valid_data3045 : data3045.Valid src3045 dst3045 Finset.univ := by decide +kernel

def src3046 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst3046 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle3046_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3046_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3046_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3046_3 : CycleData E W := ⟨3,![4,20,21,18,9],![2,8,18,38,16]⟩
def cycle3046_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle3046_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3046 : PartitionData E W := ⟨6,![cycle3046_0,cycle3046_1,cycle3046_2,cycle3046_3,cycle3046_4,cycle3046_5]⟩
lemma valid_data3046 : data3046.Valid src3046 dst3046 Finset.univ := by decide +kernel

def src3047 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst3047 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle3047_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3047_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3047_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3047_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle3047_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle3047_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data3047 : PartitionData E W := ⟨6,![cycle3047_0,cycle3047_1,cycle3047_2,cycle3047_3,cycle3047_4,cycle3047_5]⟩
lemma valid_data3047 : data3047.Valid src3047 dst3047 Finset.univ := by decide +kernel

def src3048 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst3048 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle3048_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3048_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3048_2 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,26,14]⟩
def cycle3048_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3048_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle3048_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3048 : PartitionData E W := ⟨6,![cycle3048_0,cycle3048_1,cycle3048_2,cycle3048_3,cycle3048_4,cycle3048_5]⟩
lemma valid_data3048 : data3048.Valid src3048 dst3048 Finset.univ := by decide +kernel

def src3049 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst3049 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle3049_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3049_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3049_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3049_3 : CycleData E W := ⟨2,![6,21,17,11],![14,18,38,26]⟩
def cycle3049_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle3049_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3049 : PartitionData E W := ⟨6,![cycle3049_0,cycle3049_1,cycle3049_2,cycle3049_3,cycle3049_4,cycle3049_5]⟩
lemma valid_data3049 : data3049.Valid src3049 dst3049 Finset.univ := by decide +kernel

def src3050 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst3050 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle3050_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3050_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3050_2 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle3050_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3050_4 : CycleData E W := ⟨3,![7,22,17,16,8],![3,18,38,26,16]⟩
def cycle3050_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data3050 : PartitionData E W := ⟨6,![cycle3050_0,cycle3050_1,cycle3050_2,cycle3050_3,cycle3050_4,cycle3050_5]⟩
lemma valid_data3050 : data3050.Valid src3050 dst3050 Finset.univ := by decide +kernel

def src3051 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst3051 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle3051_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3051_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3051_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3051_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3051_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle3051_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,27,28,38]⟩
def data3051 : PartitionData E W := ⟨6,![cycle3051_0,cycle3051_1,cycle3051_2,cycle3051_3,cycle3051_4,cycle3051_5]⟩
lemma valid_data3051 : data3051.Valid src3051 dst3051 Finset.univ := by decide +kernel

def src3052 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst3052 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle3052_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3052_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3052_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3052_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle3052_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle3052_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,27,28,38]⟩
def data3052 : PartitionData E W := ⟨6,![cycle3052_0,cycle3052_1,cycle3052_2,cycle3052_3,cycle3052_4,cycle3052_5]⟩
lemma valid_data3052 : data3052.Valid src3052 dst3052 Finset.univ := by decide +kernel

def src3053 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst3053 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle3053_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3053_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3053_2 : CycleData E W := ⟨2,![2,14,16,8],![3,4,27,16]⟩
def cycle3053_3 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle3053_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3053_5 : CycleData E W := ⟨3,![20,13,17,18,23],![8,28,27,26,38]⟩
def data3053 : PartitionData E W := ⟨6,![cycle3053_0,cycle3053_1,cycle3053_2,cycle3053_3,cycle3053_4,cycle3053_5]⟩
lemma valid_data3053 : data3053.Valid src3053 dst3053 Finset.univ := by decide +kernel

def src3054 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst3054 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle3054_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3054_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3054_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3054_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3054_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle3054_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data3054 : PartitionData E W := ⟨6,![cycle3054_0,cycle3054_1,cycle3054_2,cycle3054_3,cycle3054_4,cycle3054_5]⟩
lemma valid_data3054 : data3054.Valid src3054 dst3054 Finset.univ := by decide +kernel

def src3055 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst3055 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle3055_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3055_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3055_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3055_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle3055_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle3055_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data3055 : PartitionData E W := ⟨6,![cycle3055_0,cycle3055_1,cycle3055_2,cycle3055_3,cycle3055_4,cycle3055_5]⟩
lemma valid_data3055 : data3055.Valid src3055 dst3055 Finset.univ := by decide +kernel

def src3056 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst3056 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle3056_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3056_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle3056_2 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle3056_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3056_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3056_5 : CycleData E W := ⟨3,![7,22,17,16,8],![3,18,38,27,16]⟩
def data3056 : PartitionData E W := ⟨6,![cycle3056_0,cycle3056_1,cycle3056_2,cycle3056_3,cycle3056_4,cycle3056_5]⟩
lemma valid_data3056 : data3056.Valid src3056 dst3056 Finset.univ := by decide +kernel

def src3057 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst3057 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle3057_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3057_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3057_2 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,26,14]⟩
def cycle3057_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3057_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle3057_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,27]⟩
def data3057 : PartitionData E W := ⟨6,![cycle3057_0,cycle3057_1,cycle3057_2,cycle3057_3,cycle3057_4,cycle3057_5]⟩
lemma valid_data3057 : data3057.Valid src3057 dst3057 Finset.univ := by decide +kernel

def src3058 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst3058 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle3058_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3058_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3058_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3058_3 : CycleData E W := ⟨2,![6,21,17,11],![14,18,38,26]⟩
def cycle3058_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle3058_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,27]⟩
def data3058 : PartitionData E W := ⟨6,![cycle3058_0,cycle3058_1,cycle3058_2,cycle3058_3,cycle3058_4,cycle3058_5]⟩
lemma valid_data3058 : data3058.Valid src3058 dst3058 Finset.univ := by decide +kernel

def src3059 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst3059 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle3059_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3059_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3059_2 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle3059_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3059_4 : CycleData E W := ⟨2,![7,22,16,8],![3,18,38,16]⟩
def cycle3059_5 : CycleData E W := ⟨3,![20,13,18,17,23],![8,28,27,26,38]⟩
def data3059 : PartitionData E W := ⟨6,![cycle3059_0,cycle3059_1,cycle3059_2,cycle3059_3,cycle3059_4,cycle3059_5]⟩
lemma valid_data3059 : data3059.Valid src3059 dst3059 Finset.univ := by decide +kernel

def src3060 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3060 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3060_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3060_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3060_2 : CycleData E W := ⟨4,![4,23,19,15,11,5],![2,8,38,6,26,14]⟩
def cycle3060_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3060_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3060_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3060 : PartitionData E W := ⟨6,![cycle3060_0,cycle3060_1,cycle3060_2,cycle3060_3,cycle3060_4,cycle3060_5]⟩
lemma valid_data3060 : data3060.Valid src3060 dst3060 Finset.univ := by decide +kernel

def src3061 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3061 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3061_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3061_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3061_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3061_3 : CycleData E W := ⟨3,![15,11,6,21,19],![6,26,14,18,38]⟩
def cycle3061_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3061_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3061 : PartitionData E W := ⟨6,![cycle3061_0,cycle3061_1,cycle3061_2,cycle3061_3,cycle3061_4,cycle3061_5]⟩
lemma valid_data3061 : data3061.Valid src3061 dst3061 Finset.univ := by decide +kernel

def src3062 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3062 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3062_0 : CycleData E W := ⟨3,![0,15,10,3,4],![2,6,26,4,8]⟩
def cycle3062_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3062_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle3062_3 : CycleData E W := ⟨2,![5,11,16,9],![2,14,26,16]⟩
def cycle3062_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3062_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data3062 : PartitionData E W := ⟨6,![cycle3062_0,cycle3062_1,cycle3062_2,cycle3062_3,cycle3062_4,cycle3062_5]⟩
lemma valid_data3062 : data3062.Valid src3062 dst3062 Finset.univ := by decide +kernel

def src3063 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst3063 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle3063_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3063_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3063_2 : CycleData E W := ⟨4,![4,23,19,15,11,5],![2,8,38,6,26,14]⟩
def cycle3063_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3063_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle3063_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data3063 : PartitionData E W := ⟨6,![cycle3063_0,cycle3063_1,cycle3063_2,cycle3063_3,cycle3063_4,cycle3063_5]⟩
lemma valid_data3063 : data3063.Valid src3063 dst3063 Finset.univ := by decide +kernel

def src3064 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst3064 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle3064_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3064_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3064_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3064_3 : CycleData E W := ⟨3,![15,11,6,21,19],![6,26,14,18,38]⟩
def cycle3064_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle3064_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data3064 : PartitionData E W := ⟨6,![cycle3064_0,cycle3064_1,cycle3064_2,cycle3064_3,cycle3064_4,cycle3064_5]⟩
lemma valid_data3064 : data3064.Valid src3064 dst3064 Finset.univ := by decide +kernel

def src3065 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst3065 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle3065_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3065_1 : CycleData E W := ⟨2,![1,19,18,8],![3,6,38,16]⟩
def cycle3065_2 : CycleData E W := ⟨3,![2,3,23,22,7],![3,4,8,38,18]⟩
def cycle3065_3 : CycleData E W := ⟨3,![4,20,13,17,9],![2,8,28,27,16]⟩
def cycle3065_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3065_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data3065 : PartitionData E W := ⟨6,![cycle3065_0,cycle3065_1,cycle3065_2,cycle3065_3,cycle3065_4,cycle3065_5]⟩
lemma valid_data3065 : data3065.Valid src3065 dst3065 Finset.univ := by decide +kernel

def src3066 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3066 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3066_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3066_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3066_2 : CycleData E W := ⟨3,![4,23,16,11,5],![2,8,38,26,14]⟩
def cycle3066_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3066_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3066_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3066 : PartitionData E W := ⟨6,![cycle3066_0,cycle3066_1,cycle3066_2,cycle3066_3,cycle3066_4,cycle3066_5]⟩
lemma valid_data3066 : data3066.Valid src3066 dst3066 Finset.univ := by decide +kernel

def src3067 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3067 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3067_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3067_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3067_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3067_3 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle3067_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3067_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3067 : PartitionData E W := ⟨6,![cycle3067_0,cycle3067_1,cycle3067_2,cycle3067_3,cycle3067_4,cycle3067_5]⟩
lemma valid_data3067 : data3067.Valid src3067 dst3067 Finset.univ := by decide +kernel

def src3068 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3068 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3068_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3068_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3068_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle3068_3 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle3068_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3068_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data3068 : PartitionData E W := ⟨6,![cycle3068_0,cycle3068_1,cycle3068_2,cycle3068_3,cycle3068_4,cycle3068_5]⟩
lemma valid_data3068 : data3068.Valid src3068 dst3068 Finset.univ := by decide +kernel

def src3069 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3069 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3069_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3069_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3069_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3069_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3069_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3069_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3069 : PartitionData E W := ⟨6,![cycle3069_0,cycle3069_1,cycle3069_2,cycle3069_3,cycle3069_4,cycle3069_5]⟩
lemma valid_data3069 : data3069.Valid src3069 dst3069 Finset.univ := by decide +kernel

def src3070 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3070 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3070_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3070_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3070_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3070_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle3070_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3070_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3070 : PartitionData E W := ⟨6,![cycle3070_0,cycle3070_1,cycle3070_2,cycle3070_3,cycle3070_4,cycle3070_5]⟩
lemma valid_data3070 : data3070.Valid src3070 dst3070 Finset.univ := by decide +kernel

def src3071 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3071 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3071_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle3071_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3071_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,26,16]⟩
def cycle3071_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle3071_4 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle3071_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3071 : PartitionData E W := ⟨6,![cycle3071_0,cycle3071_1,cycle3071_2,cycle3071_3,cycle3071_4,cycle3071_5]⟩
lemma valid_data3071 : data3071.Valid src3071 dst3071 Finset.univ := by decide +kernel

def src3072 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst3072 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle3072_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3072_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3072_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3072_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3072_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3072_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data3072 : PartitionData E W := ⟨6,![cycle3072_0,cycle3072_1,cycle3072_2,cycle3072_3,cycle3072_4,cycle3072_5]⟩
lemma valid_data3072 : data3072.Valid src3072 dst3072 Finset.univ := by decide +kernel

def src3073 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst3073 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle3073_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3073_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3073_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3073_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle3073_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3073_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data3073 : PartitionData E W := ⟨6,![cycle3073_0,cycle3073_1,cycle3073_2,cycle3073_3,cycle3073_4,cycle3073_5]⟩
lemma valid_data3073 : data3073.Valid src3073 dst3073 Finset.univ := by decide +kernel

def src3074 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst3074 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle3074_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3074_1 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3074_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3074_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3074_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3074_5 : CycleData E W := ⟨3,![12,18,22,21,13],![14,27,38,18,28]⟩
def data3074 : PartitionData E W := ⟨6,![cycle3074_0,cycle3074_1,cycle3074_2,cycle3074_3,cycle3074_4,cycle3074_5]⟩
lemma valid_data3074 : data3074.Valid src3074 dst3074 Finset.univ := by decide +kernel

def src3075 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst3075 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle3075_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3075_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3075_2 : CycleData E W := ⟨4,![4,23,19,15,12,5],![2,8,38,6,27,14]⟩
def cycle3075_3 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle3075_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle3075_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data3075 : PartitionData E W := ⟨6,![cycle3075_0,cycle3075_1,cycle3075_2,cycle3075_3,cycle3075_4,cycle3075_5]⟩
lemma valid_data3075 : data3075.Valid src3075 dst3075 Finset.univ := by decide +kernel

def src3076 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst3076 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle3076_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3076_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3076_2 : CycleData E W := ⟨2,![4,23,13,5],![2,8,28,14]⟩
def cycle3076_3 : CycleData E W := ⟨3,![15,12,6,21,19],![6,27,14,18,38]⟩
def cycle3076_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle3076_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data3076 : PartitionData E W := ⟨6,![cycle3076_0,cycle3076_1,cycle3076_2,cycle3076_3,cycle3076_4,cycle3076_5]⟩
lemma valid_data3076 : data3076.Valid src3076 dst3076 Finset.univ := by decide +kernel

def src3077 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst3077 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle3077_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3077_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3077_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3077_3 : CycleData E W := ⟨2,![4,20,13,5],![2,8,28,14]⟩
def cycle3077_4 : CycleData E W := ⟨3,![15,12,6,22,19],![6,27,14,18,38]⟩
def cycle3077_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data3077 : PartitionData E W := ⟨6,![cycle3077_0,cycle3077_1,cycle3077_2,cycle3077_3,cycle3077_4,cycle3077_5]⟩
lemma valid_data3077 : data3077.Valid src3077 dst3077 Finset.univ := by decide +kernel

def src3078 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst3078 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle3078_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3078_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3078_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3078_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3078_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle3078_5 : CycleData E W := ⟨3,![15,16,11,22,19],![6,16,26,28,38]⟩
def data3078 : PartitionData E W := ⟨6,![cycle3078_0,cycle3078_1,cycle3078_2,cycle3078_3,cycle3078_4,cycle3078_5]⟩
lemma valid_data3078 : data3078.Valid src3078 dst3078 Finset.univ := by decide +kernel

def src3079 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst3079 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle3079_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3079_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3079_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3079_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3079_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle3079_5 : CycleData E W := ⟨3,![15,16,11,22,19],![6,16,26,28,38]⟩
def data3079 : PartitionData E W := ⟨6,![cycle3079_0,cycle3079_1,cycle3079_2,cycle3079_3,cycle3079_4,cycle3079_5]⟩
lemma valid_data3079 : data3079.Valid src3079 dst3079 Finset.univ := by decide +kernel

def src3080 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst3080 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle3080_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3080_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3080_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3080_3 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle3080_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3080_5 : CycleData E W := ⟨3,![20,11,17,18,23],![8,28,26,27,38]⟩
def data3080 : PartitionData E W := ⟨6,![cycle3080_0,cycle3080_1,cycle3080_2,cycle3080_3,cycle3080_4,cycle3080_5]⟩
lemma valid_data3080 : data3080.Valid src3080 dst3080 Finset.univ := by decide +kernel

def src3081 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst3081 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle3081_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3081_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3081_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3081_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3081_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle3081_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data3081 : PartitionData E W := ⟨6,![cycle3081_0,cycle3081_1,cycle3081_2,cycle3081_3,cycle3081_4,cycle3081_5]⟩
lemma valid_data3081 : data3081.Valid src3081 dst3081 Finset.univ := by decide +kernel

def src3082 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst3082 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle3082_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3082_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3082_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3082_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3082_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle3082_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data3082 : PartitionData E W := ⟨6,![cycle3082_0,cycle3082_1,cycle3082_2,cycle3082_3,cycle3082_4,cycle3082_5]⟩
lemma valid_data3082 : data3082.Valid src3082 dst3082 Finset.univ := by decide +kernel

def src3083 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst3083 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle3083_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3083_1 : CycleData E W := ⟨3,![1,19,13,6,7],![3,6,27,14,18]⟩
def cycle3083_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,26,16]⟩
def cycle3083_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3083_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle3083_5 : CycleData E W := ⟨2,![21,11,17,22],![18,28,26,38]⟩
def data3083 : PartitionData E W := ⟨6,![cycle3083_0,cycle3083_1,cycle3083_2,cycle3083_3,cycle3083_4,cycle3083_5]⟩
lemma valid_data3083 : data3083.Valid src3083 dst3083 Finset.univ := by decide +kernel

def src3084 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst3084 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle3084_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3084_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3084_2 : CycleData E W := ⟨3,![4,23,17,13,5],![2,8,38,27,14]⟩
def cycle3084_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3084_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle3084_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3084 : PartitionData E W := ⟨6,![cycle3084_0,cycle3084_1,cycle3084_2,cycle3084_3,cycle3084_4,cycle3084_5]⟩
lemma valid_data3084 : data3084.Valid src3084 dst3084 Finset.univ := by decide +kernel

def src3085 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst3085 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle3085_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3085_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3085_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3085_3 : CycleData E W := ⟨2,![6,21,17,13],![14,18,38,27]⟩
def cycle3085_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle3085_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3085 : PartitionData E W := ⟨6,![cycle3085_0,cycle3085_1,cycle3085_2,cycle3085_3,cycle3085_4,cycle3085_5]⟩
lemma valid_data3085 : data3085.Valid src3085 dst3085 Finset.univ := by decide +kernel

def src3086 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst3086 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle3086_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3086_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle3086_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle3086_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3086_4 : CycleData E W := ⟨3,![7,22,17,16,8],![3,18,38,27,16]⟩
def cycle3086_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data3086 : PartitionData E W := ⟨6,![cycle3086_0,cycle3086_1,cycle3086_2,cycle3086_3,cycle3086_4,cycle3086_5]⟩
lemma valid_data3086 : data3086.Valid src3086 dst3086 Finset.univ := by decide +kernel

def src3087 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst3087 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle3087_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3087_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3087_2 : CycleData E W := ⟨3,![4,23,17,13,5],![2,8,38,27,14]⟩
def cycle3087_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3087_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle3087_5 : CycleData E W := ⟨3,![15,16,22,11,19],![6,16,38,28,26]⟩
def data3087 : PartitionData E W := ⟨6,![cycle3087_0,cycle3087_1,cycle3087_2,cycle3087_3,cycle3087_4,cycle3087_5]⟩
lemma valid_data3087 : data3087.Valid src3087 dst3087 Finset.univ := by decide +kernel

def src3088 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst3088 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle3088_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3088_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3088_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3088_3 : CycleData E W := ⟨2,![6,21,17,13],![14,18,38,27]⟩
def cycle3088_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle3088_5 : CycleData E W := ⟨3,![15,16,22,11,19],![6,16,38,28,26]⟩
def data3088 : PartitionData E W := ⟨6,![cycle3088_0,cycle3088_1,cycle3088_2,cycle3088_3,cycle3088_4,cycle3088_5]⟩
lemma valid_data3088 : data3088.Valid src3088 dst3088 Finset.univ := by decide +kernel

def src3089 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst3089 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle3089_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3089_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle3089_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle3089_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3089_4 : CycleData E W := ⟨2,![7,22,16,8],![3,18,38,16]⟩
def cycle3089_5 : CycleData E W := ⟨3,![20,11,18,17,23],![8,28,26,27,38]⟩
def data3089 : PartitionData E W := ⟨6,![cycle3089_0,cycle3089_1,cycle3089_2,cycle3089_3,cycle3089_4,cycle3089_5]⟩
lemma valid_data3089 : data3089.Valid src3089 dst3089 Finset.univ := by decide +kernel

def src3090 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3090 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3090_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3090_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3090_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3090_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3090_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3090_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3090 : PartitionData E W := ⟨6,![cycle3090_0,cycle3090_1,cycle3090_2,cycle3090_3,cycle3090_4,cycle3090_5]⟩
lemma valid_data3090 : data3090.Valid src3090 dst3090 Finset.univ := by decide +kernel

def src3091 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3091 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3091_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3091_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3091_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3091_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3091_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3091_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3091 : PartitionData E W := ⟨6,![cycle3091_0,cycle3091_1,cycle3091_2,cycle3091_3,cycle3091_4,cycle3091_5]⟩
lemma valid_data3091 : data3091.Valid src3091 dst3091 Finset.univ := by decide +kernel

def src3092 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3092 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3092_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3092_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3092_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle3092_3 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,26]⟩
def cycle3092_4 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3092_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def data3092 : PartitionData E W := ⟨6,![cycle3092_0,cycle3092_1,cycle3092_2,cycle3092_3,cycle3092_4,cycle3092_5]⟩
lemma valid_data3092 : data3092.Valid src3092 dst3092 Finset.univ := by decide +kernel

def src3093 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3093 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3093_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3093_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3093_2 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3093_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3093_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3093_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3093 : PartitionData E W := ⟨6,![cycle3093_0,cycle3093_1,cycle3093_2,cycle3093_3,cycle3093_4,cycle3093_5]⟩
lemma valid_data3093 : data3093.Valid src3093 dst3093 Finset.univ := by decide +kernel

def src3094 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3094 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3094_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3094_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3094_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3094_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle3094_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3094_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data3094 : PartitionData E W := ⟨6,![cycle3094_0,cycle3094_1,cycle3094_2,cycle3094_3,cycle3094_4,cycle3094_5]⟩
lemma valid_data3094 : data3094.Valid src3094 dst3094 Finset.univ := by decide +kernel

def src3095 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3095 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3095_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3095_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3095_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,26]⟩
def cycle3095_3 : CycleData E W := ⟨3,![4,23,18,13,5],![2,8,38,27,14]⟩
def cycle3095_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3095_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data3095 : PartitionData E W := ⟨6,![cycle3095_0,cycle3095_1,cycle3095_2,cycle3095_3,cycle3095_4,cycle3095_5]⟩
lemma valid_data3095 : data3095.Valid src3095 dst3095 Finset.univ := by decide +kernel

def src3096 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3096 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3096_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3096_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3096_2 : CycleData E W := ⟨4,![4,23,19,15,13,5],![2,8,38,6,27,14]⟩
def cycle3096_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3096_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3096_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3096 : PartitionData E W := ⟨6,![cycle3096_0,cycle3096_1,cycle3096_2,cycle3096_3,cycle3096_4,cycle3096_5]⟩
lemma valid_data3096 : data3096.Valid src3096 dst3096 Finset.univ := by decide +kernel

def src3097 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3097 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3097_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3097_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3097_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3097_3 : CycleData E W := ⟨3,![15,13,6,21,19],![6,27,14,18,38]⟩
def cycle3097_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3097_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3097 : PartitionData E W := ⟨6,![cycle3097_0,cycle3097_1,cycle3097_2,cycle3097_3,cycle3097_4,cycle3097_5]⟩
lemma valid_data3097 : data3097.Valid src3097 dst3097 Finset.univ := by decide +kernel

def src3098 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3098 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3098_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3098_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3098_2 : CycleData E W := ⟨3,![4,3,2,8,9],![2,8,4,3,16]⟩
def cycle3098_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3098_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3098_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data3098 : PartitionData E W := ⟨6,![cycle3098_0,cycle3098_1,cycle3098_2,cycle3098_3,cycle3098_4,cycle3098_5]⟩
lemma valid_data3098 : data3098.Valid src3098 dst3098 Finset.univ := by decide +kernel

def src3099 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst3099 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle3099_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3099_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3099_2 : CycleData E W := ⟨4,![4,23,19,15,13,5],![2,8,38,6,27,14]⟩
def cycle3099_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3099_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle3099_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data3099 : PartitionData E W := ⟨6,![cycle3099_0,cycle3099_1,cycle3099_2,cycle3099_3,cycle3099_4,cycle3099_5]⟩
lemma valid_data3099 : data3099.Valid src3099 dst3099 Finset.univ := by decide +kernel

def src3100 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst3100 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle3100_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3100_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3100_2 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle3100_3 : CycleData E W := ⟨3,![15,13,6,21,19],![6,27,14,18,38]⟩
def cycle3100_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle3100_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data3100 : PartitionData E W := ⟨6,![cycle3100_0,cycle3100_1,cycle3100_2,cycle3100_3,cycle3100_4,cycle3100_5]⟩
lemma valid_data3100 : data3100.Valid src3100 dst3100 Finset.univ := by decide +kernel

def src3101 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst3101 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle3101_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3101_1 : CycleData E W := ⟨2,![1,19,18,8],![3,6,38,16]⟩
def cycle3101_2 : CycleData E W := ⟨3,![2,3,23,22,7],![3,4,8,38,18]⟩
def cycle3101_3 : CycleData E W := ⟨3,![4,20,11,17,9],![2,8,28,26,16]⟩
def cycle3101_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle3101_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data3101 : PartitionData E W := ⟨6,![cycle3101_0,cycle3101_1,cycle3101_2,cycle3101_3,cycle3101_4,cycle3101_5]⟩
lemma valid_data3101 : data3101.Valid src3101 dst3101 Finset.univ := by decide +kernel

def src3102 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst3102 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle3102_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3102_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3102_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3102_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3102_4 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def cycle3102_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,26,28,38]⟩
def data3102 : PartitionData E W := ⟨6,![cycle3102_0,cycle3102_1,cycle3102_2,cycle3102_3,cycle3102_4,cycle3102_5]⟩
lemma valid_data3102 : data3102.Valid src3102 dst3102 Finset.univ := by decide +kernel

def src3103 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst3103 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle3103_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3103_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle3103_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3103_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3103_4 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def cycle3103_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,16,26,28,38]⟩
def data3103 : PartitionData E W := ⟨6,![cycle3103_0,cycle3103_1,cycle3103_2,cycle3103_3,cycle3103_4,cycle3103_5]⟩
lemma valid_data3103 : data3103.Valid src3103 dst3103 Finset.univ := by decide +kernel

def src3104 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst3104 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle3104_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3104_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,27,4]⟩
def cycle3104_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3104_3 : CycleData E W := ⟨3,![4,23,22,6,5],![2,8,38,18,14]⟩
def cycle3104_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def cycle3104_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data3104 : PartitionData E W := ⟨6,![cycle3104_0,cycle3104_1,cycle3104_2,cycle3104_3,cycle3104_4,cycle3104_5]⟩
lemma valid_data3104 : data3104.Valid src3104 dst3104 Finset.univ := by decide +kernel

def src3105 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst3105 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle3105_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3105_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3105_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3105_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3105_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,26,14,27]⟩
def cycle3105_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data3105 : PartitionData E W := ⟨6,![cycle3105_0,cycle3105_1,cycle3105_2,cycle3105_3,cycle3105_4,cycle3105_5]⟩
lemma valid_data3105 : data3105.Valid src3105 dst3105 Finset.univ := by decide +kernel

def src3106 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst3106 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle3106_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3106_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle3106_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3106_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3106_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,26,14,27]⟩
def cycle3106_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data3106 : PartitionData E W := ⟨6,![cycle3106_0,cycle3106_1,cycle3106_2,cycle3106_3,cycle3106_4,cycle3106_5]⟩
lemma valid_data3106 : data3106.Valid src3106 dst3106 Finset.univ := by decide +kernel

def src3107 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst3107 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle3107_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3107_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle3107_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3107_3 : CycleData E W := ⟨3,![4,23,17,12,5],![2,8,38,26,14]⟩
def cycle3107_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle3107_5 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def data3107 : PartitionData E W := ⟨6,![cycle3107_0,cycle3107_1,cycle3107_2,cycle3107_3,cycle3107_4,cycle3107_5]⟩
lemma valid_data3107 : data3107.Valid src3107 dst3107 Finset.univ := by decide +kernel

def src3108 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst3108 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle3108_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3108_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3108_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,27]⟩
def cycle3108_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3108_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,27,14,26]⟩
def cycle3108_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data3108 : PartitionData E W := ⟨6,![cycle3108_0,cycle3108_1,cycle3108_2,cycle3108_3,cycle3108_4,cycle3108_5]⟩
lemma valid_data3108 : data3108.Valid src3108 dst3108 Finset.univ := by decide +kernel

def src3109 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst3109 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle3109_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3109_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,27,38,18]⟩
def cycle3109_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3109_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3109_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,27,14,26]⟩
def cycle3109_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data3109 : PartitionData E W := ⟨6,![cycle3109_0,cycle3109_1,cycle3109_2,cycle3109_3,cycle3109_4,cycle3109_5]⟩
lemma valid_data3109 : data3109.Valid src3109 dst3109 Finset.univ := by decide +kernel

def src3110 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst3110 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle3110_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3110_1 : CycleData E W := ⟨3,![1,19,12,6,7],![3,6,26,14,18]⟩
def cycle3110_2 : CycleData E W := ⟨2,![2,10,16,8],![3,4,27,16]⟩
def cycle3110_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3110_4 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,27,14]⟩
def cycle3110_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data3110 : PartitionData E W := ⟨6,![cycle3110_0,cycle3110_1,cycle3110_2,cycle3110_3,cycle3110_4,cycle3110_5]⟩
lemma valid_data3110 : data3110.Valid src3110 dst3110 Finset.univ := by decide +kernel

def src3111 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst3111 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle3111_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3111_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3111_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,27]⟩
def cycle3111_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3111_4 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def cycle3111_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,26]⟩
def data3111 : PartitionData E W := ⟨6,![cycle3111_0,cycle3111_1,cycle3111_2,cycle3111_3,cycle3111_4,cycle3111_5]⟩
lemma valid_data3111 : data3111.Valid src3111 dst3111 Finset.univ := by decide +kernel

def src3112 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst3112 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle3112_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3112_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,27,38,18]⟩
def cycle3112_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3112_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3112_4 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def cycle3112_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,16,38,28,26]⟩
def data3112 : PartitionData E W := ⟨6,![cycle3112_0,cycle3112_1,cycle3112_2,cycle3112_3,cycle3112_4,cycle3112_5]⟩
lemma valid_data3112 : data3112.Valid src3112 dst3112 Finset.univ := by decide +kernel

def src3113 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst3113 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle3113_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle3113_1 : CycleData E W := ⟨3,![1,19,13,14,2],![3,6,26,28,4]⟩
def cycle3113_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,27]⟩
def cycle3113_3 : CycleData E W := ⟨3,![4,20,21,6,5],![2,8,28,18,14]⟩
def cycle3113_4 : CycleData E W := ⟨2,![7,22,16,8],![3,18,38,16]⟩
def cycle3113_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data3113 : PartitionData E W := ⟨6,![cycle3113_0,cycle3113_1,cycle3113_2,cycle3113_3,cycle3113_4,cycle3113_5]⟩
lemma valid_data3113 : data3113.Valid src3113 dst3113 Finset.univ := by decide +kernel

def src3114 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3114 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3114_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3114_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3114_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3114_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3114_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle3114_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3114 : PartitionData E W := ⟨6,![cycle3114_0,cycle3114_1,cycle3114_2,cycle3114_3,cycle3114_4,cycle3114_5]⟩
lemma valid_data3114 : data3114.Valid src3114 dst3114 Finset.univ := by decide +kernel

def src3115 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3115 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3115_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3115_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle3115_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3115_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3115_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle3115_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3115 : PartitionData E W := ⟨6,![cycle3115_0,cycle3115_1,cycle3115_2,cycle3115_3,cycle3115_4,cycle3115_5]⟩
lemma valid_data3115 : data3115.Valid src3115 dst3115 Finset.univ := by decide +kernel

def src3116 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3116 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3116_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle3116_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle3116_2 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3116_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3116_4 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle3116_5 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def data3116 : PartitionData E W := ⟨6,![cycle3116_0,cycle3116_1,cycle3116_2,cycle3116_3,cycle3116_4,cycle3116_5]⟩
lemma valid_data3116 : data3116.Valid src3116 dst3116 Finset.univ := by decide +kernel

def src3117 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3117 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3117_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3117_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3117_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3117_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3117_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3117_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data3117 : PartitionData E W := ⟨6,![cycle3117_0,cycle3117_1,cycle3117_2,cycle3117_3,cycle3117_4,cycle3117_5]⟩
lemma valid_data3117 : data3117.Valid src3117 dst3117 Finset.univ := by decide +kernel

def src3118 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3118 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3118_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3118_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle3118_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3118_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle3118_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3118_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data3118 : PartitionData E W := ⟨6,![cycle3118_0,cycle3118_1,cycle3118_2,cycle3118_3,cycle3118_4,cycle3118_5]⟩
lemma valid_data3118 : data3118.Valid src3118 dst3118 Finset.univ := by decide +kernel

def src3119 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3119 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3119_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3119_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle3119_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3119_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3119_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle3119_5 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def data3119 : PartitionData E W := ⟨6,![cycle3119_0,cycle3119_1,cycle3119_2,cycle3119_3,cycle3119_4,cycle3119_5]⟩
lemma valid_data3119 : data3119.Valid src3119 dst3119 Finset.univ := by decide +kernel

def src3120 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst3120 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle3120_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3120_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3120_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3120_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle3120_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle3120_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3120 : PartitionData E W := ⟨6,![cycle3120_0,cycle3120_1,cycle3120_2,cycle3120_3,cycle3120_4,cycle3120_5]⟩
lemma valid_data3120 : data3120.Valid src3120 dst3120 Finset.univ := by decide +kernel

def src3121 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst3121 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle3121_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3121_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3121_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3121_3 : CycleData E W := ⟨3,![4,20,21,18,9],![2,8,18,38,16]⟩
def cycle3121_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle3121_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3121 : PartitionData E W := ⟨6,![cycle3121_0,cycle3121_1,cycle3121_2,cycle3121_3,cycle3121_4,cycle3121_5]⟩
lemma valid_data3121 : data3121.Valid src3121 dst3121 Finset.univ := by decide +kernel

def src3122 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst3122 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle3122_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3122_1 : CycleData E W := ⟨2,![2,10,17,8],![3,4,27,16]⟩
def cycle3122_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3122_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle3122_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle3122_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data3122 : PartitionData E W := ⟨6,![cycle3122_0,cycle3122_1,cycle3122_2,cycle3122_3,cycle3122_4,cycle3122_5]⟩
lemma valid_data3122 : data3122.Valid src3122 dst3122 Finset.univ := by decide +kernel

def src3123 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3123 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3123_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3123_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3123_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3123_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3123_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3123_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3123 : PartitionData E W := ⟨6,![cycle3123_0,cycle3123_1,cycle3123_2,cycle3123_3,cycle3123_4,cycle3123_5]⟩
lemma valid_data3123 : data3123.Valid src3123 dst3123 Finset.univ := by decide +kernel

def src3124 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3124 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3124_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3124_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3124_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3124_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle3124_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3124_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3124 : PartitionData E W := ⟨6,![cycle3124_0,cycle3124_1,cycle3124_2,cycle3124_3,cycle3124_4,cycle3124_5]⟩
lemma valid_data3124 : data3124.Valid src3124 dst3124 Finset.univ := by decide +kernel

def src3125 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3125 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3125_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3125_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3125_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3125_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3125_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3125_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3125 : PartitionData E W := ⟨6,![cycle3125_0,cycle3125_1,cycle3125_2,cycle3125_3,cycle3125_4,cycle3125_5]⟩
lemma valid_data3125 : data3125.Valid src3125 dst3125 Finset.univ := by decide +kernel

def src3126 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst3126 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle3126_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3126_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3126_2 : CycleData E W := ⟨4,![4,23,19,15,12,5],![2,8,38,6,26,14]⟩
def cycle3126_3 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle3126_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3126_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data3126 : PartitionData E W := ⟨6,![cycle3126_0,cycle3126_1,cycle3126_2,cycle3126_3,cycle3126_4,cycle3126_5]⟩
lemma valid_data3126 : data3126.Valid src3126 dst3126 Finset.univ := by decide +kernel

def src3127 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst3127 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle3127_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3127_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle3127_2 : CycleData E W := ⟨2,![4,23,13,5],![2,8,28,14]⟩
def cycle3127_3 : CycleData E W := ⟨3,![15,12,6,21,19],![6,26,14,18,38]⟩
def cycle3127_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3127_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data3127 : PartitionData E W := ⟨6,![cycle3127_0,cycle3127_1,cycle3127_2,cycle3127_3,cycle3127_4,cycle3127_5]⟩
lemma valid_data3127 : data3127.Valid src3127 dst3127 Finset.univ := by decide +kernel

def src3128 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst3128 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle3128_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle3128_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle3128_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3128_3 : CycleData E W := ⟨2,![4,20,13,5],![2,8,28,14]⟩
def cycle3128_4 : CycleData E W := ⟨3,![15,12,6,22,19],![6,26,14,18,38]⟩
def cycle3128_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data3128 : PartitionData E W := ⟨6,![cycle3128_0,cycle3128_1,cycle3128_2,cycle3128_3,cycle3128_4,cycle3128_5]⟩
lemma valid_data3128 : data3128.Valid src3128 dst3128 Finset.univ := by decide +kernel

def src3129 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst3129 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle3129_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3129_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3129_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle3129_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3129_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3129_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data3129 : PartitionData E W := ⟨6,![cycle3129_0,cycle3129_1,cycle3129_2,cycle3129_3,cycle3129_4,cycle3129_5]⟩
lemma valid_data3129 : data3129.Valid src3129 dst3129 Finset.univ := by decide +kernel

def src3130 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst3130 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle3130_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3130_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3130_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3130_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle3130_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3130_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data3130 : PartitionData E W := ⟨6,![cycle3130_0,cycle3130_1,cycle3130_2,cycle3130_3,cycle3130_4,cycle3130_5]⟩
lemma valid_data3130 : data3130.Valid src3130 dst3130 Finset.univ := by decide +kernel

def src3131 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst3131 : E → W := ![6,3,4,8,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle3131_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,18,14]⟩
def cycle3131_1 : CycleData E W := ⟨2,![2,10,18,8],![3,4,27,16]⟩
def cycle3131_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3131_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle3131_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle3131_5 : CycleData E W := ⟨3,![12,16,22,21,13],![14,26,38,18,28]⟩
def data3131 : PartitionData E W := ⟨6,![cycle3131_0,cycle3131_1,cycle3131_2,cycle3131_3,cycle3131_4,cycle3131_5]⟩
lemma valid_data3131 : data3131.Valid src3131 dst3131 Finset.univ := by decide +kernel

def src3132 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3132 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3132_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3132_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3132_2 : CycleData E W := ⟨3,![3,23,17,16,10],![4,8,38,16,26]⟩
def cycle3132_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3132_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3132_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3132 : PartitionData E W := ⟨6,![cycle3132_0,cycle3132_1,cycle3132_2,cycle3132_3,cycle3132_4,cycle3132_5]⟩
lemma valid_data3132 : data3132.Valid src3132 dst3132 Finset.univ := by decide +kernel

def src3133 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3133 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3133_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3133_1 : CycleData E W := ⟨4,![2,10,16,17,21,8],![3,4,26,16,38,18]⟩
def cycle3133_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3133_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3133_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3133_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3133 : PartitionData E W := ⟨6,![cycle3133_0,cycle3133_1,cycle3133_2,cycle3133_3,cycle3133_4,cycle3133_5]⟩
lemma valid_data3133 : data3133.Valid src3133 dst3133 Finset.univ := by decide +kernel

def src3134 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3134 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3134_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3134_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3134_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3134_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3134_4 : CycleData E W := ⟨3,![15,16,6,12,19],![6,26,16,14,27]⟩
def cycle3134_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data3134 : PartitionData E W := ⟨6,![cycle3134_0,cycle3134_1,cycle3134_2,cycle3134_3,cycle3134_4,cycle3134_5]⟩
lemma valid_data3134 : data3134.Valid src3134 dst3134 Finset.univ := by decide +kernel

def src3135 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3135 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3135_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3135_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3135_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle3135_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3135_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3135_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3135 : PartitionData E W := ⟨6,![cycle3135_0,cycle3135_1,cycle3135_2,cycle3135_3,cycle3135_4,cycle3135_5]⟩
lemma valid_data3135 : data3135.Valid src3135 dst3135 Finset.univ := by decide +kernel

def src3136 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3136 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3136_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3136_1 : CycleData E W := ⟨3,![2,10,16,21,8],![3,4,26,38,18]⟩
def cycle3136_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3136_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3136_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3136_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3136 : PartitionData E W := ⟨6,![cycle3136_0,cycle3136_1,cycle3136_2,cycle3136_3,cycle3136_4,cycle3136_5]⟩
lemma valid_data3136 : data3136.Valid src3136 dst3136 Finset.univ := by decide +kernel

def src3137 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3137 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3137_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3137_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3137_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3137_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3137_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle3137_5 : CycleData E W := ⟨4,![15,16,22,21,13,19],![6,26,38,18,28,27]⟩
def data3137 : PartitionData E W := ⟨6,![cycle3137_0,cycle3137_1,cycle3137_2,cycle3137_3,cycle3137_4,cycle3137_5]⟩
lemma valid_data3137 : data3137.Valid src3137 dst3137 Finset.univ := by decide +kernel

def src3138 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3138 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3138_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3138_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3138_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3138_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3138_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle3138_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3138 : PartitionData E W := ⟨6,![cycle3138_0,cycle3138_1,cycle3138_2,cycle3138_3,cycle3138_4,cycle3138_5]⟩
lemma valid_data3138 : data3138.Valid src3138 dst3138 Finset.univ := by decide +kernel

def src3139 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3139 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3139_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3139_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,26,38,18]⟩
def cycle3139_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3139_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3139_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle3139_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3139 : PartitionData E W := ⟨6,![cycle3139_0,cycle3139_1,cycle3139_2,cycle3139_3,cycle3139_4,cycle3139_5]⟩
lemma valid_data3139 : data3139.Valid src3139 dst3139 Finset.univ := by decide +kernel

def src3140 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3140 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3140_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3140_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3140_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3140_3 : CycleData E W := ⟨3,![4,23,18,17,5],![2,8,38,26,16]⟩
def cycle3140_4 : CycleData E W := ⟨1,![6,16,12],![14,16,27]⟩
def cycle3140_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data3140 : PartitionData E W := ⟨6,![cycle3140_0,cycle3140_1,cycle3140_2,cycle3140_3,cycle3140_4,cycle3140_5]⟩
lemma valid_data3140 : data3140.Valid src3140 dst3140 Finset.univ := by decide +kernel

def src3141 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3141 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3141_0 : CycleData E W := ⟨3,![0,15,11,6,5],![2,6,26,14,16]⟩
def cycle3141_1 : CycleData E W := ⟨3,![1,19,23,3,2],![3,6,38,8,4]⟩
def cycle3141_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3141_3 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle3141_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3141_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3141 : PartitionData E W := ⟨6,![cycle3141_0,cycle3141_1,cycle3141_2,cycle3141_3,cycle3141_4,cycle3141_5]⟩
lemma valid_data3141 : data3141.Valid src3141 dst3141 Finset.univ := by decide +kernel

def src3142 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3142 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3142_0 : CycleData E W := ⟨3,![0,15,11,6,5],![2,6,26,14,16]⟩
def cycle3142_1 : CycleData E W := ⟨2,![1,19,21,8],![3,6,38,18]⟩
def cycle3142_2 : CycleData E W := ⟨3,![2,3,23,12,7],![3,4,8,28,14]⟩
def cycle3142_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3142_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle3142_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3142 : PartitionData E W := ⟨6,![cycle3142_0,cycle3142_1,cycle3142_2,cycle3142_3,cycle3142_4,cycle3142_5]⟩
lemma valid_data3142 : data3142.Valid src3142 dst3142 Finset.univ := by decide +kernel

def src3143 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3143 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3143_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3143_1 : CycleData E W := ⟨2,![1,19,22,8],![3,6,38,18]⟩
def cycle3143_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle3143_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3143_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3143_5 : CycleData E W := ⟨2,![6,17,13,12],![14,16,27,28]⟩
def data3143 : PartitionData E W := ⟨6,![cycle3143_0,cycle3143_1,cycle3143_2,cycle3143_3,cycle3143_4,cycle3143_5]⟩
lemma valid_data3143 : data3143.Valid src3143 dst3143 Finset.univ := by decide +kernel

def src3144 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3144 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3144_0 : CycleData E W := ⟨3,![0,15,11,6,5],![2,6,26,14,16]⟩
def cycle3144_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3144_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle3144_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3144_4 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle3144_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data3144 : PartitionData E W := ⟨6,![cycle3144_0,cycle3144_1,cycle3144_2,cycle3144_3,cycle3144_4,cycle3144_5]⟩
lemma valid_data3144 : data3144.Valid src3144 dst3144 Finset.univ := by decide +kernel

def src3145 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3145 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3145_0 : CycleData E W := ⟨2,![0,19,18,5],![2,6,27,16]⟩
def cycle3145_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle3145_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle3145_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3145_4 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def cycle3145_5 : CycleData E W := ⟨3,![7,12,22,21,8],![3,14,28,38,18]⟩
def data3145 : PartitionData E W := ⟨6,![cycle3145_0,cycle3145_1,cycle3145_2,cycle3145_3,cycle3145_4,cycle3145_5]⟩
lemma valid_data3145 : data3145.Valid src3145 dst3145 Finset.univ := by decide +kernel

def src3146 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3146 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3146_0 : CycleData E W := ⟨2,![0,19,18,5],![2,6,27,16]⟩
def cycle3146_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle3146_2 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle3146_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3146_4 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def cycle3146_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data3146 : PartitionData E W := ⟨6,![cycle3146_0,cycle3146_1,cycle3146_2,cycle3146_3,cycle3146_4,cycle3146_5]⟩
lemma valid_data3146 : data3146.Valid src3146 dst3146 Finset.univ := by decide +kernel

def src3147 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3147 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3147_0 : CycleData E W := ⟨4,![0,1,2,14,16,5],![2,6,3,4,27,16]⟩
def cycle3147_1 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3147_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3147_3 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle3147_4 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle3147_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3147 : PartitionData E W := ⟨6,![cycle3147_0,cycle3147_1,cycle3147_2,cycle3147_3,cycle3147_4,cycle3147_5]⟩
lemma valid_data3147 : data3147.Valid src3147 dst3147 Finset.univ := by decide +kernel

def src3148 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3148 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3148_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3148_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,26,4]⟩
def cycle3148_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle3148_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3148_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle3148_5 : CycleData E W := ⟨3,![7,12,22,21,8],![3,14,28,38,18]⟩
def data3148 : PartitionData E W := ⟨6,![cycle3148_0,cycle3148_1,cycle3148_2,cycle3148_3,cycle3148_4,cycle3148_5]⟩
lemma valid_data3148 : data3148.Valid src3148 dst3148 Finset.univ := by decide +kernel

def src3149 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3149 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3149_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3149_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,26,4]⟩
def cycle3149_2 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle3149_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3149_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle3149_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data3149 : PartitionData E W := ⟨6,![cycle3149_0,cycle3149_1,cycle3149_2,cycle3149_3,cycle3149_4,cycle3149_5]⟩
lemma valid_data3149 : data3149.Valid src3149 dst3149 Finset.univ := by decide +kernel

def src3150 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3150 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3150_0 : CycleData E W := ⟨4,![0,1,2,10,16,5],![2,6,3,4,26,16]⟩
def cycle3150_1 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3150_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3150_3 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle3150_4 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle3150_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3150 : PartitionData E W := ⟨6,![cycle3150_0,cycle3150_1,cycle3150_2,cycle3150_3,cycle3150_4,cycle3150_5]⟩
lemma valid_data3150 : data3150.Valid src3150 dst3150 Finset.univ := by decide +kernel

def src3151 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3151 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3151_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3151_1 : CycleData E W := ⟨3,![1,19,18,14,2],![3,6,38,27,4]⟩
def cycle3151_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,26]⟩
def cycle3151_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3151_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle3151_5 : CycleData E W := ⟨3,![7,12,22,21,8],![3,14,28,38,18]⟩
def data3151 : PartitionData E W := ⟨6,![cycle3151_0,cycle3151_1,cycle3151_2,cycle3151_3,cycle3151_4,cycle3151_5]⟩
lemma valid_data3151 : data3151.Valid src3151 dst3151 Finset.univ := by decide +kernel

def src3152 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3152 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3152_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3152_1 : CycleData E W := ⟨3,![1,19,18,14,2],![3,6,38,27,4]⟩
def cycle3152_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,26]⟩
def cycle3152_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3152_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle3152_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data3152 : PartitionData E W := ⟨6,![cycle3152_0,cycle3152_1,cycle3152_2,cycle3152_3,cycle3152_4,cycle3152_5]⟩
lemma valid_data3152 : data3152.Valid src3152 dst3152 Finset.univ := by decide +kernel

def src3153 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3153 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3153_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3153_1 : CycleData E W := ⟨2,![1,19,13,7],![3,6,27,14]⟩
def cycle3153_2 : CycleData E W := ⟨3,![2,10,11,21,8],![3,4,26,28,18]⟩
def cycle3153_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle3153_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3153_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data3153 : PartitionData E W := ⟨6,![cycle3153_0,cycle3153_1,cycle3153_2,cycle3153_3,cycle3153_4,cycle3153_5]⟩
lemma valid_data3153 : data3153.Valid src3153 dst3153 Finset.univ := by decide +kernel

def src3154 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3154 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3154_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3154_1 : CycleData E W := ⟨2,![1,19,13,7],![3,6,27,14]⟩
def cycle3154_2 : CycleData E W := ⟨3,![2,14,18,21,8],![3,4,27,38,18]⟩
def cycle3154_3 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,26]⟩
def cycle3154_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3154_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data3154 : PartitionData E W := ⟨6,![cycle3154_0,cycle3154_1,cycle3154_2,cycle3154_3,cycle3154_4,cycle3154_5]⟩
lemma valid_data3154 : data3154.Valid src3154 dst3154 Finset.univ := by decide +kernel

def src3155 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3155 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3155_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,26,16]⟩
def cycle3155_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle3155_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,26]⟩
def cycle3155_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3155_4 : CycleData E W := ⟨2,![6,17,18,13],![14,16,38,27]⟩
def cycle3155_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data3155 : PartitionData E W := ⟨6,![cycle3155_0,cycle3155_1,cycle3155_2,cycle3155_3,cycle3155_4,cycle3155_5]⟩
lemma valid_data3155 : data3155.Valid src3155 dst3155 Finset.univ := by decide +kernel

def src3156 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3156 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3156_0 : CycleData E W := ⟨3,![0,15,13,6,5],![2,6,27,14,16]⟩
def cycle3156_1 : CycleData E W := ⟨3,![1,19,23,3,2],![3,6,38,8,4]⟩
def cycle3156_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3156_3 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle3156_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3156_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3156 : PartitionData E W := ⟨6,![cycle3156_0,cycle3156_1,cycle3156_2,cycle3156_3,cycle3156_4,cycle3156_5]⟩
lemma valid_data3156 : data3156.Valid src3156 dst3156 Finset.univ := by decide +kernel

def src3157 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3157 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3157_0 : CycleData E W := ⟨3,![0,15,13,6,5],![2,6,27,14,16]⟩
def cycle3157_1 : CycleData E W := ⟨2,![1,19,21,8],![3,6,38,18]⟩
def cycle3157_2 : CycleData E W := ⟨3,![2,3,23,12,7],![3,4,8,28,14]⟩
def cycle3157_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3157_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle3157_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3157 : PartitionData E W := ⟨6,![cycle3157_0,cycle3157_1,cycle3157_2,cycle3157_3,cycle3157_4,cycle3157_5]⟩
lemma valid_data3157 : data3157.Valid src3157 dst3157 Finset.univ := by decide +kernel

def src3158 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3158 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3158_0 : CycleData E W := ⟨2,![0,15,16,5],![2,6,27,16]⟩
def cycle3158_1 : CycleData E W := ⟨2,![1,19,22,8],![3,6,38,18]⟩
def cycle3158_2 : CycleData E W := ⟨2,![2,14,13,7],![3,4,27,14]⟩
def cycle3158_3 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle3158_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3158_5 : CycleData E W := ⟨2,![6,17,11,12],![14,16,26,28]⟩
def data3158 : PartitionData E W := ⟨6,![cycle3158_0,cycle3158_1,cycle3158_2,cycle3158_3,cycle3158_4,cycle3158_5]⟩
lemma valid_data3158 : data3158.Valid src3158 dst3158 Finset.univ := by decide +kernel

def src3159 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3159 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3159_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3159_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3159_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3159_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3159_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle3159_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3159 : PartitionData E W := ⟨6,![cycle3159_0,cycle3159_1,cycle3159_2,cycle3159_3,cycle3159_4,cycle3159_5]⟩
lemma valid_data3159 : data3159.Valid src3159 dst3159 Finset.univ := by decide +kernel

def src3160 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3160 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3160_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3160_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,27,38,18]⟩
def cycle3160_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3160_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3160_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle3160_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3160 : PartitionData E W := ⟨6,![cycle3160_0,cycle3160_1,cycle3160_2,cycle3160_3,cycle3160_4,cycle3160_5]⟩
lemma valid_data3160 : data3160.Valid src3160 dst3160 Finset.univ := by decide +kernel

def src3161 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3161 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3161_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3161_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,27,14]⟩
def cycle3161_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3161_3 : CycleData E W := ⟨3,![4,23,18,17,5],![2,8,38,27,16]⟩
def cycle3161_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle3161_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data3161 : PartitionData E W := ⟨6,![cycle3161_0,cycle3161_1,cycle3161_2,cycle3161_3,cycle3161_4,cycle3161_5]⟩
lemma valid_data3161 : data3161.Valid src3161 dst3161 Finset.univ := by decide +kernel

def src3162 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3162 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3162_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3162_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3162_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle3162_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3162_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3162_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data3162 : PartitionData E W := ⟨6,![cycle3162_0,cycle3162_1,cycle3162_2,cycle3162_3,cycle3162_4,cycle3162_5]⟩
lemma valid_data3162 : data3162.Valid src3162 dst3162 Finset.univ := by decide +kernel

def src3163 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3163 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3163_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3163_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,27,38,18]⟩
def cycle3163_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3163_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3163_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3163_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data3163 : PartitionData E W := ⟨6,![cycle3163_0,cycle3163_1,cycle3163_2,cycle3163_3,cycle3163_4,cycle3163_5]⟩
lemma valid_data3163 : data3163.Valid src3163 dst3163 Finset.univ := by decide +kernel

def src3164 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst3164 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle3164_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3164_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,27,14]⟩
def cycle3164_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3164_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3164_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle3164_5 : CycleData E W := ⟨4,![15,13,21,22,18,19],![6,26,28,18,38,27]⟩
def data3164 : PartitionData E W := ⟨6,![cycle3164_0,cycle3164_1,cycle3164_2,cycle3164_3,cycle3164_4,cycle3164_5]⟩
lemma valid_data3164 : data3164.Valid src3164 dst3164 Finset.univ := by decide +kernel

def src3165 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst3165 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle3165_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3165_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle3165_2 : CycleData E W := ⟨3,![3,23,17,18,10],![4,8,38,16,27]⟩
def cycle3165_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3165_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3165_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3165 : PartitionData E W := ⟨6,![cycle3165_0,cycle3165_1,cycle3165_2,cycle3165_3,cycle3165_4,cycle3165_5]⟩
lemma valid_data3165 : data3165.Valid src3165 dst3165 Finset.univ := by decide +kernel

def src3166 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst3166 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle3166_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,14,16]⟩
def cycle3166_1 : CycleData E W := ⟨4,![2,10,18,17,21,8],![3,4,27,16,38,18]⟩
def cycle3166_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle3166_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3166_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle3166_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data3166 : PartitionData E W := ⟨6,![cycle3166_0,cycle3166_1,cycle3166_2,cycle3166_3,cycle3166_4,cycle3166_5]⟩
lemma valid_data3166 : data3166.Valid src3166 dst3166 Finset.univ := by decide +kernel

def src3167 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst3167 : E → W := ![6,3,4,8,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle3167_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle3167_1 : CycleData E W := ⟨2,![2,10,11,7],![3,4,27,14]⟩
def cycle3167_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle3167_3 : CycleData E W := ⟨2,![4,23,17,5],![2,8,38,16]⟩
def cycle3167_4 : CycleData E W := ⟨3,![15,12,6,18,19],![6,26,14,16,27]⟩
def cycle3167_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data3167 : PartitionData E W := ⟨6,![cycle3167_0,cycle3167_1,cycle3167_2,cycle3167_3,cycle3167_4,cycle3167_5]⟩
lemma valid_data3167 : data3167.Valid src3167 dst3167 Finset.univ := by decide +kernel

def src3168 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst3168 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle3168_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3168_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3168_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3168_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle3168_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle3168_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3168 : PartitionData E W := ⟨6,![cycle3168_0,cycle3168_1,cycle3168_2,cycle3168_3,cycle3168_4,cycle3168_5]⟩
lemma valid_data3168 : data3168.Valid src3168 dst3168 Finset.univ := by decide +kernel

def src3169 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst3169 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle3169_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle3169_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3169_2 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3169_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3169_4 : CycleData E W := ⟨2,![6,11,16,7],![3,14,26,16]⟩
def cycle3169_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3169_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3169 : PartitionData E W := ⟨7,![cycle3169_0,cycle3169_1,cycle3169_2,cycle3169_3,cycle3169_4,cycle3169_5,cycle3169_6]⟩
lemma valid_data3169 : data3169.Valid src3169 dst3169 Finset.univ := by decide +kernel

def src3170 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst3170 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle3170_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3170_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3170_2 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle3170_3 : CycleData E W := ⟨3,![3,23,18,12,6],![3,8,38,27,14]⟩
def cycle3170_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3170_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data3170 : PartitionData E W := ⟨6,![cycle3170_0,cycle3170_1,cycle3170_2,cycle3170_3,cycle3170_4,cycle3170_5]⟩
lemma valid_data3170 : data3170.Valid src3170 dst3170 Finset.univ := by decide +kernel

def src3171 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst3171 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle3171_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3171_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3171_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3171_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle3171_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle3171_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data3171 : PartitionData E W := ⟨6,![cycle3171_0,cycle3171_1,cycle3171_2,cycle3171_3,cycle3171_4,cycle3171_5]⟩
lemma valid_data3171 : data3171.Valid src3171 dst3171 Finset.univ := by decide +kernel

def src3172 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst3172 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle3172_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3172_1 : CycleData E W := ⟨3,![3,23,13,18,7],![3,8,28,27,16]⟩
def cycle3172_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3172_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3172_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle3172_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data3172 : PartitionData E W := ⟨6,![cycle3172_0,cycle3172_1,cycle3172_2,cycle3172_3,cycle3172_4,cycle3172_5]⟩
lemma valid_data3172 : data3172.Valid src3172 dst3172 Finset.univ := by decide +kernel

def src3173 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst3173 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle3173_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3173_1 : CycleData E W := ⟨2,![1,19,13,14],![4,6,27,28]⟩
def cycle3173_2 : CycleData E W := ⟨3,![2,10,16,23,3],![3,4,26,38,8]⟩
def cycle3173_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3173_4 : CycleData E W := ⟨2,![6,12,18,7],![3,14,27,16]⟩
def cycle3173_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data3173 : PartitionData E W := ⟨6,![cycle3173_0,cycle3173_1,cycle3173_2,cycle3173_3,cycle3173_4,cycle3173_5]⟩
lemma valid_data3173 : data3173.Valid src3173 dst3173 Finset.univ := by decide +kernel

def src3174 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst3174 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle3174_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle3174_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3174_2 : CycleData E W := ⟨3,![2,14,22,23,3],![3,4,28,38,8]⟩
def cycle3174_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3174_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,26,16]⟩
def cycle3174_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3174 : PartitionData E W := ⟨6,![cycle3174_0,cycle3174_1,cycle3174_2,cycle3174_3,cycle3174_4,cycle3174_5]⟩
lemma valid_data3174 : data3174.Valid src3174 dst3174 Finset.univ := by decide +kernel

def src3175 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst3175 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle3175_0 : CycleData E W := ⟨3,![0,1,10,11,5],![2,6,4,26,14]⟩
def cycle3175_1 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3175_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3175_3 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle3175_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle3175_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3175 : PartitionData E W := ⟨6,![cycle3175_0,cycle3175_1,cycle3175_2,cycle3175_3,cycle3175_4,cycle3175_5]⟩
lemma valid_data3175 : data3175.Valid src3175 dst3175 Finset.univ := by decide +kernel

def src3176 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst3176 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle3176_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle3176_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3176_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3176_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3176_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,26,16]⟩
def cycle3176_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3176 : PartitionData E W := ⟨6,![cycle3176_0,cycle3176_1,cycle3176_2,cycle3176_3,cycle3176_4,cycle3176_5]⟩
lemma valid_data3176 : data3176.Valid src3176 dst3176 Finset.univ := by decide +kernel

def src3177 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst3177 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle3177_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3177_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3177_2 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle3177_3 : CycleData E W := ⟨3,![3,23,22,12,6],![3,8,38,28,14]⟩
def cycle3177_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3177_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data3177 : PartitionData E W := ⟨6,![cycle3177_0,cycle3177_1,cycle3177_2,cycle3177_3,cycle3177_4,cycle3177_5]⟩
lemma valid_data3177 : data3177.Valid src3177 dst3177 Finset.univ := by decide +kernel

def src3178 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst3178 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle3178_0 : CycleData E W := ⟨3,![0,1,10,11,5],![2,6,4,26,14]⟩
def cycle3178_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle3178_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3178_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3178_4 : CycleData E W := ⟨3,![15,16,8,21,19],![6,26,16,18,38]⟩
def cycle3178_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data3178 : PartitionData E W := ⟨6,![cycle3178_0,cycle3178_1,cycle3178_2,cycle3178_3,cycle3178_4,cycle3178_5]⟩
lemma valid_data3178 : data3178.Valid src3178 dst3178 Finset.univ := by decide +kernel

def src3179 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst3179 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle3179_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3179_1 : CycleData E W := ⟨2,![1,19,18,14],![4,6,38,27]⟩
def cycle3179_2 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle3179_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3179_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3179_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data3179 : PartitionData E W := ⟨6,![cycle3179_0,cycle3179_1,cycle3179_2,cycle3179_3,cycle3179_4,cycle3179_5]⟩
lemma valid_data3179 : data3179.Valid src3179 dst3179 Finset.univ := by decide +kernel

def src3180 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst3180 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle3180_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3180_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3180_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3180_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle3180_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3180_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data3180 : PartitionData E W := ⟨6,![cycle3180_0,cycle3180_1,cycle3180_2,cycle3180_3,cycle3180_4,cycle3180_5]⟩
lemma valid_data3180 : data3180.Valid src3180 dst3180 Finset.univ := by decide +kernel

def src3181 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst3181 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle3181_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3181_1 : CycleData E W := ⟨3,![3,23,13,18,7],![3,8,28,27,16]⟩
def cycle3181_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3181_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3181_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3181_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data3181 : PartitionData E W := ⟨6,![cycle3181_0,cycle3181_1,cycle3181_2,cycle3181_3,cycle3181_4,cycle3181_5]⟩
lemma valid_data3181 : data3181.Valid src3181 dst3181 Finset.univ := by decide +kernel

def src3182 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst3182 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle3182_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle3182_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3182_2 : CycleData E W := ⟨3,![2,10,16,17,7],![3,4,26,38,16]⟩
def cycle3182_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3182_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3182_5 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def data3182 : PartitionData E W := ⟨6,![cycle3182_0,cycle3182_1,cycle3182_2,cycle3182_3,cycle3182_4,cycle3182_5]⟩
lemma valid_data3182 : data3182.Valid src3182 dst3182 Finset.univ := by decide +kernel

def src3183 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst3183 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle3183_0 : CycleData E W := ⟨3,![0,19,18,11,5],![2,6,38,26,14]⟩
def cycle3183_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3183_2 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle3183_3 : CycleData E W := ⟨3,![3,23,22,12,6],![3,8,38,28,14]⟩
def cycle3183_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3183_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3183 : PartitionData E W := ⟨6,![cycle3183_0,cycle3183_1,cycle3183_2,cycle3183_3,cycle3183_4,cycle3183_5]⟩
lemma valid_data3183 : data3183.Valid src3183 dst3183 Finset.univ := by decide +kernel

def src3184 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst3184 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle3184_0 : CycleData E W := ⟨3,![0,1,10,11,5],![2,6,4,26,14]⟩
def cycle3184_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle3184_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3184_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3184_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle3184_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data3184 : PartitionData E W := ⟨6,![cycle3184_0,cycle3184_1,cycle3184_2,cycle3184_3,cycle3184_4,cycle3184_5]⟩
lemma valid_data3184 : data3184.Valid src3184 dst3184 Finset.univ := by decide +kernel

def src3185 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst3185 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle3185_0 : CycleData E W := ⟨3,![0,19,18,11,5],![2,6,38,26,14]⟩
def cycle3185_1 : CycleData E W := ⟨1,![1,15,14],![4,6,27]⟩
def cycle3185_2 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle3185_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3185_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3185_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data3185 : PartitionData E W := ⟨6,![cycle3185_0,cycle3185_1,cycle3185_2,cycle3185_3,cycle3185_4,cycle3185_5]⟩
lemma valid_data3185 : data3185.Valid src3185 dst3185 Finset.univ := by decide +kernel

def src3186 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst3186 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle3186_0 : CycleData E W := ⟨3,![0,19,18,13,5],![2,6,38,27,14]⟩
def cycle3186_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3186_2 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle3186_3 : CycleData E W := ⟨3,![3,23,22,12,6],![3,8,38,28,14]⟩
def cycle3186_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3186_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data3186 : PartitionData E W := ⟨6,![cycle3186_0,cycle3186_1,cycle3186_2,cycle3186_3,cycle3186_4,cycle3186_5]⟩
lemma valid_data3186 : data3186.Valid src3186 dst3186 Finset.univ := by decide +kernel

def src3187 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst3187 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle3187_0 : CycleData E W := ⟨3,![0,1,14,13,5],![2,6,4,27,14]⟩
def cycle3187_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle3187_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3187_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3187_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle3187_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data3187 : PartitionData E W := ⟨6,![cycle3187_0,cycle3187_1,cycle3187_2,cycle3187_3,cycle3187_4,cycle3187_5]⟩
lemma valid_data3187 : data3187.Valid src3187 dst3187 Finset.univ := by decide +kernel

def src3188 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst3188 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle3188_0 : CycleData E W := ⟨3,![0,19,18,13,5],![2,6,38,27,14]⟩
def cycle3188_1 : CycleData E W := ⟨1,![1,15,10],![4,6,26]⟩
def cycle3188_2 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle3188_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3188_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3188_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data3188 : PartitionData E W := ⟨6,![cycle3188_0,cycle3188_1,cycle3188_2,cycle3188_3,cycle3188_4,cycle3188_5]⟩
lemma valid_data3188 : data3188.Valid src3188 dst3188 Finset.univ := by decide +kernel

def src3189 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst3189 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle3189_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3189_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3189_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3189_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle3189_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3189_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data3189 : PartitionData E W := ⟨6,![cycle3189_0,cycle3189_1,cycle3189_2,cycle3189_3,cycle3189_4,cycle3189_5]⟩
lemma valid_data3189 : data3189.Valid src3189 dst3189 Finset.univ := by decide +kernel

def src3190 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst3190 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle3190_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3190_1 : CycleData E W := ⟨3,![3,23,11,16,7],![3,8,28,26,16]⟩
def cycle3190_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3190_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3190_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle3190_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data3190 : PartitionData E W := ⟨6,![cycle3190_0,cycle3190_1,cycle3190_2,cycle3190_3,cycle3190_4,cycle3190_5]⟩
lemma valid_data3190 : data3190.Valid src3190 dst3190 Finset.univ := by decide +kernel

def src3191 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst3191 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle3191_0 : CycleData E W := ⟨3,![0,15,11,12,5],![2,6,26,28,14]⟩
def cycle3191_1 : CycleData E W := ⟨1,![1,19,14],![4,6,27]⟩
def cycle3191_2 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle3191_3 : CycleData E W := ⟨3,![3,23,18,13,6],![3,8,38,27,14]⟩
def cycle3191_4 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle3191_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data3191 : PartitionData E W := ⟨6,![cycle3191_0,cycle3191_1,cycle3191_2,cycle3191_3,cycle3191_4,cycle3191_5]⟩
lemma valid_data3191 : data3191.Valid src3191 dst3191 Finset.univ := by decide +kernel

def src3192 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst3192 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle3192_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3192_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3192_2 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle3192_3 : CycleData E W := ⟨3,![3,23,22,12,6],![3,8,38,28,14]⟩
def cycle3192_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3192_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data3192 : PartitionData E W := ⟨6,![cycle3192_0,cycle3192_1,cycle3192_2,cycle3192_3,cycle3192_4,cycle3192_5]⟩
lemma valid_data3192 : data3192.Valid src3192 dst3192 Finset.univ := by decide +kernel

def src3193 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst3193 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle3193_0 : CycleData E W := ⟨3,![0,1,14,13,5],![2,6,4,27,14]⟩
def cycle3193_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle3193_2 : CycleData E W := ⟨2,![3,23,12,6],![3,8,28,14]⟩
def cycle3193_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3193_4 : CycleData E W := ⟨3,![15,16,8,21,19],![6,27,16,18,38]⟩
def cycle3193_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data3193 : PartitionData E W := ⟨6,![cycle3193_0,cycle3193_1,cycle3193_2,cycle3193_3,cycle3193_4,cycle3193_5]⟩
lemma valid_data3193 : data3193.Valid src3193 dst3193 Finset.univ := by decide +kernel

def src3194 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst3194 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle3194_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle3194_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,26]⟩
def cycle3194_2 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle3194_3 : CycleData E W := ⟨2,![3,20,12,6],![3,8,28,14]⟩
def cycle3194_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3194_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data3194 : PartitionData E W := ⟨6,![cycle3194_0,cycle3194_1,cycle3194_2,cycle3194_3,cycle3194_4,cycle3194_5]⟩
lemma valid_data3194 : data3194.Valid src3194 dst3194 Finset.univ := by decide +kernel

def src3195 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst3195 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle3195_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3195_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,27]⟩
def cycle3195_2 : CycleData E W := ⟨3,![2,14,22,23,3],![3,4,28,38,8]⟩
def cycle3195_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3195_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle3195_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data3195 : PartitionData E W := ⟨6,![cycle3195_0,cycle3195_1,cycle3195_2,cycle3195_3,cycle3195_4,cycle3195_5]⟩
lemma valid_data3195 : data3195.Valid src3195 dst3195 Finset.univ := by decide +kernel

def src3196 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst3196 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle3196_0 : CycleData E W := ⟨3,![0,1,10,11,5],![2,6,4,27,14]⟩
def cycle3196_1 : CycleData E W := ⟨2,![2,14,23,3],![3,4,28,8]⟩
def cycle3196_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3196_3 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle3196_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle3196_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data3196 : PartitionData E W := ⟨6,![cycle3196_0,cycle3196_1,cycle3196_2,cycle3196_3,cycle3196_4,cycle3196_5]⟩
lemma valid_data3196 : data3196.Valid src3196 dst3196 Finset.univ := by decide +kernel

def src3197 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst3197 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle3197_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle3197_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,38,27]⟩
def cycle3197_2 : CycleData E W := ⟨2,![2,14,20,3],![3,4,28,8]⟩
def cycle3197_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle3197_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle3197_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data3197 : PartitionData E W := ⟨6,![cycle3197_0,cycle3197_1,cycle3197_2,cycle3197_3,cycle3197_4,cycle3197_5]⟩
lemma valid_data3197 : data3197.Valid src3197 dst3197 Finset.univ := by decide +kernel

def src3198 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst3198 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle3198_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3198_1 : CycleData E W := ⟨2,![3,23,17,7],![3,8,38,16]⟩
def cycle3198_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3198_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle3198_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3198_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data3198 : PartitionData E W := ⟨6,![cycle3198_0,cycle3198_1,cycle3198_2,cycle3198_3,cycle3198_4,cycle3198_5]⟩
lemma valid_data3198 : data3198.Valid src3198 dst3198 Finset.univ := by decide +kernel

def src3199 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst3199 : E → W := ![6,4,3,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle3199_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,6,4,3,14]⟩
def cycle3199_1 : CycleData E W := ⟨3,![3,23,13,16,7],![3,8,28,26,16]⟩
def cycle3199_2 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle3199_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle3199_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle3199_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data3199 : PartitionData E W := ⟨6,![cycle3199_0,cycle3199_1,cycle3199_2,cycle3199_3,cycle3199_4,cycle3199_5]⟩
lemma valid_data3199 : data3199.Valid src3199 dst3199 Finset.univ := by decide +kernel

def lookupB15 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data3000 else (if j < 2 then data3001 else data3002)) else (if j < 4 then data3003 else (if j < 5 then data3004 else data3005))) else (if j < 9 then (if j < 7 then data3006 else (if j < 8 then data3007 else data3008)) else (if j < 10 then data3009 else (if j < 11 then data3010 else data3011)))) else (if j < 18 then (if j < 15 then (if j < 13 then data3012 else (if j < 14 then data3013 else data3014)) else (if j < 16 then data3015 else (if j < 17 then data3016 else data3017))) else (if j < 21 then (if j < 19 then data3018 else (if j < 20 then data3019 else data3020)) else (if j < 23 then (if j < 22 then data3021 else data3022) else (if j < 24 then data3023 else data3024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data3025 else (if j < 27 then data3026 else data3027)) else (if j < 29 then data3028 else (if j < 30 then data3029 else data3030))) else (if j < 34 then (if j < 32 then data3031 else (if j < 33 then data3032 else data3033)) else (if j < 35 then data3034 else (if j < 36 then data3035 else data3036)))) else (if j < 43 then (if j < 40 then (if j < 38 then data3037 else (if j < 39 then data3038 else data3039)) else (if j < 41 then data3040 else (if j < 42 then data3041 else data3042))) else (if j < 46 then (if j < 44 then data3043 else (if j < 45 then data3044 else data3045)) else (if j < 48 then (if j < 47 then data3046 else data3047) else (if j < 49 then data3048 else data3049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data3050 else (if j < 52 then data3051 else data3052)) else (if j < 54 then data3053 else (if j < 55 then data3054 else data3055))) else (if j < 59 then (if j < 57 then data3056 else (if j < 58 then data3057 else data3058)) else (if j < 60 then data3059 else (if j < 61 then data3060 else data3061)))) else (if j < 68 then (if j < 65 then (if j < 63 then data3062 else (if j < 64 then data3063 else data3064)) else (if j < 66 then data3065 else (if j < 67 then data3066 else data3067))) else (if j < 71 then (if j < 69 then data3068 else (if j < 70 then data3069 else data3070)) else (if j < 73 then (if j < 72 then data3071 else data3072) else (if j < 74 then data3073 else data3074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data3075 else (if j < 77 then data3076 else data3077)) else (if j < 79 then data3078 else (if j < 80 then data3079 else data3080))) else (if j < 84 then (if j < 82 then data3081 else (if j < 83 then data3082 else data3083)) else (if j < 85 then data3084 else (if j < 86 then data3085 else data3086)))) else (if j < 93 then (if j < 90 then (if j < 88 then data3087 else (if j < 89 then data3088 else data3089)) else (if j < 91 then data3090 else (if j < 92 then data3091 else data3092))) else (if j < 96 then (if j < 94 then data3093 else (if j < 95 then data3094 else data3095)) else (if j < 98 then (if j < 97 then data3096 else data3097) else (if j < 99 then data3098 else data3099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data3100 else (if j < 102 then data3101 else data3102)) else (if j < 104 then data3103 else (if j < 105 then data3104 else data3105))) else (if j < 109 then (if j < 107 then data3106 else (if j < 108 then data3107 else data3108)) else (if j < 110 then data3109 else (if j < 111 then data3110 else data3111)))) else (if j < 118 then (if j < 115 then (if j < 113 then data3112 else (if j < 114 then data3113 else data3114)) else (if j < 116 then data3115 else (if j < 117 then data3116 else data3117))) else (if j < 121 then (if j < 119 then data3118 else (if j < 120 then data3119 else data3120)) else (if j < 123 then (if j < 122 then data3121 else data3122) else (if j < 124 then data3123 else data3124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data3125 else (if j < 127 then data3126 else data3127)) else (if j < 129 then data3128 else (if j < 130 then data3129 else data3130))) else (if j < 134 then (if j < 132 then data3131 else (if j < 133 then data3132 else data3133)) else (if j < 135 then data3134 else (if j < 136 then data3135 else data3136)))) else (if j < 143 then (if j < 140 then (if j < 138 then data3137 else (if j < 139 then data3138 else data3139)) else (if j < 141 then data3140 else (if j < 142 then data3141 else data3142))) else (if j < 146 then (if j < 144 then data3143 else (if j < 145 then data3144 else data3145)) else (if j < 148 then (if j < 147 then data3146 else data3147) else (if j < 149 then data3148 else data3149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data3150 else (if j < 152 then data3151 else data3152)) else (if j < 154 then data3153 else (if j < 155 then data3154 else data3155))) else (if j < 159 then (if j < 157 then data3156 else (if j < 158 then data3157 else data3158)) else (if j < 160 then data3159 else (if j < 161 then data3160 else data3161)))) else (if j < 168 then (if j < 165 then (if j < 163 then data3162 else (if j < 164 then data3163 else data3164)) else (if j < 166 then data3165 else (if j < 167 then data3166 else data3167))) else (if j < 171 then (if j < 169 then data3168 else (if j < 170 then data3169 else data3170)) else (if j < 173 then (if j < 172 then data3171 else data3172) else (if j < 174 then data3173 else data3174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data3175 else (if j < 177 then data3176 else data3177)) else (if j < 179 then data3178 else (if j < 180 then data3179 else data3180))) else (if j < 184 then (if j < 182 then data3181 else (if j < 183 then data3182 else data3183)) else (if j < 185 then data3184 else (if j < 186 then data3185 else data3186)))) else (if j < 193 then (if j < 190 then (if j < 188 then data3187 else (if j < 189 then data3188 else data3189)) else (if j < 191 then data3190 else (if j < 192 then data3191 else data3192))) else (if j < 196 then (if j < 194 then data3193 else (if j < 195 then data3194 else data3195)) else (if j < 198 then (if j < 197 then data3196 else data3197) else (if j < 199 then data3198 else data3199))))))))

def srcTableB15 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src3000 else (if j < 2 then src3001 else src3002)) else (if j < 4 then src3003 else (if j < 5 then src3004 else src3005))) else (if j < 9 then (if j < 7 then src3006 else (if j < 8 then src3007 else src3008)) else (if j < 10 then src3009 else (if j < 11 then src3010 else src3011)))) else (if j < 18 then (if j < 15 then (if j < 13 then src3012 else (if j < 14 then src3013 else src3014)) else (if j < 16 then src3015 else (if j < 17 then src3016 else src3017))) else (if j < 21 then (if j < 19 then src3018 else (if j < 20 then src3019 else src3020)) else (if j < 23 then (if j < 22 then src3021 else src3022) else (if j < 24 then src3023 else src3024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src3025 else (if j < 27 then src3026 else src3027)) else (if j < 29 then src3028 else (if j < 30 then src3029 else src3030))) else (if j < 34 then (if j < 32 then src3031 else (if j < 33 then src3032 else src3033)) else (if j < 35 then src3034 else (if j < 36 then src3035 else src3036)))) else (if j < 43 then (if j < 40 then (if j < 38 then src3037 else (if j < 39 then src3038 else src3039)) else (if j < 41 then src3040 else (if j < 42 then src3041 else src3042))) else (if j < 46 then (if j < 44 then src3043 else (if j < 45 then src3044 else src3045)) else (if j < 48 then (if j < 47 then src3046 else src3047) else (if j < 49 then src3048 else src3049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src3050 else (if j < 52 then src3051 else src3052)) else (if j < 54 then src3053 else (if j < 55 then src3054 else src3055))) else (if j < 59 then (if j < 57 then src3056 else (if j < 58 then src3057 else src3058)) else (if j < 60 then src3059 else (if j < 61 then src3060 else src3061)))) else (if j < 68 then (if j < 65 then (if j < 63 then src3062 else (if j < 64 then src3063 else src3064)) else (if j < 66 then src3065 else (if j < 67 then src3066 else src3067))) else (if j < 71 then (if j < 69 then src3068 else (if j < 70 then src3069 else src3070)) else (if j < 73 then (if j < 72 then src3071 else src3072) else (if j < 74 then src3073 else src3074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src3075 else (if j < 77 then src3076 else src3077)) else (if j < 79 then src3078 else (if j < 80 then src3079 else src3080))) else (if j < 84 then (if j < 82 then src3081 else (if j < 83 then src3082 else src3083)) else (if j < 85 then src3084 else (if j < 86 then src3085 else src3086)))) else (if j < 93 then (if j < 90 then (if j < 88 then src3087 else (if j < 89 then src3088 else src3089)) else (if j < 91 then src3090 else (if j < 92 then src3091 else src3092))) else (if j < 96 then (if j < 94 then src3093 else (if j < 95 then src3094 else src3095)) else (if j < 98 then (if j < 97 then src3096 else src3097) else (if j < 99 then src3098 else src3099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src3100 else (if j < 102 then src3101 else src3102)) else (if j < 104 then src3103 else (if j < 105 then src3104 else src3105))) else (if j < 109 then (if j < 107 then src3106 else (if j < 108 then src3107 else src3108)) else (if j < 110 then src3109 else (if j < 111 then src3110 else src3111)))) else (if j < 118 then (if j < 115 then (if j < 113 then src3112 else (if j < 114 then src3113 else src3114)) else (if j < 116 then src3115 else (if j < 117 then src3116 else src3117))) else (if j < 121 then (if j < 119 then src3118 else (if j < 120 then src3119 else src3120)) else (if j < 123 then (if j < 122 then src3121 else src3122) else (if j < 124 then src3123 else src3124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src3125 else (if j < 127 then src3126 else src3127)) else (if j < 129 then src3128 else (if j < 130 then src3129 else src3130))) else (if j < 134 then (if j < 132 then src3131 else (if j < 133 then src3132 else src3133)) else (if j < 135 then src3134 else (if j < 136 then src3135 else src3136)))) else (if j < 143 then (if j < 140 then (if j < 138 then src3137 else (if j < 139 then src3138 else src3139)) else (if j < 141 then src3140 else (if j < 142 then src3141 else src3142))) else (if j < 146 then (if j < 144 then src3143 else (if j < 145 then src3144 else src3145)) else (if j < 148 then (if j < 147 then src3146 else src3147) else (if j < 149 then src3148 else src3149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src3150 else (if j < 152 then src3151 else src3152)) else (if j < 154 then src3153 else (if j < 155 then src3154 else src3155))) else (if j < 159 then (if j < 157 then src3156 else (if j < 158 then src3157 else src3158)) else (if j < 160 then src3159 else (if j < 161 then src3160 else src3161)))) else (if j < 168 then (if j < 165 then (if j < 163 then src3162 else (if j < 164 then src3163 else src3164)) else (if j < 166 then src3165 else (if j < 167 then src3166 else src3167))) else (if j < 171 then (if j < 169 then src3168 else (if j < 170 then src3169 else src3170)) else (if j < 173 then (if j < 172 then src3171 else src3172) else (if j < 174 then src3173 else src3174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src3175 else (if j < 177 then src3176 else src3177)) else (if j < 179 then src3178 else (if j < 180 then src3179 else src3180))) else (if j < 184 then (if j < 182 then src3181 else (if j < 183 then src3182 else src3183)) else (if j < 185 then src3184 else (if j < 186 then src3185 else src3186)))) else (if j < 193 then (if j < 190 then (if j < 188 then src3187 else (if j < 189 then src3188 else src3189)) else (if j < 191 then src3190 else (if j < 192 then src3191 else src3192))) else (if j < 196 then (if j < 194 then src3193 else (if j < 195 then src3194 else src3195)) else (if j < 198 then (if j < 197 then src3196 else src3197) else (if j < 199 then src3198 else src3199))))))))

def dstTableB15 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst3000 else (if j < 2 then dst3001 else dst3002)) else (if j < 4 then dst3003 else (if j < 5 then dst3004 else dst3005))) else (if j < 9 then (if j < 7 then dst3006 else (if j < 8 then dst3007 else dst3008)) else (if j < 10 then dst3009 else (if j < 11 then dst3010 else dst3011)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst3012 else (if j < 14 then dst3013 else dst3014)) else (if j < 16 then dst3015 else (if j < 17 then dst3016 else dst3017))) else (if j < 21 then (if j < 19 then dst3018 else (if j < 20 then dst3019 else dst3020)) else (if j < 23 then (if j < 22 then dst3021 else dst3022) else (if j < 24 then dst3023 else dst3024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst3025 else (if j < 27 then dst3026 else dst3027)) else (if j < 29 then dst3028 else (if j < 30 then dst3029 else dst3030))) else (if j < 34 then (if j < 32 then dst3031 else (if j < 33 then dst3032 else dst3033)) else (if j < 35 then dst3034 else (if j < 36 then dst3035 else dst3036)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst3037 else (if j < 39 then dst3038 else dst3039)) else (if j < 41 then dst3040 else (if j < 42 then dst3041 else dst3042))) else (if j < 46 then (if j < 44 then dst3043 else (if j < 45 then dst3044 else dst3045)) else (if j < 48 then (if j < 47 then dst3046 else dst3047) else (if j < 49 then dst3048 else dst3049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst3050 else (if j < 52 then dst3051 else dst3052)) else (if j < 54 then dst3053 else (if j < 55 then dst3054 else dst3055))) else (if j < 59 then (if j < 57 then dst3056 else (if j < 58 then dst3057 else dst3058)) else (if j < 60 then dst3059 else (if j < 61 then dst3060 else dst3061)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst3062 else (if j < 64 then dst3063 else dst3064)) else (if j < 66 then dst3065 else (if j < 67 then dst3066 else dst3067))) else (if j < 71 then (if j < 69 then dst3068 else (if j < 70 then dst3069 else dst3070)) else (if j < 73 then (if j < 72 then dst3071 else dst3072) else (if j < 74 then dst3073 else dst3074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst3075 else (if j < 77 then dst3076 else dst3077)) else (if j < 79 then dst3078 else (if j < 80 then dst3079 else dst3080))) else (if j < 84 then (if j < 82 then dst3081 else (if j < 83 then dst3082 else dst3083)) else (if j < 85 then dst3084 else (if j < 86 then dst3085 else dst3086)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst3087 else (if j < 89 then dst3088 else dst3089)) else (if j < 91 then dst3090 else (if j < 92 then dst3091 else dst3092))) else (if j < 96 then (if j < 94 then dst3093 else (if j < 95 then dst3094 else dst3095)) else (if j < 98 then (if j < 97 then dst3096 else dst3097) else (if j < 99 then dst3098 else dst3099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst3100 else (if j < 102 then dst3101 else dst3102)) else (if j < 104 then dst3103 else (if j < 105 then dst3104 else dst3105))) else (if j < 109 then (if j < 107 then dst3106 else (if j < 108 then dst3107 else dst3108)) else (if j < 110 then dst3109 else (if j < 111 then dst3110 else dst3111)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst3112 else (if j < 114 then dst3113 else dst3114)) else (if j < 116 then dst3115 else (if j < 117 then dst3116 else dst3117))) else (if j < 121 then (if j < 119 then dst3118 else (if j < 120 then dst3119 else dst3120)) else (if j < 123 then (if j < 122 then dst3121 else dst3122) else (if j < 124 then dst3123 else dst3124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst3125 else (if j < 127 then dst3126 else dst3127)) else (if j < 129 then dst3128 else (if j < 130 then dst3129 else dst3130))) else (if j < 134 then (if j < 132 then dst3131 else (if j < 133 then dst3132 else dst3133)) else (if j < 135 then dst3134 else (if j < 136 then dst3135 else dst3136)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst3137 else (if j < 139 then dst3138 else dst3139)) else (if j < 141 then dst3140 else (if j < 142 then dst3141 else dst3142))) else (if j < 146 then (if j < 144 then dst3143 else (if j < 145 then dst3144 else dst3145)) else (if j < 148 then (if j < 147 then dst3146 else dst3147) else (if j < 149 then dst3148 else dst3149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst3150 else (if j < 152 then dst3151 else dst3152)) else (if j < 154 then dst3153 else (if j < 155 then dst3154 else dst3155))) else (if j < 159 then (if j < 157 then dst3156 else (if j < 158 then dst3157 else dst3158)) else (if j < 160 then dst3159 else (if j < 161 then dst3160 else dst3161)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst3162 else (if j < 164 then dst3163 else dst3164)) else (if j < 166 then dst3165 else (if j < 167 then dst3166 else dst3167))) else (if j < 171 then (if j < 169 then dst3168 else (if j < 170 then dst3169 else dst3170)) else (if j < 173 then (if j < 172 then dst3171 else dst3172) else (if j < 174 then dst3173 else dst3174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst3175 else (if j < 177 then dst3176 else dst3177)) else (if j < 179 then dst3178 else (if j < 180 then dst3179 else dst3180))) else (if j < 184 then (if j < 182 then dst3181 else (if j < 183 then dst3182 else dst3183)) else (if j < 185 then dst3184 else (if j < 186 then dst3185 else dst3186)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst3187 else (if j < 189 then dst3188 else dst3189)) else (if j < 191 then dst3190 else (if j < 192 then dst3191 else dst3192))) else (if j < 196 then (if j < 194 then dst3193 else (if j < 195 then dst3194 else dst3195)) else (if j < 198 then (if j < 197 then dst3196 else dst3197) else (if j < 199 then dst3198 else dst3199))))))))

def caseB15 (i : Fin 200) : Cases := ⟨3000 + i.val,by have := i.isLt; omega⟩
lemma tableB15_valid (i : Fin 200) :
    (lookupB15 i.val).Valid (srcTableB15 i.val) (dstTableB15 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data3000
  · exact valid_data3001
  · exact valid_data3002
  · exact valid_data3003
  · exact valid_data3004
  · exact valid_data3005
  · exact valid_data3006
  · exact valid_data3007
  · exact valid_data3008
  · exact valid_data3009
  · exact valid_data3010
  · exact valid_data3011
  · exact valid_data3012
  · exact valid_data3013
  · exact valid_data3014
  · exact valid_data3015
  · exact valid_data3016
  · exact valid_data3017
  · exact valid_data3018
  · exact valid_data3019
  · exact valid_data3020
  · exact valid_data3021
  · exact valid_data3022
  · exact valid_data3023
  · exact valid_data3024
  · exact valid_data3025
  · exact valid_data3026
  · exact valid_data3027
  · exact valid_data3028
  · exact valid_data3029
  · exact valid_data3030
  · exact valid_data3031
  · exact valid_data3032
  · exact valid_data3033
  · exact valid_data3034
  · exact valid_data3035
  · exact valid_data3036
  · exact valid_data3037
  · exact valid_data3038
  · exact valid_data3039
  · exact valid_data3040
  · exact valid_data3041
  · exact valid_data3042
  · exact valid_data3043
  · exact valid_data3044
  · exact valid_data3045
  · exact valid_data3046
  · exact valid_data3047
  · exact valid_data3048
  · exact valid_data3049
  · exact valid_data3050
  · exact valid_data3051
  · exact valid_data3052
  · exact valid_data3053
  · exact valid_data3054
  · exact valid_data3055
  · exact valid_data3056
  · exact valid_data3057
  · exact valid_data3058
  · exact valid_data3059
  · exact valid_data3060
  · exact valid_data3061
  · exact valid_data3062
  · exact valid_data3063
  · exact valid_data3064
  · exact valid_data3065
  · exact valid_data3066
  · exact valid_data3067
  · exact valid_data3068
  · exact valid_data3069
  · exact valid_data3070
  · exact valid_data3071
  · exact valid_data3072
  · exact valid_data3073
  · exact valid_data3074
  · exact valid_data3075
  · exact valid_data3076
  · exact valid_data3077
  · exact valid_data3078
  · exact valid_data3079
  · exact valid_data3080
  · exact valid_data3081
  · exact valid_data3082
  · exact valid_data3083
  · exact valid_data3084
  · exact valid_data3085
  · exact valid_data3086
  · exact valid_data3087
  · exact valid_data3088
  · exact valid_data3089
  · exact valid_data3090
  · exact valid_data3091
  · exact valid_data3092
  · exact valid_data3093
  · exact valid_data3094
  · exact valid_data3095
  · exact valid_data3096
  · exact valid_data3097
  · exact valid_data3098
  · exact valid_data3099
  · exact valid_data3100
  · exact valid_data3101
  · exact valid_data3102
  · exact valid_data3103
  · exact valid_data3104
  · exact valid_data3105
  · exact valid_data3106
  · exact valid_data3107
  · exact valid_data3108
  · exact valid_data3109
  · exact valid_data3110
  · exact valid_data3111
  · exact valid_data3112
  · exact valid_data3113
  · exact valid_data3114
  · exact valid_data3115
  · exact valid_data3116
  · exact valid_data3117
  · exact valid_data3118
  · exact valid_data3119
  · exact valid_data3120
  · exact valid_data3121
  · exact valid_data3122
  · exact valid_data3123
  · exact valid_data3124
  · exact valid_data3125
  · exact valid_data3126
  · exact valid_data3127
  · exact valid_data3128
  · exact valid_data3129
  · exact valid_data3130
  · exact valid_data3131
  · exact valid_data3132
  · exact valid_data3133
  · exact valid_data3134
  · exact valid_data3135
  · exact valid_data3136
  · exact valid_data3137
  · exact valid_data3138
  · exact valid_data3139
  · exact valid_data3140
  · exact valid_data3141
  · exact valid_data3142
  · exact valid_data3143
  · exact valid_data3144
  · exact valid_data3145
  · exact valid_data3146
  · exact valid_data3147
  · exact valid_data3148
  · exact valid_data3149
  · exact valid_data3150
  · exact valid_data3151
  · exact valid_data3152
  · exact valid_data3153
  · exact valid_data3154
  · exact valid_data3155
  · exact valid_data3156
  · exact valid_data3157
  · exact valid_data3158
  · exact valid_data3159
  · exact valid_data3160
  · exact valid_data3161
  · exact valid_data3162
  · exact valid_data3163
  · exact valid_data3164
  · exact valid_data3165
  · exact valid_data3166
  · exact valid_data3167
  · exact valid_data3168
  · exact valid_data3169
  · exact valid_data3170
  · exact valid_data3171
  · exact valid_data3172
  · exact valid_data3173
  · exact valid_data3174
  · exact valid_data3175
  · exact valid_data3176
  · exact valid_data3177
  · exact valid_data3178
  · exact valid_data3179
  · exact valid_data3180
  · exact valid_data3181
  · exact valid_data3182
  · exact valid_data3183
  · exact valid_data3184
  · exact valid_data3185
  · exact valid_data3186
  · exact valid_data3187
  · exact valid_data3188
  · exact valid_data3189
  · exact valid_data3190
  · exact valid_data3191
  · exact valid_data3192
  · exact valid_data3193
  · exact valid_data3194
  · exact valid_data3195
  · exact valid_data3196
  · exact valid_data3197
  · exact valid_data3198
  · exact valid_data3199

lemma srcB15_row : ∀ (i : Fin 200) (e : E),
    srcTableB15 i.val e = caseSource (caseB15 i) e := by decide +kernel

lemma dstB15_row : ∀ (i : Fin 200) (e : E),
    dstTableB15 i.val e = caseTarget (caseB15 i) e := by decide +kernel

lemma sizeB15 : ∀ i : Fin 200, (lookupB15 i.val).size ≤ 5 →
    (lookupB15 i.val).size = 2 ∧
      (⟨caseKey (caseB15 i),caseKey_lt (caseB15 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB15 (i : Fin 200) : Certificate (caseB15 i) := by
  refine ⟨lookupB15 i.val,?_,sizeB15 i⟩
  have hv := tableB15_valid i
  rw [funext (srcB15_row i),funext (dstB15_row i)] at hv
  exact hv
lemma certificateInterval15 : FiniteIntervals.Covers CertificateAt 3000 3200 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 3000 200 (fun i _ => certificateB15 i)
#print axioms certificateInterval15
end Erdos184Work.FiveRows3

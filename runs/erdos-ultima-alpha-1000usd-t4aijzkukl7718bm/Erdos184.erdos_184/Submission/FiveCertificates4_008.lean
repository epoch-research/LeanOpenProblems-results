import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src400 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst400 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle400_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle400_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle400_2 : CycleData E W := ⟨2,![3,16,12,11],![4,6,26,14]⟩
def cycle400_3 : CycleData E W := ⟨2,![4,25,24,15],![4,8,39,28]⟩
def cycle400_4 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle400_5 : CycleData E W := ⟨3,![13,17,22,23,14],![5,26,38,18,28]⟩
def data400 : PartitionData E W := ⟨6,![cycle400_0,cycle400_1,cycle400_2,cycle400_3,cycle400_4,cycle400_5]⟩
lemma valid_data400 : data400.Valid src400 dst400 Finset.univ := by decide +kernel

def src401 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst401 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle401_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle401_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle401_2 : CycleData E W := ⟨2,![3,16,12,11],![4,6,26,14]⟩
def cycle401_3 : CycleData E W := ⟨3,![4,25,24,23,15],![4,8,39,18,28]⟩
def cycle401_4 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle401_5 : CycleData E W := ⟨2,![13,17,22,14],![5,26,38,28]⟩
def data401 : PartitionData E W := ⟨6,![cycle401_0,cycle401_1,cycle401_2,cycle401_3,cycle401_4,cycle401_5]⟩
lemma valid_data401 : data401.Valid src401 dst401 Finset.univ := by decide +kernel

def src402 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst402 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle402_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle402_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,38,16]⟩
def cycle402_2 : CycleData E W := ⟨2,![3,16,12,11],![4,6,26,14]⟩
def cycle402_3 : CycleData E W := ⟨3,![4,21,22,23,15],![4,8,38,18,28]⟩
def cycle402_4 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle402_5 : CycleData E W := ⟨2,![13,17,24,14],![5,26,39,28]⟩
def data402 : PartitionData E W := ⟨6,![cycle402_0,cycle402_1,cycle402_2,cycle402_3,cycle402_4,cycle402_5]⟩
lemma valid_data402 : data402.Valid src402 dst402 Finset.univ := by decide +kernel

def src403 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst403 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle403_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle403_1 : CycleData E W := ⟨2,![2,20,19,9],![3,6,38,16]⟩
def cycle403_2 : CycleData E W := ⟨2,![3,16,12,11],![4,6,26,14]⟩
def cycle403_3 : CycleData E W := ⟨2,![4,21,22,15],![4,8,38,28]⟩
def cycle403_4 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle403_5 : CycleData E W := ⟨3,![13,17,24,23,14],![5,26,39,18,28]⟩
def data403 : PartitionData E W := ⟨6,![cycle403_0,cycle403_1,cycle403_2,cycle403_3,cycle403_4,cycle403_5]⟩
lemma valid_data403 : data403.Valid src403 dst403 Finset.univ := by decide +kernel

def src404 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst404 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle404_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle404_1 : CycleData E W := ⟨3,![2,3,11,7,8],![3,6,4,14,18]⟩
def cycle404_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle404_3 : CycleData E W := ⟨3,![5,25,19,12,6],![2,8,39,26,14]⟩
def cycle404_4 : CycleData E W := ⟨3,![13,18,17,22,14],![5,26,16,38,28]⟩
def cycle404_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data404 : PartitionData E W := ⟨6,![cycle404_0,cycle404_1,cycle404_2,cycle404_3,cycle404_4,cycle404_5]⟩
lemma valid_data404 : data404.Valid src404 dst404 Finset.univ := by decide +kernel

def src405 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst405 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle405_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle405_1 : CycleData E W := ⟨4,![2,3,11,12,18,9],![3,6,4,14,26,16]⟩
def cycle405_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle405_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle405_4 : CycleData E W := ⟨2,![13,19,22,14],![5,26,39,28]⟩
def cycle405_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data405 : PartitionData E W := ⟨6,![cycle405_0,cycle405_1,cycle405_2,cycle405_3,cycle405_4,cycle405_5]⟩
lemma valid_data405 : data405.Valid src405 dst405 Finset.univ := by decide +kernel

def src406 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst406 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle406_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle406_1 : CycleData E W := ⟨3,![2,3,15,23,8],![3,6,4,28,18]⟩
def cycle406_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle406_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle406_4 : CycleData E W := ⟨3,![13,18,17,22,14],![5,26,16,38,28]⟩
def cycle406_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data406 : PartitionData E W := ⟨6,![cycle406_0,cycle406_1,cycle406_2,cycle406_3,cycle406_4,cycle406_5]⟩
lemma valid_data406 : data406.Valid src406 dst406 Finset.univ := by decide +kernel

def src407 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst407 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle407_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,18,14]⟩
def cycle407_1 : CycleData E W := ⟨4,![2,3,11,12,18,9],![3,6,4,14,26,16]⟩
def cycle407_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle407_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle407_4 : CycleData E W := ⟨2,![13,17,22,14],![5,26,38,28]⟩
def cycle407_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data407 : PartitionData E W := ⟨6,![cycle407_0,cycle407_1,cycle407_2,cycle407_3,cycle407_4,cycle407_5]⟩
lemma valid_data407 : data407.Valid src407 dst407 Finset.univ := by decide +kernel

def src408 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst408 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle408_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle408_1 : CycleData E W := ⟨3,![2,3,11,7,8],![3,6,4,14,18]⟩
def cycle408_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle408_3 : CycleData E W := ⟨3,![5,25,17,12,6],![2,8,38,26,14]⟩
def cycle408_4 : CycleData E W := ⟨3,![13,18,19,22,14],![5,26,16,39,28]⟩
def cycle408_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data408 : PartitionData E W := ⟨6,![cycle408_0,cycle408_1,cycle408_2,cycle408_3,cycle408_4,cycle408_5]⟩
lemma valid_data408 : data408.Valid src408 dst408 Finset.univ := by decide +kernel

def src409 : E → W := ![2,5,3,6,4,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst409 : E → W := ![5,3,6,4,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle409_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,16]⟩
def cycle409_1 : CycleData E W := ⟨2,![2,16,22,8],![3,6,38,18]⟩
def cycle409_2 : CycleData E W := ⟨2,![3,20,24,15],![4,6,39,28]⟩
def cycle409_3 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle409_4 : CycleData E W := ⟨3,![13,12,7,23,14],![5,26,14,18,28]⟩
def cycle409_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data409 : PartitionData E W := ⟨6,![cycle409_0,cycle409_1,cycle409_2,cycle409_3,cycle409_4,cycle409_5]⟩
lemma valid_data409 : data409.Valid src409 dst409 Finset.univ := by decide +kernel

def src410 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,5,26,28,14,6,38,16,26,39,8,38,28,18,39]
def dst410 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,5,26,28,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle410_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle410_1 : CycleData E W := ⟨2,![2,3,15,8],![3,6,4,14]⟩
def cycle410_2 : CycleData E W := ⟨4,![5,4,11,12,18,6],![2,8,4,5,26,16]⟩
def cycle410_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle410_4 : CycleData E W := ⟨2,![23,13,19,24],![18,28,26,39]⟩
def cycle410_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data410 : PartitionData E W := ⟨6,![cycle410_0,cycle410_1,cycle410_2,cycle410_3,cycle410_4,cycle410_5]⟩
lemma valid_data410 : data410.Valid src410 dst410 Finset.univ := by decide +kernel

def src411 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,5,26,28,14,6,38,26,16,39,8,38,18,28,39]
def dst411 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,5,26,28,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle411_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle411_1 : CycleData E W := ⟨2,![2,3,15,8],![3,6,4,14]⟩
def cycle411_2 : CycleData E W := ⟨4,![5,4,11,12,18,6],![2,8,4,5,26,16]⟩
def cycle411_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle411_4 : CycleData E W := ⟨2,![22,17,13,23],![18,38,26,28]⟩
def cycle411_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data411 : PartitionData E W := ⟨6,![cycle411_0,cycle411_1,cycle411_2,cycle411_3,cycle411_4,cycle411_5]⟩
lemma valid_data411 : data411.Valid src411 dst411 Finset.univ := by decide +kernel

def src412 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,5,28,26,14,6,38,16,26,39,8,38,28,18,39]
def dst412 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,5,28,26,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle412_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle412_1 : CycleData E W := ⟨2,![2,3,15,8],![3,6,4,14]⟩
def cycle412_2 : CycleData E W := ⟨5,![5,4,11,12,22,17,6],![2,8,4,5,28,38,16]⟩
def cycle412_3 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle412_4 : CycleData E W := ⟨2,![23,13,19,24],![18,28,26,39]⟩
def cycle412_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data412 : PartitionData E W := ⟨6,![cycle412_0,cycle412_1,cycle412_2,cycle412_3,cycle412_4,cycle412_5]⟩
lemma valid_data412 : data412.Valid src412 dst412 Finset.univ := by decide +kernel

def src413 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,5,28,26,14,6,38,26,16,39,8,38,18,28,39]
def dst413 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,5,28,26,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle413_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle413_1 : CycleData E W := ⟨2,![2,3,15,8],![3,6,4,14]⟩
def cycle413_2 : CycleData E W := ⟨4,![4,21,17,13,12,11],![4,8,38,26,28,5]⟩
def cycle413_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle413_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle413_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data413 : PartitionData E W := ⟨6,![cycle413_0,cycle413_1,cycle413_2,cycle413_3,cycle413_4,cycle413_5]⟩
lemma valid_data413 : data413.Valid src413 dst413 Finset.univ := by decide +kernel

def src414 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst414 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle414_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle414_1 : CycleData E W := ⟨2,![2,3,11,8],![3,6,4,14]⟩
def cycle414_2 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle414_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle414_4 : CycleData E W := ⟨3,![7,18,22,23,12],![14,16,38,18,28]⟩
def cycle414_5 : CycleData E W := ⟨3,![13,24,20,16,14],![5,28,39,6,26]⟩
def data414 : PartitionData E W := ⟨6,![cycle414_0,cycle414_1,cycle414_2,cycle414_3,cycle414_4,cycle414_5]⟩
lemma valid_data414 : data414.Valid src414 dst414 Finset.univ := by decide +kernel

def src415 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst415 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle415_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle415_1 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle415_2 : CycleData E W := ⟨1,![3,16,15],![4,6,26]⟩
def cycle415_3 : CycleData E W := ⟨4,![5,4,11,12,23,10],![2,8,4,14,28,18]⟩
def cycle415_4 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def cycle415_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data415 : PartitionData E W := ⟨6,![cycle415_0,cycle415_1,cycle415_2,cycle415_3,cycle415_4,cycle415_5]⟩
lemma valid_data415 : data415.Valid src415 dst415 Finset.univ := by decide +kernel

def src416 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst416 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle416_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle416_1 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle416_2 : CycleData E W := ⟨1,![3,16,15],![4,6,26]⟩
def cycle416_3 : CycleData E W := ⟨4,![5,4,11,12,23,10],![2,8,4,14,28,18]⟩
def cycle416_4 : CycleData E W := ⟨2,![13,24,17,14],![5,28,39,26]⟩
def cycle416_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data416 : PartitionData E W := ⟨6,![cycle416_0,cycle416_1,cycle416_2,cycle416_3,cycle416_4,cycle416_5]⟩
lemma valid_data416 : data416.Valid src416 dst416 Finset.univ := by decide +kernel

def src417 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst417 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle417_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle417_1 : CycleData E W := ⟨2,![2,3,11,8],![3,6,4,14]⟩
def cycle417_2 : CycleData E W := ⟨3,![4,21,20,16,15],![4,8,38,6,26]⟩
def cycle417_3 : CycleData E W := ⟨2,![5,25,18,6],![2,8,39,16]⟩
def cycle417_4 : CycleData E W := ⟨2,![7,19,22,12],![14,16,38,28]⟩
def cycle417_5 : CycleData E W := ⟨3,![13,23,24,17,14],![5,28,18,39,26]⟩
def data417 : PartitionData E W := ⟨6,![cycle417_0,cycle417_1,cycle417_2,cycle417_3,cycle417_4,cycle417_5]⟩
lemma valid_data417 : data417.Valid src417 dst417 Finset.univ := by decide +kernel

def src418 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst418 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle418_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle418_1 : CycleData E W := ⟨2,![2,16,23,9],![3,6,38,18]⟩
def cycle418_2 : CycleData E W := ⟨2,![3,20,19,15],![4,6,39,26]⟩
def cycle418_3 : CycleData E W := ⟨2,![4,21,12,11],![4,8,28,14]⟩
def cycle418_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle418_5 : CycleData E W := ⟨3,![13,22,17,18,14],![5,28,38,16,26]⟩
def data418 : PartitionData E W := ⟨6,![cycle418_0,cycle418_1,cycle418_2,cycle418_3,cycle418_4,cycle418_5]⟩
lemma valid_data418 : data418.Valid src418 dst418 Finset.univ := by decide +kernel

def src419 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst419 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle419_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle419_1 : CycleData E W := ⟨2,![2,20,23,9],![3,6,39,18]⟩
def cycle419_2 : CycleData E W := ⟨3,![3,16,17,18,15],![4,6,38,16,26]⟩
def cycle419_3 : CycleData E W := ⟨2,![4,21,12,11],![4,8,28,14]⟩
def cycle419_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,38,18]⟩
def cycle419_5 : CycleData E W := ⟨2,![13,22,19,14],![5,28,39,26]⟩
def data419 : PartitionData E W := ⟨6,![cycle419_0,cycle419_1,cycle419_2,cycle419_3,cycle419_4,cycle419_5]⟩
lemma valid_data419 : data419.Valid src419 dst419 Finset.univ := by decide +kernel

def src420 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst420 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle420_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle420_1 : CycleData E W := ⟨2,![2,3,11,8],![3,6,4,14]⟩
def cycle420_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle420_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle420_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle420_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data420 : PartitionData E W := ⟨6,![cycle420_0,cycle420_1,cycle420_2,cycle420_3,cycle420_4,cycle420_5]⟩
lemma valid_data420 : data420.Valid src420 dst420 Finset.univ := by decide +kernel

def src421 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst421 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle421_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle421_1 : CycleData E W := ⟨2,![2,16,23,9],![3,6,38,18]⟩
def cycle421_2 : CycleData E W := ⟨3,![3,20,19,18,15],![4,6,39,16,26]⟩
def cycle421_3 : CycleData E W := ⟨2,![4,21,12,11],![4,8,28,14]⟩
def cycle421_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle421_5 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def data421 : PartitionData E W := ⟨6,![cycle421_0,cycle421_1,cycle421_2,cycle421_3,cycle421_4,cycle421_5]⟩
lemma valid_data421 : data421.Valid src421 dst421 Finset.univ := by decide +kernel

def src422 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst422 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle422_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,14,16]⟩
def cycle422_1 : CycleData E W := ⟨2,![2,20,23,9],![3,6,39,18]⟩
def cycle422_2 : CycleData E W := ⟨2,![3,16,17,15],![4,6,38,26]⟩
def cycle422_3 : CycleData E W := ⟨2,![4,21,12,11],![4,8,28,14]⟩
def cycle422_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,38,18]⟩
def cycle422_5 : CycleData E W := ⟨3,![13,22,19,18,14],![5,28,39,16,26]⟩
def data422 : PartitionData E W := ⟨6,![cycle422_0,cycle422_1,cycle422_2,cycle422_3,cycle422_4,cycle422_5]⟩
lemma valid_data422 : data422.Valid src422 dst422 Finset.univ := by decide +kernel

def src423 : E → W := ![2,5,3,6,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst423 : E → W := ![5,3,6,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle423_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle423_1 : CycleData E W := ⟨2,![2,3,11,8],![3,6,4,14]⟩
def cycle423_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle423_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle423_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle423_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data423 : PartitionData E W := ⟨6,![cycle423_0,cycle423_1,cycle423_2,cycle423_3,cycle423_4,cycle423_5]⟩
lemma valid_data423 : data423.Valid src423 dst423 Finset.univ := by decide +kernel

def src424 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,5,26,28,14,6,38,16,26,39,8,38,28,18,39]
def dst424 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,5,26,28,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle424_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle424_1 : CycleData E W := ⟨4,![2,3,11,12,18,8],![3,8,4,5,26,16]⟩
def cycle424_2 : CycleData E W := ⟨2,![5,4,15,6],![2,6,4,14]⟩
def cycle424_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle424_4 : CycleData E W := ⟨2,![23,13,19,24],![18,28,26,39]⟩
def cycle424_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data424 : PartitionData E W := ⟨6,![cycle424_0,cycle424_1,cycle424_2,cycle424_3,cycle424_4,cycle424_5]⟩
lemma valid_data424 : data424.Valid src424 dst424 Finset.univ := by decide +kernel

def src425 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,5,26,28,14,6,38,26,16,39,8,38,18,28,39]
def dst425 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,5,26,28,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle425_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle425_1 : CycleData E W := ⟨4,![2,3,11,12,18,8],![3,8,4,5,26,16]⟩
def cycle425_2 : CycleData E W := ⟨2,![5,4,15,6],![2,6,4,14]⟩
def cycle425_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle425_4 : CycleData E W := ⟨2,![22,17,13,23],![18,38,26,28]⟩
def cycle425_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data425 : PartitionData E W := ⟨6,![cycle425_0,cycle425_1,cycle425_2,cycle425_3,cycle425_4,cycle425_5]⟩
lemma valid_data425 : data425.Valid src425 dst425 Finset.univ := by decide +kernel

def src426 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,5,28,26,14,6,38,16,26,39,8,38,28,18,39]
def dst426 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,5,28,26,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle426_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle426_1 : CycleData E W := ⟨2,![2,21,17,8],![3,8,38,16]⟩
def cycle426_2 : CycleData E W := ⟨4,![3,25,19,13,12,11],![4,8,39,26,28,5]⟩
def cycle426_3 : CycleData E W := ⟨2,![5,4,15,6],![2,6,4,14]⟩
def cycle426_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle426_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data426 : PartitionData E W := ⟨6,![cycle426_0,cycle426_1,cycle426_2,cycle426_3,cycle426_4,cycle426_5]⟩
lemma valid_data426 : data426.Valid src426 dst426 Finset.univ := by decide +kernel

def src427 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,5,28,26,14,6,38,26,16,39,8,38,18,28,39]
def dst427 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,5,28,26,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle427_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle427_1 : CycleData E W := ⟨4,![2,21,16,20,19,8],![3,8,38,6,39,16]⟩
def cycle427_2 : CycleData E W := ⟨3,![3,25,24,12,11],![4,8,39,28,5]⟩
def cycle427_3 : CycleData E W := ⟨2,![5,4,15,6],![2,6,4,14]⟩
def cycle427_4 : CycleData E W := ⟨1,![7,18,14],![14,16,26]⟩
def cycle427_5 : CycleData E W := ⟨2,![22,17,13,23],![18,38,26,28]⟩
def data427 : PartitionData E W := ⟨6,![cycle427_0,cycle427_1,cycle427_2,cycle427_3,cycle427_4,cycle427_5]⟩
lemma valid_data427 : data427.Valid src427 dst427 Finset.univ := by decide +kernel

def src428 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst428 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle428_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle428_1 : CycleData E W := ⟨3,![2,3,11,7,8],![3,8,4,14,16]⟩
def cycle428_2 : CycleData E W := ⟨1,![4,16,15],![4,6,26]⟩
def cycle428_3 : CycleData E W := ⟨3,![5,20,24,12,6],![2,6,39,28,14]⟩
def cycle428_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle428_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data428 : PartitionData E W := ⟨6,![cycle428_0,cycle428_1,cycle428_2,cycle428_3,cycle428_4,cycle428_5]⟩
lemma valid_data428 : data428.Valid src428 dst428 Finset.univ := by decide +kernel

def src429 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst429 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle429_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle429_1 : CycleData E W := ⟨4,![2,3,11,12,23,9],![3,8,4,14,28,18]⟩
def cycle429_2 : CycleData E W := ⟨1,![4,16,15],![4,6,26]⟩
def cycle429_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle429_4 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def cycle429_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data429 : PartitionData E W := ⟨6,![cycle429_0,cycle429_1,cycle429_2,cycle429_3,cycle429_4,cycle429_5]⟩
lemma valid_data429 : data429.Valid src429 dst429 Finset.univ := by decide +kernel

def src430 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst430 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle430_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle430_1 : CycleData E W := ⟨4,![2,3,11,12,23,9],![3,8,4,14,28,18]⟩
def cycle430_2 : CycleData E W := ⟨1,![4,16,15],![4,6,26]⟩
def cycle430_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle430_4 : CycleData E W := ⟨2,![13,24,17,14],![5,28,39,26]⟩
def cycle430_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data430 : PartitionData E W := ⟨6,![cycle430_0,cycle430_1,cycle430_2,cycle430_3,cycle430_4,cycle430_5]⟩
lemma valid_data430 : data430.Valid src430 dst430 Finset.univ := by decide +kernel

def src431 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst431 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle431_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle431_1 : CycleData E W := ⟨3,![2,3,11,7,8],![3,8,4,14,16]⟩
def cycle431_2 : CycleData E W := ⟨1,![4,16,15],![4,6,26]⟩
def cycle431_3 : CycleData E W := ⟨3,![5,20,22,12,6],![2,6,38,28,14]⟩
def cycle431_4 : CycleData E W := ⟨3,![13,23,24,17,14],![5,28,18,39,26]⟩
def cycle431_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data431 : PartitionData E W := ⟨6,![cycle431_0,cycle431_1,cycle431_2,cycle431_3,cycle431_4,cycle431_5]⟩
lemma valid_data431 : data431.Valid src431 dst431 Finset.univ := by decide +kernel

def src432 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst432 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle432_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle432_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,39,18]⟩
def cycle432_2 : CycleData E W := ⟨2,![3,21,12,11],![4,8,28,14]⟩
def cycle432_3 : CycleData E W := ⟨2,![4,20,19,15],![4,6,39,26]⟩
def cycle432_4 : CycleData E W := ⟨2,![5,16,23,10],![2,6,38,18]⟩
def cycle432_5 : CycleData E W := ⟨3,![13,22,17,18,14],![5,28,38,16,26]⟩
def data432 : PartitionData E W := ⟨6,![cycle432_0,cycle432_1,cycle432_2,cycle432_3,cycle432_4,cycle432_5]⟩
lemma valid_data432 : data432.Valid src432 dst432 Finset.univ := by decide +kernel

def src433 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst433 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle433_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle433_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,38,18]⟩
def cycle433_2 : CycleData E W := ⟨2,![3,21,12,11],![4,8,28,14]⟩
def cycle433_3 : CycleData E W := ⟨3,![4,16,17,18,15],![4,6,38,16,26]⟩
def cycle433_4 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle433_5 : CycleData E W := ⟨2,![13,22,19,14],![5,28,39,26]⟩
def data433 : PartitionData E W := ⟨6,![cycle433_0,cycle433_1,cycle433_2,cycle433_3,cycle433_4,cycle433_5]⟩
lemma valid_data433 : data433.Valid src433 dst433 Finset.univ := by decide +kernel

def src434 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst434 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle434_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle434_1 : CycleData E W := ⟨3,![2,3,15,18,8],![3,8,4,26,16]⟩
def cycle434_2 : CycleData E W := ⟨2,![5,4,11,6],![2,6,4,14]⟩
def cycle434_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle434_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle434_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data434 : PartitionData E W := ⟨6,![cycle434_0,cycle434_1,cycle434_2,cycle434_3,cycle434_4,cycle434_5]⟩
lemma valid_data434 : data434.Valid src434 dst434 Finset.univ := by decide +kernel

def src435 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst435 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle435_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle435_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,39,18]⟩
def cycle435_2 : CycleData E W := ⟨2,![3,21,12,11],![4,8,28,14]⟩
def cycle435_3 : CycleData E W := ⟨3,![4,20,19,18,15],![4,6,39,16,26]⟩
def cycle435_4 : CycleData E W := ⟨2,![5,16,23,10],![2,6,38,18]⟩
def cycle435_5 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def data435 : PartitionData E W := ⟨6,![cycle435_0,cycle435_1,cycle435_2,cycle435_3,cycle435_4,cycle435_5]⟩
lemma valid_data435 : data435.Valid src435 dst435 Finset.univ := by decide +kernel

def src436 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst436 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle436_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,5,3,16,14]⟩
def cycle436_1 : CycleData E W := ⟨2,![2,25,24,9],![3,8,38,18]⟩
def cycle436_2 : CycleData E W := ⟨2,![3,21,12,11],![4,8,28,14]⟩
def cycle436_3 : CycleData E W := ⟨2,![4,16,17,15],![4,6,38,26]⟩
def cycle436_4 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle436_5 : CycleData E W := ⟨3,![13,22,19,18,14],![5,28,39,16,26]⟩
def data436 : PartitionData E W := ⟨6,![cycle436_0,cycle436_1,cycle436_2,cycle436_3,cycle436_4,cycle436_5]⟩
lemma valid_data436 : data436.Valid src436 dst436 Finset.univ := by decide +kernel

def src437 : E → W := ![2,5,3,8,4,6,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst437 : E → W := ![5,3,8,4,6,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle437_0 : CycleData E W := ⟨2,![0,1,9,10],![2,5,3,18]⟩
def cycle437_1 : CycleData E W := ⟨3,![2,3,15,18,8],![3,8,4,26,16]⟩
def cycle437_2 : CycleData E W := ⟨2,![5,4,11,6],![2,6,4,14]⟩
def cycle437_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle437_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle437_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data437 : PartitionData E W := ⟨6,![cycle437_0,cycle437_1,cycle437_2,cycle437_3,cycle437_4,cycle437_5]⟩
lemma valid_data437 : data437.Valid src437 dst437 Finset.univ := by decide +kernel

def src438 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,5,26,28,14,6,38,16,26,39,8,38,28,18,39]
def dst438 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,5,26,28,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle438_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle438_1 : CycleData E W := ⟨2,![2,3,15,8],![3,8,4,14]⟩
def cycle438_2 : CycleData E W := ⟨4,![4,16,17,18,12,11],![4,6,38,16,26,5]⟩
def cycle438_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle438_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle438_5 : CycleData E W := ⟨3,![21,22,13,19,25],![8,38,28,26,39]⟩
def data438 : PartitionData E W := ⟨6,![cycle438_0,cycle438_1,cycle438_2,cycle438_3,cycle438_4,cycle438_5]⟩
lemma valid_data438 : data438.Valid src438 dst438 Finset.univ := by decide +kernel

def src439 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,5,26,28,14,6,38,26,16,39,8,38,18,28,39]
def dst439 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,5,26,28,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle439_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle439_1 : CycleData E W := ⟨2,![2,3,15,8],![3,8,4,14]⟩
def cycle439_2 : CycleData E W := ⟨3,![4,16,17,12,11],![4,6,38,26,5]⟩
def cycle439_3 : CycleData E W := ⟨4,![5,20,25,21,22,10],![2,6,39,8,38,18]⟩
def cycle439_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle439_5 : CycleData E W := ⟨2,![18,13,24,19],![16,26,28,39]⟩
def data439 : PartitionData E W := ⟨6,![cycle439_0,cycle439_1,cycle439_2,cycle439_3,cycle439_4,cycle439_5]⟩
lemma valid_data439 : data439.Valid src439 dst439 Finset.univ := by decide +kernel

def src440 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,5,28,26,14,6,38,16,26,39,8,38,28,18,39]
def dst440 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,5,28,26,14,4,38,16,26,39,6,38,28,18,39,8]
def cycle440_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle440_1 : CycleData E W := ⟨2,![2,3,15,8],![3,8,4,14]⟩
def cycle440_2 : CycleData E W := ⟨3,![4,16,22,12,11],![4,6,38,28,5]⟩
def cycle440_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle440_4 : CycleData E W := ⟨2,![9,23,13,14],![14,18,28,26]⟩
def cycle440_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data440 : PartitionData E W := ⟨6,![cycle440_0,cycle440_1,cycle440_2,cycle440_3,cycle440_4,cycle440_5]⟩
lemma valid_data440 : data440.Valid src440 dst440 Finset.univ := by decide +kernel

def src441 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,5,28,26,14,6,38,26,16,39,8,38,18,28,39]
def dst441 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,5,28,26,14,4,38,26,16,39,6,38,18,28,39,8]
def cycle441_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle441_1 : CycleData E W := ⟨2,![2,3,15,8],![3,8,4,14]⟩
def cycle441_2 : CycleData E W := ⟨4,![5,4,11,12,23,10],![2,6,4,5,28,18]⟩
def cycle441_3 : CycleData E W := ⟨2,![9,22,17,14],![14,18,38,26]⟩
def cycle441_4 : CycleData E W := ⟨2,![18,13,24,19],![16,26,28,39]⟩
def cycle441_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data441 : PartitionData E W := ⟨6,![cycle441_0,cycle441_1,cycle441_2,cycle441_3,cycle441_4,cycle441_5]⟩
lemma valid_data441 : data441.Valid src441 dst441 Finset.univ := by decide +kernel

def src442 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst442 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle442_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle442_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle442_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle442_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle442_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle442_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data442 : PartitionData E W := ⟨6,![cycle442_0,cycle442_1,cycle442_2,cycle442_3,cycle442_4,cycle442_5]⟩
lemma valid_data442 : data442.Valid src442 dst442 Finset.univ := by decide +kernel

def src443 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst443 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle443_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle443_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle443_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle443_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle443_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle443_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data443 : PartitionData E W := ⟨6,![cycle443_0,cycle443_1,cycle443_2,cycle443_3,cycle443_4,cycle443_5]⟩
lemma valid_data443 : data443.Valid src443 dst443 Finset.univ := by decide +kernel

def src444 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst444 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle444_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle444_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle444_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle444_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle444_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle444_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data444 : PartitionData E W := ⟨6,![cycle444_0,cycle444_1,cycle444_2,cycle444_3,cycle444_4,cycle444_5]⟩
lemma valid_data444 : data444.Valid src444 dst444 Finset.univ := by decide +kernel

def src445 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst445 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle445_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle445_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle445_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle445_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle445_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle445_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data445 : PartitionData E W := ⟨6,![cycle445_0,cycle445_1,cycle445_2,cycle445_3,cycle445_4,cycle445_5]⟩
lemma valid_data445 : data445.Valid src445 dst445 Finset.univ := by decide +kernel

def src446 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst446 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle446_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle446_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle446_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle446_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle446_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle446_5 : CycleData E W := ⟨3,![13,19,25,21,14],![5,26,39,8,28]⟩
def data446 : PartitionData E W := ⟨6,![cycle446_0,cycle446_1,cycle446_2,cycle446_3,cycle446_4,cycle446_5]⟩
lemma valid_data446 : data446.Valid src446 dst446 Finset.univ := by decide +kernel

def src447 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst447 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle447_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle447_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle447_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle447_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle447_4 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle447_5 : CycleData E W := ⟨4,![13,18,17,25,21,14],![5,26,16,38,8,28]⟩
def data447 : PartitionData E W := ⟨6,![cycle447_0,cycle447_1,cycle447_2,cycle447_3,cycle447_4,cycle447_5]⟩
lemma valid_data447 : data447.Valid src447 dst447 Finset.univ := by decide +kernel

def src448 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst448 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle448_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle448_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle448_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle448_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle448_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle448_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data448 : PartitionData E W := ⟨6,![cycle448_0,cycle448_1,cycle448_2,cycle448_3,cycle448_4,cycle448_5]⟩
lemma valid_data448 : data448.Valid src448 dst448 Finset.univ := by decide +kernel

def src449 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst449 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle449_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle449_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle449_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle449_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle449_4 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle449_5 : CycleData E W := ⟨4,![13,18,19,25,21,14],![5,26,16,39,8,28]⟩
def data449 : PartitionData E W := ⟨6,![cycle449_0,cycle449_1,cycle449_2,cycle449_3,cycle449_4,cycle449_5]⟩
lemma valid_data449 : data449.Valid src449 dst449 Finset.univ := by decide +kernel

def lookupB8 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data400 else (if j < 2 then data401 else data402)) else (if j < 4 then data403 else (if j < 5 then data404 else data405))) else (if j < 9 then (if j < 7 then data406 else (if j < 8 then data407 else data408)) else (if j < 10 then data409 else (if j < 11 then data410 else data411)))) else (if j < 18 then (if j < 15 then (if j < 13 then data412 else (if j < 14 then data413 else data414)) else (if j < 16 then data415 else (if j < 17 then data416 else data417))) else (if j < 21 then (if j < 19 then data418 else (if j < 20 then data419 else data420)) else (if j < 23 then (if j < 22 then data421 else data422) else (if j < 24 then data423 else data424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data425 else (if j < 27 then data426 else data427)) else (if j < 29 then data428 else (if j < 30 then data429 else data430))) else (if j < 34 then (if j < 32 then data431 else (if j < 33 then data432 else data433)) else (if j < 35 then data434 else (if j < 36 then data435 else data436)))) else (if j < 43 then (if j < 40 then (if j < 38 then data437 else (if j < 39 then data438 else data439)) else (if j < 41 then data440 else (if j < 42 then data441 else data442))) else (if j < 46 then (if j < 44 then data443 else (if j < 45 then data444 else data445)) else (if j < 48 then (if j < 47 then data446 else data447) else (if j < 49 then data448 else data449))))))

def srcTableB8 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src400 else (if j < 2 then src401 else src402)) else (if j < 4 then src403 else (if j < 5 then src404 else src405))) else (if j < 9 then (if j < 7 then src406 else (if j < 8 then src407 else src408)) else (if j < 10 then src409 else (if j < 11 then src410 else src411)))) else (if j < 18 then (if j < 15 then (if j < 13 then src412 else (if j < 14 then src413 else src414)) else (if j < 16 then src415 else (if j < 17 then src416 else src417))) else (if j < 21 then (if j < 19 then src418 else (if j < 20 then src419 else src420)) else (if j < 23 then (if j < 22 then src421 else src422) else (if j < 24 then src423 else src424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src425 else (if j < 27 then src426 else src427)) else (if j < 29 then src428 else (if j < 30 then src429 else src430))) else (if j < 34 then (if j < 32 then src431 else (if j < 33 then src432 else src433)) else (if j < 35 then src434 else (if j < 36 then src435 else src436)))) else (if j < 43 then (if j < 40 then (if j < 38 then src437 else (if j < 39 then src438 else src439)) else (if j < 41 then src440 else (if j < 42 then src441 else src442))) else (if j < 46 then (if j < 44 then src443 else (if j < 45 then src444 else src445)) else (if j < 48 then (if j < 47 then src446 else src447) else (if j < 49 then src448 else src449))))))

def dstTableB8 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst400 else (if j < 2 then dst401 else dst402)) else (if j < 4 then dst403 else (if j < 5 then dst404 else dst405))) else (if j < 9 then (if j < 7 then dst406 else (if j < 8 then dst407 else dst408)) else (if j < 10 then dst409 else (if j < 11 then dst410 else dst411)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst412 else (if j < 14 then dst413 else dst414)) else (if j < 16 then dst415 else (if j < 17 then dst416 else dst417))) else (if j < 21 then (if j < 19 then dst418 else (if j < 20 then dst419 else dst420)) else (if j < 23 then (if j < 22 then dst421 else dst422) else (if j < 24 then dst423 else dst424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst425 else (if j < 27 then dst426 else dst427)) else (if j < 29 then dst428 else (if j < 30 then dst429 else dst430))) else (if j < 34 then (if j < 32 then dst431 else (if j < 33 then dst432 else dst433)) else (if j < 35 then dst434 else (if j < 36 then dst435 else dst436)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst437 else (if j < 39 then dst438 else dst439)) else (if j < 41 then dst440 else (if j < 42 then dst441 else dst442))) else (if j < 46 then (if j < 44 then dst443 else (if j < 45 then dst444 else dst445)) else (if j < 48 then (if j < 47 then dst446 else dst447) else (if j < 49 then dst448 else dst449))))))

def caseB8 (i : Fin 50) : Cases := ⟨400 + i.val,by have := i.isLt; omega⟩
lemma tableB8_valid (i : Fin 50) :
    (lookupB8 i.val).Valid (srcTableB8 i.val) (dstTableB8 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data400
  · exact valid_data401
  · exact valid_data402
  · exact valid_data403
  · exact valid_data404
  · exact valid_data405
  · exact valid_data406
  · exact valid_data407
  · exact valid_data408
  · exact valid_data409
  · exact valid_data410
  · exact valid_data411
  · exact valid_data412
  · exact valid_data413
  · exact valid_data414
  · exact valid_data415
  · exact valid_data416
  · exact valid_data417
  · exact valid_data418
  · exact valid_data419
  · exact valid_data420
  · exact valid_data421
  · exact valid_data422
  · exact valid_data423
  · exact valid_data424
  · exact valid_data425
  · exact valid_data426
  · exact valid_data427
  · exact valid_data428
  · exact valid_data429
  · exact valid_data430
  · exact valid_data431
  · exact valid_data432
  · exact valid_data433
  · exact valid_data434
  · exact valid_data435
  · exact valid_data436
  · exact valid_data437
  · exact valid_data438
  · exact valid_data439
  · exact valid_data440
  · exact valid_data441
  · exact valid_data442
  · exact valid_data443
  · exact valid_data444
  · exact valid_data445
  · exact valid_data446
  · exact valid_data447
  · exact valid_data448
  · exact valid_data449

lemma srcB8_row : ∀ (i : Fin 50) (e : E),
    srcTableB8 i.val e = caseSource (caseB8 i) e := by decide +kernel

lemma dstB8_row : ∀ (i : Fin 50) (e : E),
    dstTableB8 i.val e = caseTarget (caseB8 i) e := by decide +kernel

lemma sizeB8 : ∀ i : Fin 50, (lookupB8 i.val).size ≤ 5 →
    (lookupB8 i.val).size = 2 ∧
      (⟨caseKey (caseB8 i),caseKey_lt (caseB8 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB8 (i : Fin 50) : Certificate (caseB8 i) := by
  refine ⟨lookupB8 i.val,?_,sizeB8 i⟩
  have hv := tableB8_valid i
  rw [funext (srcB8_row i),funext (dstB8_row i)] at hv
  exact hv
lemma certificateInterval8 : FiniteIntervals.Covers CertificateAt 400 450 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 400 50 (fun i _ => certificateB8 i)
#print axioms certificateInterval8
end Erdos184Work.FiveRows4

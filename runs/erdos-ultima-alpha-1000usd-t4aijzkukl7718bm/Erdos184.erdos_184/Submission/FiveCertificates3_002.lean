import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src400 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst400 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle400_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle400_1 : CycleData E W := ⟨3,![1,2,19,12,7],![3,8,6,27,14]⟩
def cycle400_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle400_3 : CycleData E W := ⟨3,![4,14,23,20,9],![2,4,28,8,18]⟩
def cycle400_4 : CycleData E W := ⟨2,![8,21,16,11],![14,18,38,26]⟩
def cycle400_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data400 : PartitionData E W := ⟨6,![cycle400_0,cycle400_1,cycle400_2,cycle400_3,cycle400_4,cycle400_5]⟩
lemma valid_data400 : data400.Valid src400 dst400 Finset.univ := by decide +kernel

def src401 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst401 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle401_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle401_1 : CycleData E W := ⟨3,![1,2,19,12,7],![3,8,6,27,14]⟩
def cycle401_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle401_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle401_4 : CycleData E W := ⟨2,![8,22,16,11],![14,18,38,26]⟩
def cycle401_5 : CycleData E W := ⟨3,![20,13,18,17,23],![8,28,27,16,38]⟩
def data401 : PartitionData E W := ⟨6,![cycle401_0,cycle401_1,cycle401_2,cycle401_3,cycle401_4,cycle401_5]⟩
lemma valid_data401 : data401.Valid src401 dst401 Finset.univ := by decide +kernel

def src402 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst402 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle402_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle402_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle402_2 : CycleData E W := ⟨3,![3,2,23,18,10],![4,6,8,38,26]⟩
def cycle402_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle402_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle402_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data402 : PartitionData E W := ⟨6,![cycle402_0,cycle402_1,cycle402_2,cycle402_3,cycle402_4,cycle402_5]⟩
lemma valid_data402 : data402.Valid src402 dst402 Finset.univ := by decide +kernel

def src403 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst403 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle403_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle403_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle403_2 : CycleData E W := ⟨2,![3,2,23,14],![4,6,8,28]⟩
def cycle403_3 : CycleData E W := ⟨3,![4,10,18,21,9],![2,4,26,38,18]⟩
def cycle403_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle403_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data403 : PartitionData E W := ⟨6,![cycle403_0,cycle403_1,cycle403_2,cycle403_3,cycle403_4,cycle403_5]⟩
lemma valid_data403 : data403.Valid src403 dst403 Finset.univ := by decide +kernel

def src404 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst404 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle404_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle404_1 : CycleData E W := ⟨3,![1,20,13,12,7],![3,8,28,27,14]⟩
def cycle404_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle404_3 : CycleData E W := ⟨3,![3,15,16,17,10],![4,6,27,16,26]⟩
def cycle404_4 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle404_5 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,26]⟩
def data404 : PartitionData E W := ⟨6,![cycle404_0,cycle404_1,cycle404_2,cycle404_3,cycle404_4,cycle404_5]⟩
lemma valid_data404 : data404.Valid src404 dst404 Finset.univ := by decide +kernel

def src405 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst405 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle405_0 : CycleData E W := ⟨2,![0,1,20,9],![2,3,8,18]⟩
def cycle405_1 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle405_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle405_3 : CycleData E W := ⟨2,![4,14,17,5],![2,4,27,16]⟩
def cycle405_4 : CycleData E W := ⟨2,![6,16,11,7],![3,16,26,14]⟩
def cycle405_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle405_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data405 : PartitionData E W := ⟨7,![cycle405_0,cycle405_1,cycle405_2,cycle405_3,cycle405_4,cycle405_5,cycle405_6]⟩
lemma valid_data405 : data405.Valid src405 dst405 Finset.univ := by decide +kernel

def src406 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst406 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle406_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle406_1 : CycleData E W := ⟨3,![1,2,15,11,7],![3,8,6,26,14]⟩
def cycle406_2 : CycleData E W := ⟨3,![4,3,19,21,9],![2,4,6,38,18]⟩
def cycle406_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle406_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle406_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data406 : PartitionData E W := ⟨6,![cycle406_0,cycle406_1,cycle406_2,cycle406_3,cycle406_4,cycle406_5]⟩
lemma valid_data406 : data406.Valid src406 dst406 Finset.univ := by decide +kernel

def src407 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst407 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle407_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle407_1 : CycleData E W := ⟨3,![1,2,15,11,7],![3,8,6,26,14]⟩
def cycle407_2 : CycleData E W := ⟨3,![4,3,19,22,9],![2,4,6,38,18]⟩
def cycle407_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle407_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle407_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data407 : PartitionData E W := ⟨6,![cycle407_0,cycle407_1,cycle407_2,cycle407_3,cycle407_4,cycle407_5]⟩
lemma valid_data407 : data407.Valid src407 dst407 Finset.univ := by decide +kernel

def src408 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst408 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle408_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle408_1 : CycleData E W := ⟨3,![1,2,15,11,7],![3,8,6,26,14]⟩
def cycle408_2 : CycleData E W := ⟨1,![3,19,14],![4,6,27]⟩
def cycle408_3 : CycleData E W := ⟨4,![4,10,16,23,20,9],![2,4,26,38,8,18]⟩
def cycle408_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle408_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data408 : PartitionData E W := ⟨6,![cycle408_0,cycle408_1,cycle408_2,cycle408_3,cycle408_4,cycle408_5]⟩
lemma valid_data408 : data408.Valid src408 dst408 Finset.univ := by decide +kernel

def src409 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst409 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle409_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle409_1 : CycleData E W := ⟨3,![1,2,15,11,7],![3,8,6,26,14]⟩
def cycle409_2 : CycleData E W := ⟨1,![3,19,14],![4,6,27]⟩
def cycle409_3 : CycleData E W := ⟨3,![4,10,16,21,9],![2,4,26,38,18]⟩
def cycle409_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle409_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data409 : PartitionData E W := ⟨6,![cycle409_0,cycle409_1,cycle409_2,cycle409_3,cycle409_4,cycle409_5]⟩
lemma valid_data409 : data409.Valid src409 dst409 Finset.univ := by decide +kernel

def src410 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst410 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle410_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle410_1 : CycleData E W := ⟨3,![1,2,15,11,7],![3,8,6,26,14]⟩
def cycle410_2 : CycleData E W := ⟨1,![3,19,14],![4,6,27]⟩
def cycle410_3 : CycleData E W := ⟨3,![4,10,16,22,9],![2,4,26,38,18]⟩
def cycle410_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle410_5 : CycleData E W := ⟨3,![20,13,18,17,23],![8,28,27,16,38]⟩
def data410 : PartitionData E W := ⟨6,![cycle410_0,cycle410_1,cycle410_2,cycle410_3,cycle410_4,cycle410_5]⟩
lemma valid_data410 : data410.Valid src410 dst410 Finset.univ := by decide +kernel

def src411 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst411 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle411_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle411_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle411_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle411_3 : CycleData E W := ⟨1,![3,15,14],![4,6,27]⟩
def cycle411_4 : CycleData E W := ⟨4,![4,10,11,12,21,9],![2,4,26,14,28,18]⟩
def cycle411_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data411 : PartitionData E W := ⟨6,![cycle411_0,cycle411_1,cycle411_2,cycle411_3,cycle411_4,cycle411_5]⟩
lemma valid_data411 : data411.Valid src411 dst411 Finset.univ := by decide +kernel

def src412 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst412 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle412_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle412_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle412_2 : CycleData E W := ⟨2,![2,23,13,15],![6,8,28,27]⟩
def cycle412_3 : CycleData E W := ⟨3,![4,3,19,21,9],![2,4,6,38,18]⟩
def cycle412_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle412_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data412 : PartitionData E W := ⟨6,![cycle412_0,cycle412_1,cycle412_2,cycle412_3,cycle412_4,cycle412_5]⟩
lemma valid_data412 : data412.Valid src412 dst412 Finset.univ := by decide +kernel

def src413 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst413 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle413_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle413_1 : CycleData E W := ⟨2,![1,20,12,7],![3,8,28,14]⟩
def cycle413_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle413_3 : CycleData E W := ⟨1,![3,15,14],![4,6,27]⟩
def cycle413_4 : CycleData E W := ⟨3,![4,10,11,8,9],![2,4,26,14,18]⟩
def cycle413_5 : CycleData E W := ⟨4,![16,13,21,22,18,17],![16,27,28,18,38,26]⟩
def data413 : PartitionData E W := ⟨6,![cycle413_0,cycle413_1,cycle413_2,cycle413_3,cycle413_4,cycle413_5]⟩
lemma valid_data413 : data413.Valid src413 dst413 Finset.univ := by decide +kernel

def src414 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst414 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle414_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle414_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle414_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle414_3 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle414_4 : CycleData E W := ⟨4,![4,14,13,12,21,9],![2,4,27,14,28,18]⟩
def cycle414_5 : CycleData E W := ⟨3,![16,11,22,18,17],![16,26,28,38,27]⟩
def data414 : PartitionData E W := ⟨6,![cycle414_0,cycle414_1,cycle414_2,cycle414_3,cycle414_4,cycle414_5]⟩
lemma valid_data414 : data414.Valid src414 dst414 Finset.univ := by decide +kernel

def src415 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst415 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle415_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle415_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle415_2 : CycleData E W := ⟨2,![2,23,11,15],![6,8,28,26]⟩
def cycle415_3 : CycleData E W := ⟨3,![4,3,19,21,9],![2,4,6,38,18]⟩
def cycle415_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle415_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data415 : PartitionData E W := ⟨6,![cycle415_0,cycle415_1,cycle415_2,cycle415_3,cycle415_4,cycle415_5]⟩
lemma valid_data415 : data415.Valid src415 dst415 Finset.univ := by decide +kernel

def src416 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst416 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle416_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle416_1 : CycleData E W := ⟨2,![1,20,12,7],![3,8,28,14]⟩
def cycle416_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle416_3 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle416_4 : CycleData E W := ⟨3,![4,14,13,8,9],![2,4,27,14,18]⟩
def cycle416_5 : CycleData E W := ⟨4,![16,11,21,22,18,17],![16,26,28,18,38,27]⟩
def data416 : PartitionData E W := ⟨6,![cycle416_0,cycle416_1,cycle416_2,cycle416_3,cycle416_4,cycle416_5]⟩
lemma valid_data416 : data416.Valid src416 dst416 Finset.univ := by decide +kernel

def src417 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst417 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle417_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle417_1 : CycleData E W := ⟨3,![1,2,19,13,7],![3,8,6,27,14]⟩
def cycle417_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle417_3 : CycleData E W := ⟨4,![4,14,18,23,20,9],![2,4,27,38,8,18]⟩
def cycle417_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle417_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data417 : PartitionData E W := ⟨6,![cycle417_0,cycle417_1,cycle417_2,cycle417_3,cycle417_4,cycle417_5]⟩
lemma valid_data417 : data417.Valid src417 dst417 Finset.univ := by decide +kernel

def src418 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst418 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle418_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle418_1 : CycleData E W := ⟨3,![1,2,19,13,7],![3,8,6,27,14]⟩
def cycle418_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle418_3 : CycleData E W := ⟨3,![4,14,18,21,9],![2,4,27,38,18]⟩
def cycle418_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle418_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data418 : PartitionData E W := ⟨6,![cycle418_0,cycle418_1,cycle418_2,cycle418_3,cycle418_4,cycle418_5]⟩
lemma valid_data418 : data418.Valid src418 dst418 Finset.univ := by decide +kernel

def src419 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst419 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle419_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle419_1 : CycleData E W := ⟨3,![1,2,19,13,7],![3,8,6,27,14]⟩
def cycle419_2 : CycleData E W := ⟨1,![3,15,10],![4,6,26]⟩
def cycle419_3 : CycleData E W := ⟨3,![4,14,18,22,9],![2,4,27,38,18]⟩
def cycle419_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle419_5 : CycleData E W := ⟨3,![20,11,16,17,23],![8,28,26,16,38]⟩
def data419 : PartitionData E W := ⟨6,![cycle419_0,cycle419_1,cycle419_2,cycle419_3,cycle419_4,cycle419_5]⟩
lemma valid_data419 : data419.Valid src419 dst419 Finset.univ := by decide +kernel

def src420 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst420 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle420_0 : CycleData E W := ⟨2,![0,1,20,9],![2,3,8,18]⟩
def cycle420_1 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle420_2 : CycleData E W := ⟨1,![3,15,14],![4,6,27]⟩
def cycle420_3 : CycleData E W := ⟨2,![4,10,17,5],![2,4,26,16]⟩
def cycle420_4 : CycleData E W := ⟨2,![6,16,13,7],![3,16,27,14]⟩
def cycle420_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle420_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data420 : PartitionData E W := ⟨7,![cycle420_0,cycle420_1,cycle420_2,cycle420_3,cycle420_4,cycle420_5,cycle420_6]⟩
lemma valid_data420 : data420.Valid src420 dst420 Finset.univ := by decide +kernel

def src421 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst421 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle421_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle421_1 : CycleData E W := ⟨3,![1,2,15,13,7],![3,8,6,27,14]⟩
def cycle421_2 : CycleData E W := ⟨3,![4,3,19,21,9],![2,4,6,38,18]⟩
def cycle421_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle421_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle421_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data421 : PartitionData E W := ⟨6,![cycle421_0,cycle421_1,cycle421_2,cycle421_3,cycle421_4,cycle421_5]⟩
lemma valid_data421 : data421.Valid src421 dst421 Finset.univ := by decide +kernel

def src422 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst422 : E → W := ![3,8,6,4,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle422_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle422_1 : CycleData E W := ⟨3,![1,2,15,13,7],![3,8,6,27,14]⟩
def cycle422_2 : CycleData E W := ⟨3,![4,3,19,22,9],![2,4,6,38,18]⟩
def cycle422_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle422_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle422_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data422 : PartitionData E W := ⟨6,![cycle422_0,cycle422_1,cycle422_2,cycle422_3,cycle422_4,cycle422_5]⟩
lemma valid_data422 : data422.Valid src422 dst422 Finset.univ := by decide +kernel

def src423 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst423 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle423_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle423_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle423_2 : CycleData E W := ⟨3,![3,2,23,18,10],![4,6,8,38,27]⟩
def cycle423_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle423_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle423_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data423 : PartitionData E W := ⟨6,![cycle423_0,cycle423_1,cycle423_2,cycle423_3,cycle423_4,cycle423_5]⟩
lemma valid_data423 : data423.Valid src423 dst423 Finset.univ := by decide +kernel

def src424 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst424 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle424_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle424_1 : CycleData E W := ⟨2,![1,20,8,7],![3,8,18,14]⟩
def cycle424_2 : CycleData E W := ⟨2,![3,2,23,14],![4,6,8,28]⟩
def cycle424_3 : CycleData E W := ⟨3,![4,10,18,21,9],![2,4,27,38,18]⟩
def cycle424_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle424_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data424 : PartitionData E W := ⟨6,![cycle424_0,cycle424_1,cycle424_2,cycle424_3,cycle424_4,cycle424_5]⟩
lemma valid_data424 : data424.Valid src424 dst424 Finset.univ := by decide +kernel

def src425 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst425 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle425_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle425_1 : CycleData E W := ⟨3,![1,20,13,12,7],![3,8,28,26,14]⟩
def cycle425_2 : CycleData E W := ⟨1,![2,23,19],![6,8,38]⟩
def cycle425_3 : CycleData E W := ⟨3,![3,15,16,17,10],![4,6,26,16,27]⟩
def cycle425_4 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle425_5 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def data425 : PartitionData E W := ⟨6,![cycle425_0,cycle425_1,cycle425_2,cycle425_3,cycle425_4,cycle425_5]⟩
lemma valid_data425 : data425.Valid src425 dst425 Finset.univ := by decide +kernel

def src426 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst426 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle426_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle426_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle426_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle426_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle426_4 : CycleData E W := ⟨3,![20,8,11,18,23],![8,18,14,27,38]⟩
def cycle426_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data426 : PartitionData E W := ⟨6,![cycle426_0,cycle426_1,cycle426_2,cycle426_3,cycle426_4,cycle426_5]⟩
lemma valid_data426 : data426.Valid src426 dst426 Finset.univ := by decide +kernel

def src427 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst427 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle427_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle427_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle427_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle427_3 : CycleData E W := ⟨3,![4,14,23,20,9],![2,4,28,8,18]⟩
def cycle427_4 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle427_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data427 : PartitionData E W := ⟨6,![cycle427_0,cycle427_1,cycle427_2,cycle427_3,cycle427_4,cycle427_5]⟩
lemma valid_data427 : data427.Valid src427 dst427 Finset.univ := by decide +kernel

def src428 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst428 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle428_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle428_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle428_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle428_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle428_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def cycle428_5 : CycleData E W := ⟨3,![20,13,16,17,23],![8,28,26,16,38]⟩
def data428 : PartitionData E W := ⟨6,![cycle428_0,cycle428_1,cycle428_2,cycle428_3,cycle428_4,cycle428_5]⟩
lemma valid_data428 : data428.Valid src428 dst428 Finset.univ := by decide +kernel

def src429 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst429 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle429_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle429_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle429_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle429_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle429_4 : CycleData E W := ⟨4,![20,8,11,18,17,23],![8,18,14,27,16,38]⟩
def cycle429_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data429 : PartitionData E W := ⟨6,![cycle429_0,cycle429_1,cycle429_2,cycle429_3,cycle429_4,cycle429_5]⟩
lemma valid_data429 : data429.Valid src429 dst429 Finset.univ := by decide +kernel

def src430 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst430 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle430_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle430_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle430_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle430_3 : CycleData E W := ⟨3,![4,14,23,20,9],![2,4,28,8,18]⟩
def cycle430_4 : CycleData E W := ⟨3,![8,21,17,18,11],![14,18,38,16,27]⟩
def cycle430_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data430 : PartitionData E W := ⟨6,![cycle430_0,cycle430_1,cycle430_2,cycle430_3,cycle430_4,cycle430_5]⟩
lemma valid_data430 : data430.Valid src430 dst430 Finset.univ := by decide +kernel

def src431 : E → W := ![2,3,8,6,4,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst431 : E → W := ![3,8,6,4,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle431_0 : CycleData E W := ⟨1,![0,6,5],![2,3,16]⟩
def cycle431_1 : CycleData E W := ⟨3,![1,2,15,12,7],![3,8,6,26,14]⟩
def cycle431_2 : CycleData E W := ⟨1,![3,19,10],![4,6,27]⟩
def cycle431_3 : CycleData E W := ⟨2,![4,14,21,9],![2,4,28,18]⟩
def cycle431_4 : CycleData E W := ⟨3,![8,22,17,18,11],![14,18,38,16,27]⟩
def cycle431_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data431 : PartitionData E W := ⟨6,![cycle431_0,cycle431_1,cycle431_2,cycle431_3,cycle431_4,cycle431_5]⟩
lemma valid_data431 : data431.Valid src431 dst431 Finset.univ := by decide +kernel

def src432 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst432 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle432_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle432_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle432_2 : CycleData E W := ⟨3,![3,20,7,12,19],![6,8,18,14,27]⟩
def cycle432_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle432_4 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle432_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data432 : PartitionData E W := ⟨6,![cycle432_0,cycle432_1,cycle432_2,cycle432_3,cycle432_4,cycle432_5]⟩
lemma valid_data432 : data432.Valid src432 dst432 Finset.univ := by decide +kernel

def src433 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst433 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle433_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle433_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle433_2 : CycleData E W := ⟨3,![3,20,7,12,19],![6,8,18,14,27]⟩
def cycle433_3 : CycleData E W := ⟨4,![4,23,14,10,16,9],![2,8,28,4,26,16]⟩
def cycle433_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle433_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data433 : PartitionData E W := ⟨6,![cycle433_0,cycle433_1,cycle433_2,cycle433_3,cycle433_4,cycle433_5]⟩
lemma valid_data433 : data433.Valid src433 dst433 Finset.univ := by decide +kernel

def src434 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst434 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle434_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle434_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle434_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle434_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle434_4 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,27]⟩
def cycle434_5 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def data434 : PartitionData E W := ⟨6,![cycle434_0,cycle434_1,cycle434_2,cycle434_3,cycle434_4,cycle434_5]⟩
lemma valid_data434 : data434.Valid src434 dst434 Finset.univ := by decide +kernel

def src435 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst435 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle435_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle435_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle435_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle435_3 : CycleData E W := ⟨2,![7,21,13,12],![14,18,28,27]⟩
def cycle435_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle435_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data435 : PartitionData E W := ⟨6,![cycle435_0,cycle435_1,cycle435_2,cycle435_3,cycle435_4,cycle435_5]⟩
lemma valid_data435 : data435.Valid src435 dst435 Finset.univ := by decide +kernel

def src436 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst436 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle436_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle436_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle436_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle436_3 : CycleData E W := ⟨3,![20,7,12,13,23],![8,18,14,27,28]⟩
def cycle436_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle436_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data436 : PartitionData E W := ⟨6,![cycle436_0,cycle436_1,cycle436_2,cycle436_3,cycle436_4,cycle436_5]⟩
lemma valid_data436 : data436.Valid src436 dst436 Finset.univ := by decide +kernel

def src437 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst437 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle437_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle437_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle437_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle437_3 : CycleData E W := ⟨2,![7,21,13,12],![14,18,28,27]⟩
def cycle437_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle437_5 : CycleData E W := ⟨3,![10,16,23,20,14],![4,26,38,8,28]⟩
def data437 : PartitionData E W := ⟨6,![cycle437_0,cycle437_1,cycle437_2,cycle437_3,cycle437_4,cycle437_5]⟩
lemma valid_data437 : data437.Valid src437 dst437 Finset.univ := by decide +kernel

def src438 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst438 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle438_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle438_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,27,14]⟩
def cycle438_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle438_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle438_4 : CycleData E W := ⟨3,![10,11,7,21,14],![4,26,14,18,28]⟩
def cycle438_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data438 : PartitionData E W := ⟨6,![cycle438_0,cycle438_1,cycle438_2,cycle438_3,cycle438_4,cycle438_5]⟩
lemma valid_data438 : data438.Valid src438 dst438 Finset.univ := by decide +kernel

def src439 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst439 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle439_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle439_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,27,14]⟩
def cycle439_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle439_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle439_4 : CycleData E W := ⟨2,![7,8,17,11],![14,18,16,26]⟩
def cycle439_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data439 : PartitionData E W := ⟨6,![cycle439_0,cycle439_1,cycle439_2,cycle439_3,cycle439_4,cycle439_5]⟩
lemma valid_data439 : data439.Valid src439 dst439 Finset.univ := by decide +kernel

def src440 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst440 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle440_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle440_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,27,14]⟩
def cycle440_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle440_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle440_4 : CycleData E W := ⟨2,![7,8,17,11],![14,18,16,26]⟩
def cycle440_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def data440 : PartitionData E W := ⟨6,![cycle440_0,cycle440_1,cycle440_2,cycle440_3,cycle440_4,cycle440_5]⟩
lemma valid_data440 : data440.Valid src440 dst440 Finset.univ := by decide +kernel

def src441 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst441 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle441_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle441_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle441_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle441_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle441_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle441_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle441_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data441 : PartitionData E W := ⟨7,![cycle441_0,cycle441_1,cycle441_2,cycle441_3,cycle441_4,cycle441_5,cycle441_6]⟩
lemma valid_data441 : data441.Valid src441 dst441 Finset.univ := by decide +kernel

def src442 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst442 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle442_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle442_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle442_2 : CycleData E W := ⟨4,![4,3,19,21,8,9],![2,8,6,38,18,16]⟩
def cycle442_3 : CycleData E W := ⟨2,![20,7,12,23],![8,18,14,28]⟩
def cycle442_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle442_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data442 : PartitionData E W := ⟨6,![cycle442_0,cycle442_1,cycle442_2,cycle442_3,cycle442_4,cycle442_5]⟩
lemma valid_data442 : data442.Valid src442 dst442 Finset.univ := by decide +kernel

def src443 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst443 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle443_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle443_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle443_2 : CycleData E W := ⟨3,![3,20,13,18,19],![6,8,28,27,38]⟩
def cycle443_3 : CycleData E W := ⟨3,![4,23,22,8,9],![2,8,38,18,16]⟩
def cycle443_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle443_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data443 : PartitionData E W := ⟨6,![cycle443_0,cycle443_1,cycle443_2,cycle443_3,cycle443_4,cycle443_5]⟩
lemma valid_data443 : data443.Valid src443 dst443 Finset.univ := by decide +kernel

def src444 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst444 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle444_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle444_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle444_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle444_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle444_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle444_5 : CycleData E W := ⟨3,![10,16,22,13,14],![4,26,38,28,27]⟩
def data444 : PartitionData E W := ⟨6,![cycle444_0,cycle444_1,cycle444_2,cycle444_3,cycle444_4,cycle444_5]⟩
lemma valid_data444 : data444.Valid src444 dst444 Finset.univ := by decide +kernel

def src445 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst445 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle445_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle445_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle445_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle445_3 : CycleData E W := ⟨2,![20,7,12,23],![8,18,14,28]⟩
def cycle445_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle445_5 : CycleData E W := ⟨3,![10,16,22,13,14],![4,26,38,28,27]⟩
def data445 : PartitionData E W := ⟨6,![cycle445_0,cycle445_1,cycle445_2,cycle445_3,cycle445_4,cycle445_5]⟩
lemma valid_data445 : data445.Valid src445 dst445 Finset.univ := by decide +kernel

def src446 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst446 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle446_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle446_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle446_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle446_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle446_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle446_5 : CycleData E W := ⟨4,![10,16,23,20,13,14],![4,26,38,8,28,27]⟩
def data446 : PartitionData E W := ⟨6,![cycle446_0,cycle446_1,cycle446_2,cycle446_3,cycle446_4,cycle446_5]⟩
lemma valid_data446 : data446.Valid src446 dst446 Finset.univ := by decide +kernel

def src447 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst447 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle447_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle447_1 : CycleData E W := ⟨3,![2,15,13,12,6],![3,6,27,28,14]⟩
def cycle447_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle447_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle447_4 : CycleData E W := ⟨3,![7,21,22,18,11],![14,18,28,38,26]⟩
def cycle447_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data447 : PartitionData E W := ⟨6,![cycle447_0,cycle447_1,cycle447_2,cycle447_3,cycle447_4,cycle447_5]⟩
lemma valid_data447 : data447.Valid src447 dst447 Finset.univ := by decide +kernel

def src448 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst448 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle448_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle448_1 : CycleData E W := ⟨3,![2,15,13,12,6],![3,6,27,28,14]⟩
def cycle448_2 : CycleData E W := ⟨2,![3,23,22,19],![6,8,28,38]⟩
def cycle448_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle448_4 : CycleData E W := ⟨2,![7,21,18,11],![14,18,38,26]⟩
def cycle448_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data448 : PartitionData E W := ⟨6,![cycle448_0,cycle448_1,cycle448_2,cycle448_3,cycle448_4,cycle448_5]⟩
lemma valid_data448 : data448.Valid src448 dst448 Finset.univ := by decide +kernel

def src449 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst449 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle449_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle449_1 : CycleData E W := ⟨3,![2,15,13,12,6],![3,6,27,28,14]⟩
def cycle449_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle449_3 : CycleData E W := ⟨3,![4,20,21,8,9],![2,8,28,18,16]⟩
def cycle449_4 : CycleData E W := ⟨2,![7,22,18,11],![14,18,38,26]⟩
def cycle449_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data449 : PartitionData E W := ⟨6,![cycle449_0,cycle449_1,cycle449_2,cycle449_3,cycle449_4,cycle449_5]⟩
lemma valid_data449 : data449.Valid src449 dst449 Finset.univ := by decide +kernel

def src450 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst450 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle450_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle450_1 : CycleData E W := ⟨3,![2,15,11,12,6],![3,6,26,28,14]⟩
def cycle450_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle450_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle450_4 : CycleData E W := ⟨3,![7,21,22,18,13],![14,18,28,38,27]⟩
def cycle450_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data450 : PartitionData E W := ⟨6,![cycle450_0,cycle450_1,cycle450_2,cycle450_3,cycle450_4,cycle450_5]⟩
lemma valid_data450 : data450.Valid src450 dst450 Finset.univ := by decide +kernel

def src451 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst451 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle451_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle451_1 : CycleData E W := ⟨3,![2,15,11,12,6],![3,6,26,28,14]⟩
def cycle451_2 : CycleData E W := ⟨2,![3,23,22,19],![6,8,28,38]⟩
def cycle451_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle451_4 : CycleData E W := ⟨2,![7,21,18,13],![14,18,38,27]⟩
def cycle451_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data451 : PartitionData E W := ⟨6,![cycle451_0,cycle451_1,cycle451_2,cycle451_3,cycle451_4,cycle451_5]⟩
lemma valid_data451 : data451.Valid src451 dst451 Finset.univ := by decide +kernel

def src452 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst452 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle452_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle452_1 : CycleData E W := ⟨3,![2,15,11,12,6],![3,6,26,28,14]⟩
def cycle452_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle452_3 : CycleData E W := ⟨3,![4,20,21,8,9],![2,8,28,18,16]⟩
def cycle452_4 : CycleData E W := ⟨2,![7,22,18,13],![14,18,38,27]⟩
def cycle452_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data452 : PartitionData E W := ⟨6,![cycle452_0,cycle452_1,cycle452_2,cycle452_3,cycle452_4,cycle452_5]⟩
lemma valid_data452 : data452.Valid src452 dst452 Finset.univ := by decide +kernel

def src453 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst453 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle453_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle453_1 : CycleData E W := ⟨4,![2,15,10,14,13,6],![3,6,26,4,27,14]⟩
def cycle453_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle453_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle453_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle453_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data453 : PartitionData E W := ⟨6,![cycle453_0,cycle453_1,cycle453_2,cycle453_3,cycle453_4,cycle453_5]⟩
lemma valid_data453 : data453.Valid src453 dst453 Finset.univ := by decide +kernel

def src454 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst454 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle454_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle454_1 : CycleData E W := ⟨2,![2,19,13,6],![3,6,27,14]⟩
def cycle454_2 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle454_3 : CycleData E W := ⟨2,![20,7,12,23],![8,18,14,28]⟩
def cycle454_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle454_5 : CycleData E W := ⟨3,![10,11,22,18,14],![4,26,28,38,27]⟩
def data454 : PartitionData E W := ⟨6,![cycle454_0,cycle454_1,cycle454_2,cycle454_3,cycle454_4,cycle454_5]⟩
lemma valid_data454 : data454.Valid src454 dst454 Finset.univ := by decide +kernel

def src455 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst455 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle455_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle455_1 : CycleData E W := ⟨4,![2,15,10,14,13,6],![3,6,26,4,27,14]⟩
def cycle455_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle455_3 : CycleData E W := ⟨3,![4,20,11,16,9],![2,8,28,26,16]⟩
def cycle455_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle455_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data455 : PartitionData E W := ⟨6,![cycle455_0,cycle455_1,cycle455_2,cycle455_3,cycle455_4,cycle455_5]⟩
lemma valid_data455 : data455.Valid src455 dst455 Finset.univ := by decide +kernel

def src456 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst456 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle456_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle456_1 : CycleData E W := ⟨2,![2,15,13,6],![3,6,27,14]⟩
def cycle456_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle456_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle456_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle456_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle456_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data456 : PartitionData E W := ⟨7,![cycle456_0,cycle456_1,cycle456_2,cycle456_3,cycle456_4,cycle456_5,cycle456_6]⟩
lemma valid_data456 : data456.Valid src456 dst456 Finset.univ := by decide +kernel

def src457 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst457 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle457_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle457_1 : CycleData E W := ⟨2,![2,15,13,6],![3,6,27,14]⟩
def cycle457_2 : CycleData E W := ⟨4,![4,3,19,21,8,9],![2,8,6,38,18,16]⟩
def cycle457_3 : CycleData E W := ⟨2,![20,7,12,23],![8,18,14,28]⟩
def cycle457_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle457_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data457 : PartitionData E W := ⟨6,![cycle457_0,cycle457_1,cycle457_2,cycle457_3,cycle457_4,cycle457_5]⟩
lemma valid_data457 : data457.Valid src457 dst457 Finset.univ := by decide +kernel

def src458 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst458 : E → W := ![4,3,6,8,2,3,14,18,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle458_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle458_1 : CycleData E W := ⟨2,![2,15,13,6],![3,6,27,14]⟩
def cycle458_2 : CycleData E W := ⟨3,![3,20,11,18,19],![6,8,28,26,38]⟩
def cycle458_3 : CycleData E W := ⟨3,![4,23,22,8,9],![2,8,38,18,16]⟩
def cycle458_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle458_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data458 : PartitionData E W := ⟨6,![cycle458_0,cycle458_1,cycle458_2,cycle458_3,cycle458_4,cycle458_5]⟩
lemma valid_data458 : data458.Valid src458 dst458 Finset.univ := by decide +kernel

def src459 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst459 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle459_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle459_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle459_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle459_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle459_4 : CycleData E W := ⟨3,![10,11,7,21,14],![4,27,14,18,28]⟩
def cycle459_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data459 : PartitionData E W := ⟨6,![cycle459_0,cycle459_1,cycle459_2,cycle459_3,cycle459_4,cycle459_5]⟩
lemma valid_data459 : data459.Valid src459 dst459 Finset.univ := by decide +kernel

def src460 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst460 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle460_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle460_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle460_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle460_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle460_4 : CycleData E W := ⟨2,![7,8,17,11],![14,18,16,27]⟩
def cycle460_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data460 : PartitionData E W := ⟨6,![cycle460_0,cycle460_1,cycle460_2,cycle460_3,cycle460_4,cycle460_5]⟩
lemma valid_data460 : data460.Valid src460 dst460 Finset.univ := by decide +kernel

def src461 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst461 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle461_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle461_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle461_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle461_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle461_4 : CycleData E W := ⟨2,![7,8,17,11],![14,18,16,27]⟩
def cycle461_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data461 : PartitionData E W := ⟨6,![cycle461_0,cycle461_1,cycle461_2,cycle461_3,cycle461_4,cycle461_5]⟩
lemma valid_data461 : data461.Valid src461 dst461 Finset.univ := by decide +kernel

def src462 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst462 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle462_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle462_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle462_2 : CycleData E W := ⟨3,![3,20,7,11,19],![6,8,18,14,27]⟩
def cycle462_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle462_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle462_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data462 : PartitionData E W := ⟨6,![cycle462_0,cycle462_1,cycle462_2,cycle462_3,cycle462_4,cycle462_5]⟩
lemma valid_data462 : data462.Valid src462 dst462 Finset.univ := by decide +kernel

def src463 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst463 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle463_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle463_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle463_2 : CycleData E W := ⟨3,![3,20,7,11,19],![6,8,18,14,27]⟩
def cycle463_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle463_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle463_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data463 : PartitionData E W := ⟨6,![cycle463_0,cycle463_1,cycle463_2,cycle463_3,cycle463_4,cycle463_5]⟩
lemma valid_data463 : data463.Valid src463 dst463 Finset.univ := by decide +kernel

def src464 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst464 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle464_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle464_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle464_2 : CycleData E W := ⟨3,![10,19,3,20,14],![4,27,6,8,28]⟩
def cycle464_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle464_4 : CycleData E W := ⟨2,![7,22,18,11],![14,18,38,27]⟩
def cycle464_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data464 : PartitionData E W := ⟨6,![cycle464_0,cycle464_1,cycle464_2,cycle464_3,cycle464_4,cycle464_5]⟩
lemma valid_data464 : data464.Valid src464 dst464 Finset.univ := by decide +kernel

def src465 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst465 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle465_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle465_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle465_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle465_3 : CycleData E W := ⟨3,![10,11,7,21,14],![4,27,14,18,28]⟩
def cycle465_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle465_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data465 : PartitionData E W := ⟨6,![cycle465_0,cycle465_1,cycle465_2,cycle465_3,cycle465_4,cycle465_5]⟩
lemma valid_data465 : data465.Valid src465 dst465 Finset.univ := by decide +kernel

def src466 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst466 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle466_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle466_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle466_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle466_3 : CycleData E W := ⟨4,![10,11,7,20,23,14],![4,27,14,18,8,28]⟩
def cycle466_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle466_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data466 : PartitionData E W := ⟨6,![cycle466_0,cycle466_1,cycle466_2,cycle466_3,cycle466_4,cycle466_5]⟩
lemma valid_data466 : data466.Valid src466 dst466 Finset.univ := by decide +kernel

def src467 : E → W := ![2,4,3,6,8,2,3,14,18,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst467 : E → W := ![4,3,6,8,2,3,14,18,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle467_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle467_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle467_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle467_3 : CycleData E W := ⟨3,![10,11,7,21,14],![4,27,14,18,28]⟩
def cycle467_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle467_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data467 : PartitionData E W := ⟨6,![cycle467_0,cycle467_1,cycle467_2,cycle467_3,cycle467_4,cycle467_5]⟩
lemma valid_data467 : data467.Valid src467 dst467 Finset.univ := by decide +kernel

def src468 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst468 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle468_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle468_1 : CycleData E W := ⟨3,![2,19,12,7,6],![3,6,27,14,18]⟩
def cycle468_2 : CycleData E W := ⟨4,![10,15,3,20,21,14],![4,26,6,8,18,28]⟩
def cycle468_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle468_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle468_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data468 : PartitionData E W := ⟨6,![cycle468_0,cycle468_1,cycle468_2,cycle468_3,cycle468_4,cycle468_5]⟩
lemma valid_data468 : data468.Valid src468 dst468 Finset.univ := by decide +kernel

def src469 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst469 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle469_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle469_1 : CycleData E W := ⟨3,![2,19,12,7,6],![3,6,27,14,18]⟩
def cycle469_2 : CycleData E W := ⟨3,![10,15,3,23,14],![4,26,6,8,28]⟩
def cycle469_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle469_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle469_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data469 : PartitionData E W := ⟨6,![cycle469_0,cycle469_1,cycle469_2,cycle469_3,cycle469_4,cycle469_5]⟩
lemma valid_data469 : data469.Valid src469 dst469 Finset.univ := by decide +kernel

def src470 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst470 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle470_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle470_1 : CycleData E W := ⟨3,![2,19,12,7,6],![3,6,27,14,18]⟩
def cycle470_2 : CycleData E W := ⟨3,![10,15,3,20,14],![4,26,6,8,28]⟩
def cycle470_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle470_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle470_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data470 : PartitionData E W := ⟨6,![cycle470_0,cycle470_1,cycle470_2,cycle470_3,cycle470_4,cycle470_5]⟩
lemma valid_data470 : data470.Valid src470 dst470 Finset.univ := by decide +kernel

def src471 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst471 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle471_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle471_1 : CycleData E W := ⟨3,![2,15,11,7,6],![3,6,26,14,18]⟩
def cycle471_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle471_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle471_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle471_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data471 : PartitionData E W := ⟨6,![cycle471_0,cycle471_1,cycle471_2,cycle471_3,cycle471_4,cycle471_5]⟩
lemma valid_data471 : data471.Valid src471 dst471 Finset.univ := by decide +kernel

def src472 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst472 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle472_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle472_1 : CycleData E W := ⟨3,![2,15,11,7,6],![3,6,26,14,18]⟩
def cycle472_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle472_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle472_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle472_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data472 : PartitionData E W := ⟨6,![cycle472_0,cycle472_1,cycle472_2,cycle472_3,cycle472_4,cycle472_5]⟩
lemma valid_data472 : data472.Valid src472 dst472 Finset.univ := by decide +kernel

def src473 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst473 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle473_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle473_1 : CycleData E W := ⟨3,![2,15,11,7,6],![3,6,26,14,18]⟩
def cycle473_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle473_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle473_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle473_5 : CycleData E W := ⟨3,![10,16,22,21,14],![4,26,38,18,28]⟩
def data473 : PartitionData E W := ⟨6,![cycle473_0,cycle473_1,cycle473_2,cycle473_3,cycle473_4,cycle473_5]⟩
lemma valid_data473 : data473.Valid src473 dst473 Finset.univ := by decide +kernel

def src474 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst474 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle474_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle474_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,27,14,18]⟩
def cycle474_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle474_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,27,16]⟩
def cycle474_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle474_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data474 : PartitionData E W := ⟨6,![cycle474_0,cycle474_1,cycle474_2,cycle474_3,cycle474_4,cycle474_5]⟩
lemma valid_data474 : data474.Valid src474 dst474 Finset.univ := by decide +kernel

def src475 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst475 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle475_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle475_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,27,14,18]⟩
def cycle475_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle475_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle475_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle475_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data475 : PartitionData E W := ⟨6,![cycle475_0,cycle475_1,cycle475_2,cycle475_3,cycle475_4,cycle475_5]⟩
lemma valid_data475 : data475.Valid src475 dst475 Finset.univ := by decide +kernel

def src476 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst476 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle476_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle476_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,27,14,18]⟩
def cycle476_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle476_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle476_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle476_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def data476 : PartitionData E W := ⟨6,![cycle476_0,cycle476_1,cycle476_2,cycle476_3,cycle476_4,cycle476_5]⟩
lemma valid_data476 : data476.Valid src476 dst476 Finset.univ := by decide +kernel

def src477 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst477 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle477_0 : CycleData E W := ⟨2,![0,14,17,9],![2,4,27,16]⟩
def cycle477_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle477_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle477_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,3]⟩
def cycle477_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle477_5 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle477_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data477 : PartitionData E W := ⟨7,![cycle477_0,cycle477_1,cycle477_2,cycle477_3,cycle477_4,cycle477_5,cycle477_6]⟩
lemma valid_data477 : data477.Valid src477 dst477 Finset.univ := by decide +kernel

def src478 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst478 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle478_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle478_1 : CycleData E W := ⟨3,![2,15,11,7,6],![3,6,26,14,18]⟩
def cycle478_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle478_3 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle478_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle478_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data478 : PartitionData E W := ⟨6,![cycle478_0,cycle478_1,cycle478_2,cycle478_3,cycle478_4,cycle478_5]⟩
lemma valid_data478 : data478.Valid src478 dst478 Finset.univ := by decide +kernel

def src479 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst479 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle479_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle479_1 : CycleData E W := ⟨3,![2,15,11,7,6],![3,6,26,14,18]⟩
def cycle479_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle479_3 : CycleData E W := ⟨3,![4,20,12,8,9],![2,8,28,14,16]⟩
def cycle479_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle479_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data479 : PartitionData E W := ⟨6,![cycle479_0,cycle479_1,cycle479_2,cycle479_3,cycle479_4,cycle479_5]⟩
lemma valid_data479 : data479.Valid src479 dst479 Finset.univ := by decide +kernel

def src480 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst480 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle480_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle480_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle480_2 : CycleData E W := ⟨4,![4,23,16,11,8,9],![2,8,38,26,14,16]⟩
def cycle480_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle480_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle480_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data480 : PartitionData E W := ⟨6,![cycle480_0,cycle480_1,cycle480_2,cycle480_3,cycle480_4,cycle480_5]⟩
lemma valid_data480 : data480.Valid src480 dst480 Finset.univ := by decide +kernel

def src481 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst481 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle481_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle481_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle481_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle481_3 : CycleData E W := ⟨2,![7,21,16,11],![14,18,38,26]⟩
def cycle481_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle481_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data481 : PartitionData E W := ⟨6,![cycle481_0,cycle481_1,cycle481_2,cycle481_3,cycle481_4,cycle481_5]⟩
lemma valid_data481 : data481.Valid src481 dst481 Finset.univ := by decide +kernel

def src482 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst482 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle482_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle482_1 : CycleData E W := ⟨3,![2,3,20,21,6],![3,6,8,28,18]⟩
def cycle482_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle482_3 : CycleData E W := ⟨2,![7,22,16,11],![14,18,38,26]⟩
def cycle482_4 : CycleData E W := ⟨2,![8,18,13,12],![14,16,27,28]⟩
def cycle482_5 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def data482 : PartitionData E W := ⟨6,![cycle482_0,cycle482_1,cycle482_2,cycle482_3,cycle482_4,cycle482_5]⟩
lemma valid_data482 : data482.Valid src482 dst482 Finset.univ := by decide +kernel

def src483 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst483 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle483_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle483_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle483_2 : CycleData E W := ⟨4,![4,23,18,11,8,9],![2,8,38,26,14,16]⟩
def cycle483_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle483_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle483_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data483 : PartitionData E W := ⟨6,![cycle483_0,cycle483_1,cycle483_2,cycle483_3,cycle483_4,cycle483_5]⟩
lemma valid_data483 : data483.Valid src483 dst483 Finset.univ := by decide +kernel

def src484 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst484 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle484_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle484_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle484_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle484_3 : CycleData E W := ⟨2,![7,21,18,11],![14,18,38,26]⟩
def cycle484_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle484_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data484 : PartitionData E W := ⟨6,![cycle484_0,cycle484_1,cycle484_2,cycle484_3,cycle484_4,cycle484_5]⟩
lemma valid_data484 : data484.Valid src484 dst484 Finset.univ := by decide +kernel

def src485 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst485 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle485_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle485_1 : CycleData E W := ⟨3,![2,15,13,21,6],![3,6,27,28,18]⟩
def cycle485_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle485_3 : CycleData E W := ⟨3,![4,20,12,8,9],![2,8,28,14,16]⟩
def cycle485_4 : CycleData E W := ⟨2,![7,22,18,11],![14,18,38,26]⟩
def cycle485_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data485 : PartitionData E W := ⟨6,![cycle485_0,cycle485_1,cycle485_2,cycle485_3,cycle485_4,cycle485_5]⟩
lemma valid_data485 : data485.Valid src485 dst485 Finset.univ := by decide +kernel

def src486 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst486 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle486_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle486_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle486_2 : CycleData E W := ⟨4,![4,23,18,13,8,9],![2,8,38,27,14,16]⟩
def cycle486_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle486_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle486_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data486 : PartitionData E W := ⟨6,![cycle486_0,cycle486_1,cycle486_2,cycle486_3,cycle486_4,cycle486_5]⟩
lemma valid_data486 : data486.Valid src486 dst486 Finset.univ := by decide +kernel

def src487 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst487 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle487_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle487_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle487_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle487_3 : CycleData E W := ⟨2,![7,21,18,13],![14,18,38,27]⟩
def cycle487_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle487_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data487 : PartitionData E W := ⟨6,![cycle487_0,cycle487_1,cycle487_2,cycle487_3,cycle487_4,cycle487_5]⟩
lemma valid_data487 : data487.Valid src487 dst487 Finset.univ := by decide +kernel

def src488 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst488 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle488_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle488_1 : CycleData E W := ⟨3,![2,15,11,21,6],![3,6,26,28,18]⟩
def cycle488_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle488_3 : CycleData E W := ⟨3,![4,20,12,8,9],![2,8,28,14,16]⟩
def cycle488_4 : CycleData E W := ⟨2,![7,22,18,13],![14,18,38,27]⟩
def cycle488_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data488 : PartitionData E W := ⟨6,![cycle488_0,cycle488_1,cycle488_2,cycle488_3,cycle488_4,cycle488_5]⟩
lemma valid_data488 : data488.Valid src488 dst488 Finset.univ := by decide +kernel

def src489 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst489 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle489_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle489_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle489_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle489_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle489_4 : CycleData E W := ⟨3,![10,16,8,13,14],![4,26,16,14,27]⟩
def cycle489_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data489 : PartitionData E W := ⟨6,![cycle489_0,cycle489_1,cycle489_2,cycle489_3,cycle489_4,cycle489_5]⟩
lemma valid_data489 : data489.Valid src489 dst489 Finset.univ := by decide +kernel

def src490 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst490 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle490_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle490_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle490_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle490_3 : CycleData E W := ⟨2,![7,21,18,13],![14,18,38,27]⟩
def cycle490_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle490_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data490 : PartitionData E W := ⟨6,![cycle490_0,cycle490_1,cycle490_2,cycle490_3,cycle490_4,cycle490_5]⟩
lemma valid_data490 : data490.Valid src490 dst490 Finset.univ := by decide +kernel

def src491 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst491 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle491_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle491_1 : CycleData E W := ⟨3,![2,3,20,21,6],![3,6,8,28,18]⟩
def cycle491_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle491_3 : CycleData E W := ⟨2,![7,22,18,13],![14,18,38,27]⟩
def cycle491_4 : CycleData E W := ⟨2,![8,16,11,12],![14,16,26,28]⟩
def cycle491_5 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def data491 : PartitionData E W := ⟨6,![cycle491_0,cycle491_1,cycle491_2,cycle491_3,cycle491_4,cycle491_5]⟩
lemma valid_data491 : data491.Valid src491 dst491 Finset.univ := by decide +kernel

def src492 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst492 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle492_0 : CycleData E W := ⟨2,![0,10,17,9],![2,4,26,16]⟩
def cycle492_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,27,6]⟩
def cycle492_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle492_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,3]⟩
def cycle492_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle492_5 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def cycle492_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data492 : PartitionData E W := ⟨7,![cycle492_0,cycle492_1,cycle492_2,cycle492_3,cycle492_4,cycle492_5,cycle492_6]⟩
lemma valid_data492 : data492.Valid src492 dst492 Finset.univ := by decide +kernel

def src493 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst493 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle493_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle493_1 : CycleData E W := ⟨3,![2,15,13,7,6],![3,6,27,14,18]⟩
def cycle493_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle493_3 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle493_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle493_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data493 : PartitionData E W := ⟨6,![cycle493_0,cycle493_1,cycle493_2,cycle493_3,cycle493_4,cycle493_5]⟩
lemma valid_data493 : data493.Valid src493 dst493 Finset.univ := by decide +kernel

def src494 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst494 : E → W := ![4,3,6,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle494_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle494_1 : CycleData E W := ⟨3,![2,15,13,7,6],![3,6,27,14,18]⟩
def cycle494_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle494_3 : CycleData E W := ⟨3,![4,20,12,8,9],![2,8,28,14,16]⟩
def cycle494_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle494_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data494 : PartitionData E W := ⟨6,![cycle494_0,cycle494_1,cycle494_2,cycle494_3,cycle494_4,cycle494_5]⟩
lemma valid_data494 : data494.Valid src494 dst494 Finset.univ := by decide +kernel

def src495 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst495 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle495_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle495_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle495_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle495_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,26,16]⟩
def cycle495_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle495_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data495 : PartitionData E W := ⟨6,![cycle495_0,cycle495_1,cycle495_2,cycle495_3,cycle495_4,cycle495_5]⟩
lemma valid_data495 : data495.Valid src495 dst495 Finset.univ := by decide +kernel

def src496 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst496 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle496_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle496_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle496_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle496_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle496_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle496_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data496 : PartitionData E W := ⟨6,![cycle496_0,cycle496_1,cycle496_2,cycle496_3,cycle496_4,cycle496_5]⟩
lemma valid_data496 : data496.Valid src496 dst496 Finset.univ := by decide +kernel

def src497 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst497 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle497_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle497_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle497_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle497_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle497_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle497_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data497 : PartitionData E W := ⟨6,![cycle497_0,cycle497_1,cycle497_2,cycle497_3,cycle497_4,cycle497_5]⟩
lemma valid_data497 : data497.Valid src497 dst497 Finset.univ := by decide +kernel

def src498 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst498 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle498_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle498_1 : CycleData E W := ⟨3,![2,19,11,7,6],![3,6,27,14,18]⟩
def cycle498_2 : CycleData E W := ⟨3,![3,20,21,13,15],![6,8,18,28,26]⟩
def cycle498_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle498_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle498_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data498 : PartitionData E W := ⟨6,![cycle498_0,cycle498_1,cycle498_2,cycle498_3,cycle498_4,cycle498_5]⟩
lemma valid_data498 : data498.Valid src498 dst498 Finset.univ := by decide +kernel

def src499 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst499 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle499_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle499_1 : CycleData E W := ⟨3,![2,19,11,7,6],![3,6,27,14,18]⟩
def cycle499_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle499_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle499_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle499_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data499 : PartitionData E W := ⟨6,![cycle499_0,cycle499_1,cycle499_2,cycle499_3,cycle499_4,cycle499_5]⟩
lemma valid_data499 : data499.Valid src499 dst499 Finset.univ := by decide +kernel

def src500 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst500 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle500_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle500_1 : CycleData E W := ⟨3,![2,19,11,7,6],![3,6,27,14,18]⟩
def cycle500_2 : CycleData E W := ⟨2,![3,20,13,15],![6,8,28,26]⟩
def cycle500_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle500_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle500_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data500 : PartitionData E W := ⟨6,![cycle500_0,cycle500_1,cycle500_2,cycle500_3,cycle500_4,cycle500_5]⟩
lemma valid_data500 : data500.Valid src500 dst500 Finset.univ := by decide +kernel

def src501 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst501 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle501_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle501_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle501_2 : CycleData E W := ⟨4,![10,19,3,20,21,14],![4,27,6,8,18,28]⟩
def cycle501_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle501_4 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle501_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data501 : PartitionData E W := ⟨6,![cycle501_0,cycle501_1,cycle501_2,cycle501_3,cycle501_4,cycle501_5]⟩
lemma valid_data501 : data501.Valid src501 dst501 Finset.univ := by decide +kernel

def src502 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst502 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle502_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle502_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle502_2 : CycleData E W := ⟨3,![10,19,3,23,14],![4,27,6,8,28]⟩
def cycle502_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle502_4 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle502_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data502 : PartitionData E W := ⟨6,![cycle502_0,cycle502_1,cycle502_2,cycle502_3,cycle502_4,cycle502_5]⟩
lemma valid_data502 : data502.Valid src502 dst502 Finset.univ := by decide +kernel

def src503 : E → W := ![2,4,3,6,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst503 : E → W := ![4,3,6,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle503_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle503_1 : CycleData E W := ⟨3,![2,15,12,7,6],![3,6,26,14,18]⟩
def cycle503_2 : CycleData E W := ⟨3,![10,19,3,20,14],![4,27,6,8,28]⟩
def cycle503_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle503_4 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle503_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data503 : PartitionData E W := ⟨6,![cycle503_0,cycle503_1,cycle503_2,cycle503_3,cycle503_4,cycle503_5]⟩
lemma valid_data503 : data503.Valid src503 dst503 Finset.univ := by decide +kernel

def src504 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst504 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle504_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle504_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle504_2 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle504_3 : CycleData E W := ⟨3,![10,16,7,21,14],![4,26,16,18,28]⟩
def cycle504_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle504_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data504 : PartitionData E W := ⟨6,![cycle504_0,cycle504_1,cycle504_2,cycle504_3,cycle504_4,cycle504_5]⟩
lemma valid_data504 : data504.Valid src504 dst504 Finset.univ := by decide +kernel

def src505 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst505 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle505_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle505_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle505_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,27,14]⟩
def cycle505_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle505_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle505_5 : CycleData E W := ⟨4,![10,15,19,18,22,14],![4,26,6,27,38,28]⟩
def data505 : PartitionData E W := ⟨6,![cycle505_0,cycle505_1,cycle505_2,cycle505_3,cycle505_4,cycle505_5]⟩
lemma valid_data505 : data505.Valid src505 dst505 Finset.univ := by decide +kernel

def src506 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst506 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle506_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle506_1 : CycleData E W := ⟨4,![2,15,10,14,21,6],![3,6,26,4,28,18]⟩
def cycle506_2 : CycleData E W := ⟨3,![4,3,19,12,9],![2,8,6,27,14]⟩
def cycle506_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle506_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle506_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data506 : PartitionData E W := ⟨6,![cycle506_0,cycle506_1,cycle506_2,cycle506_3,cycle506_4,cycle506_5]⟩
lemma valid_data506 : data506.Valid src506 dst506 Finset.univ := by decide +kernel

def src507 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst507 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle507_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle507_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle507_2 : CycleData E W := ⟨3,![4,23,16,11,9],![2,8,38,26,14]⟩
def cycle507_3 : CycleData E W := ⟨2,![7,21,22,17],![16,18,28,38]⟩
def cycle507_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle507_5 : CycleData E W := ⟨3,![10,15,19,13,14],![4,26,6,27,28]⟩
def data507 : PartitionData E W := ⟨6,![cycle507_0,cycle507_1,cycle507_2,cycle507_3,cycle507_4,cycle507_5]⟩
lemma valid_data507 : data507.Valid src507 dst507 Finset.univ := by decide +kernel

def src508 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst508 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle508_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle508_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle508_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,27,14]⟩
def cycle508_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle508_4 : CycleData E W := ⟨3,![15,11,8,18,19],![6,26,14,16,27]⟩
def cycle508_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data508 : PartitionData E W := ⟨6,![cycle508_0,cycle508_1,cycle508_2,cycle508_3,cycle508_4,cycle508_5]⟩
lemma valid_data508 : data508.Valid src508 dst508 Finset.univ := by decide +kernel

def src509 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst509 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle509_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle509_1 : CycleData E W := ⟨4,![2,15,10,14,21,6],![3,6,26,4,28,18]⟩
def cycle509_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle509_3 : CycleData E W := ⟨3,![4,23,16,11,9],![2,8,38,26,14]⟩
def cycle509_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle509_5 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def data509 : PartitionData E W := ⟨6,![cycle509_0,cycle509_1,cycle509_2,cycle509_3,cycle509_4,cycle509_5]⟩
lemma valid_data509 : data509.Valid src509 dst509 Finset.univ := by decide +kernel

def src510 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst510 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle510_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle510_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle510_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle510_3 : CycleData E W := ⟨4,![4,20,21,13,12,9],![2,8,18,28,27,14]⟩
def cycle510_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle510_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data510 : PartitionData E W := ⟨6,![cycle510_0,cycle510_1,cycle510_2,cycle510_3,cycle510_4,cycle510_5]⟩
lemma valid_data510 : data510.Valid src510 dst510 Finset.univ := by decide +kernel

def src511 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst511 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle511_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle511_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle511_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle511_3 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,27,14]⟩
def cycle511_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle511_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data511 : PartitionData E W := ⟨6,![cycle511_0,cycle511_1,cycle511_2,cycle511_3,cycle511_4,cycle511_5]⟩
lemma valid_data511 : data511.Valid src511 dst511 Finset.univ := by decide +kernel

def src512 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst512 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle512_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle512_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle512_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle512_3 : CycleData E W := ⟨3,![4,20,13,12,9],![2,8,28,27,14]⟩
def cycle512_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle512_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def data512 : PartitionData E W := ⟨6,![cycle512_0,cycle512_1,cycle512_2,cycle512_3,cycle512_4,cycle512_5]⟩
lemma valid_data512 : data512.Valid src512 dst512 Finset.univ := by decide +kernel

def src513 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst513 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle513_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle513_1 : CycleData E W := ⟨4,![2,15,11,8,7,6],![3,6,26,14,16,18]⟩
def cycle513_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle513_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle513_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle513_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data513 : PartitionData E W := ⟨6,![cycle513_0,cycle513_1,cycle513_2,cycle513_3,cycle513_4,cycle513_5]⟩
lemma valid_data513 : data513.Valid src513 dst513 Finset.univ := by decide +kernel

def src514 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst514 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle514_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle514_1 : CycleData E W := ⟨4,![2,15,11,8,7,6],![3,6,26,14,16,18]⟩
def cycle514_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle514_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle514_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle514_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data514 : PartitionData E W := ⟨6,![cycle514_0,cycle514_1,cycle514_2,cycle514_3,cycle514_4,cycle514_5]⟩
lemma valid_data514 : data514.Valid src514 dst514 Finset.univ := by decide +kernel

def src515 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst515 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle515_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle515_1 : CycleData E W := ⟨4,![2,15,11,8,7,6],![3,6,26,14,16,18]⟩
def cycle515_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle515_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle515_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle515_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data515 : PartitionData E W := ⟨6,![cycle515_0,cycle515_1,cycle515_2,cycle515_3,cycle515_4,cycle515_5]⟩
lemma valid_data515 : data515.Valid src515 dst515 Finset.univ := by decide +kernel

def src516 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst516 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle516_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle516_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle516_2 : CycleData E W := ⟨3,![4,23,16,11,9],![2,8,38,26,14]⟩
def cycle516_3 : CycleData E W := ⟨2,![8,7,21,12],![14,16,18,28]⟩
def cycle516_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle516_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data516 : PartitionData E W := ⟨6,![cycle516_0,cycle516_1,cycle516_2,cycle516_3,cycle516_4,cycle516_5]⟩
lemma valid_data516 : data516.Valid src516 dst516 Finset.univ := by decide +kernel

def src517 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst517 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle517_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle517_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle517_2 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle517_3 : CycleData E W := ⟨3,![8,7,21,16,11],![14,16,18,38,26]⟩
def cycle517_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle517_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data517 : PartitionData E W := ⟨6,![cycle517_0,cycle517_1,cycle517_2,cycle517_3,cycle517_4,cycle517_5]⟩
lemma valid_data517 : data517.Valid src517 dst517 Finset.univ := by decide +kernel

def src518 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst518 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle518_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle518_1 : CycleData E W := ⟨3,![2,19,13,21,6],![3,6,27,28,18]⟩
def cycle518_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle518_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle518_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle518_5 : CycleData E W := ⟨3,![10,11,8,18,14],![4,26,14,16,27]⟩
def data518 : PartitionData E W := ⟨6,![cycle518_0,cycle518_1,cycle518_2,cycle518_3,cycle518_4,cycle518_5]⟩
lemma valid_data518 : data518.Valid src518 dst518 Finset.univ := by decide +kernel

def src519 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst519 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle519_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle519_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle519_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle519_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle519_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle519_5 : CycleData E W := ⟨3,![10,18,22,13,14],![4,26,38,28,27]⟩
def data519 : PartitionData E W := ⟨6,![cycle519_0,cycle519_1,cycle519_2,cycle519_3,cycle519_4,cycle519_5]⟩
lemma valid_data519 : data519.Valid src519 dst519 Finset.univ := by decide +kernel

def src520 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst520 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle520_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle520_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle520_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle520_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle520_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle520_5 : CycleData E W := ⟨3,![10,18,22,13,14],![4,26,38,28,27]⟩
def data520 : PartitionData E W := ⟨6,![cycle520_0,cycle520_1,cycle520_2,cycle520_3,cycle520_4,cycle520_5]⟩
lemma valid_data520 : data520.Valid src520 dst520 Finset.univ := by decide +kernel

def src521 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst521 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle521_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle521_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,27,16,18]⟩
def cycle521_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle521_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle521_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle521_5 : CycleData E W := ⟨4,![10,18,22,21,13,14],![4,26,38,18,28,27]⟩
def data521 : PartitionData E W := ⟨6,![cycle521_0,cycle521_1,cycle521_2,cycle521_3,cycle521_4,cycle521_5]⟩
lemma valid_data521 : data521.Valid src521 dst521 Finset.univ := by decide +kernel

def src522 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst522 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle522_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle522_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle522_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle522_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle522_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle522_5 : CycleData E W := ⟨3,![10,11,22,18,14],![4,26,28,38,27]⟩
def data522 : PartitionData E W := ⟨6,![cycle522_0,cycle522_1,cycle522_2,cycle522_3,cycle522_4,cycle522_5]⟩
lemma valid_data522 : data522.Valid src522 dst522 Finset.univ := by decide +kernel

def src523 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst523 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle523_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle523_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle523_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle523_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle523_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle523_5 : CycleData E W := ⟨3,![10,11,22,18,14],![4,26,28,38,27]⟩
def data523 : PartitionData E W := ⟨6,![cycle523_0,cycle523_1,cycle523_2,cycle523_3,cycle523_4,cycle523_5]⟩
lemma valid_data523 : data523.Valid src523 dst523 Finset.univ := by decide +kernel

def src524 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst524 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle524_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle524_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle524_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle524_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle524_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle524_5 : CycleData E W := ⟨4,![10,11,21,22,18,14],![4,26,28,18,38,27]⟩
def data524 : PartitionData E W := ⟨6,![cycle524_0,cycle524_1,cycle524_2,cycle524_3,cycle524_4,cycle524_5]⟩
lemma valid_data524 : data524.Valid src524 dst524 Finset.univ := by decide +kernel

def src525 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst525 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle525_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle525_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle525_2 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle525_3 : CycleData E W := ⟨2,![7,21,11,16],![16,18,28,26]⟩
def cycle525_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle525_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data525 : PartitionData E W := ⟨6,![cycle525_0,cycle525_1,cycle525_2,cycle525_3,cycle525_4,cycle525_5]⟩
lemma valid_data525 : data525.Valid src525 dst525 Finset.univ := by decide +kernel

def src526 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst526 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle526_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle526_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle526_2 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle526_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle526_4 : CycleData E W := ⟨3,![10,16,8,13,14],![4,26,16,14,27]⟩
def cycle526_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data526 : PartitionData E W := ⟨6,![cycle526_0,cycle526_1,cycle526_2,cycle526_3,cycle526_4,cycle526_5]⟩
lemma valid_data526 : data526.Valid src526 dst526 Finset.univ := by decide +kernel

def src527 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst527 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle527_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle527_1 : CycleData E W := ⟨3,![2,15,11,21,6],![3,6,26,28,18]⟩
def cycle527_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle527_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle527_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle527_5 : CycleData E W := ⟨3,![10,16,8,13,14],![4,26,16,14,27]⟩
def data527 : PartitionData E W := ⟨6,![cycle527_0,cycle527_1,cycle527_2,cycle527_3,cycle527_4,cycle527_5]⟩
lemma valid_data527 : data527.Valid src527 dst527 Finset.univ := by decide +kernel

def src528 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst528 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle528_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle528_1 : CycleData E W := ⟨4,![2,15,13,8,7,6],![3,6,27,14,16,18]⟩
def cycle528_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle528_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle528_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle528_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data528 : PartitionData E W := ⟨6,![cycle528_0,cycle528_1,cycle528_2,cycle528_3,cycle528_4,cycle528_5]⟩
lemma valid_data528 : data528.Valid src528 dst528 Finset.univ := by decide +kernel

def src529 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst529 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle529_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle529_1 : CycleData E W := ⟨4,![2,15,13,8,7,6],![3,6,27,14,16,18]⟩
def cycle529_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle529_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle529_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle529_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data529 : PartitionData E W := ⟨6,![cycle529_0,cycle529_1,cycle529_2,cycle529_3,cycle529_4,cycle529_5]⟩
lemma valid_data529 : data529.Valid src529 dst529 Finset.univ := by decide +kernel

def src530 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst530 : E → W := ![4,3,6,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle530_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle530_1 : CycleData E W := ⟨4,![2,15,13,8,7,6],![3,6,27,14,16,18]⟩
def cycle530_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle530_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle530_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle530_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data530 : PartitionData E W := ⟨6,![cycle530_0,cycle530_1,cycle530_2,cycle530_3,cycle530_4,cycle530_5]⟩
lemma valid_data530 : data530.Valid src530 dst530 Finset.univ := by decide +kernel

def src531 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst531 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle531_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle531_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle531_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle531_3 : CycleData E W := ⟨4,![4,20,21,13,12,9],![2,8,18,28,26,14]⟩
def cycle531_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle531_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data531 : PartitionData E W := ⟨6,![cycle531_0,cycle531_1,cycle531_2,cycle531_3,cycle531_4,cycle531_5]⟩
lemma valid_data531 : data531.Valid src531 dst531 Finset.univ := by decide +kernel

def src532 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst532 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle532_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle532_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle532_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle532_3 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,26,14]⟩
def cycle532_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle532_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data532 : PartitionData E W := ⟨6,![cycle532_0,cycle532_1,cycle532_2,cycle532_3,cycle532_4,cycle532_5]⟩
lemma valid_data532 : data532.Valid src532 dst532 Finset.univ := by decide +kernel

def src533 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst533 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle533_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle533_1 : CycleData E W := ⟨3,![2,15,16,7,6],![3,6,26,16,18]⟩
def cycle533_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle533_3 : CycleData E W := ⟨3,![4,20,13,12,9],![2,8,28,26,14]⟩
def cycle533_4 : CycleData E W := ⟨1,![8,17,11],![14,16,27]⟩
def cycle533_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data533 : PartitionData E W := ⟨6,![cycle533_0,cycle533_1,cycle533_2,cycle533_3,cycle533_4,cycle533_5]⟩
lemma valid_data533 : data533.Valid src533 dst533 Finset.univ := by decide +kernel

def src534 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst534 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle534_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle534_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle534_2 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle534_3 : CycleData E W := ⟨2,![7,21,13,16],![16,18,28,26]⟩
def cycle534_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle534_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data534 : PartitionData E W := ⟨6,![cycle534_0,cycle534_1,cycle534_2,cycle534_3,cycle534_4,cycle534_5]⟩
lemma valid_data534 : data534.Valid src534 dst534 Finset.univ := by decide +kernel

def src535 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst535 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle535_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle535_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle535_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,26,14]⟩
def cycle535_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle535_4 : CycleData E W := ⟨3,![15,16,8,11,19],![6,26,16,14,27]⟩
def cycle535_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data535 : PartitionData E W := ⟨6,![cycle535_0,cycle535_1,cycle535_2,cycle535_3,cycle535_4,cycle535_5]⟩
lemma valid_data535 : data535.Valid src535 dst535 Finset.univ := by decide +kernel

def src536 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst536 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle536_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle536_1 : CycleData E W := ⟨3,![2,15,13,21,6],![3,6,26,28,18]⟩
def cycle536_2 : CycleData E W := ⟨3,![4,3,19,11,9],![2,8,6,27,14]⟩
def cycle536_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle536_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle536_5 : CycleData E W := ⟨3,![10,18,23,20,14],![4,27,38,8,28]⟩
def data536 : PartitionData E W := ⟨6,![cycle536_0,cycle536_1,cycle536_2,cycle536_3,cycle536_4,cycle536_5]⟩
lemma valid_data536 : data536.Valid src536 dst536 Finset.univ := by decide +kernel

def src537 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst537 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle537_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle537_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle537_2 : CycleData E W := ⟨3,![4,23,16,12,9],![2,8,38,26,14]⟩
def cycle537_3 : CycleData E W := ⟨2,![7,21,22,17],![16,18,28,38]⟩
def cycle537_4 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle537_5 : CycleData E W := ⟨3,![10,19,15,13,14],![4,27,6,26,28]⟩
def data537 : PartitionData E W := ⟨6,![cycle537_0,cycle537_1,cycle537_2,cycle537_3,cycle537_4,cycle537_5]⟩
lemma valid_data537 : data537.Valid src537 dst537 Finset.univ := by decide +kernel

def src538 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst538 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle538_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle538_1 : CycleData E W := ⟨2,![2,3,20,6],![3,6,8,18]⟩
def cycle538_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,26,14]⟩
def cycle538_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle538_4 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle538_5 : CycleData E W := ⟨4,![10,19,15,16,22,14],![4,27,6,26,38,28]⟩
def data538 : PartitionData E W := ⟨6,![cycle538_0,cycle538_1,cycle538_2,cycle538_3,cycle538_4,cycle538_5]⟩
lemma valid_data538 : data538.Valid src538 dst538 Finset.univ := by decide +kernel

def src539 : E → W := ![2,4,3,6,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst539 : E → W := ![4,3,6,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle539_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle539_1 : CycleData E W := ⟨3,![2,15,13,21,6],![3,6,26,28,18]⟩
def cycle539_2 : CycleData E W := ⟨3,![10,19,3,20,14],![4,27,6,8,28]⟩
def cycle539_3 : CycleData E W := ⟨3,![4,23,16,12,9],![2,8,38,26,14]⟩
def cycle539_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle539_5 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def data539 : PartitionData E W := ⟨6,![cycle539_0,cycle539_1,cycle539_2,cycle539_3,cycle539_4,cycle539_5]⟩
lemma valid_data539 : data539.Valid src539 dst539 Finset.univ := by decide +kernel

def src540 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst540 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle540_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle540_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle540_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle540_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle540_4 : CycleData E W := ⟨3,![10,11,16,22,14],![4,14,26,38,28]⟩
def cycle540_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data540 : PartitionData E W := ⟨6,![cycle540_0,cycle540_1,cycle540_2,cycle540_3,cycle540_4,cycle540_5]⟩
lemma valid_data540 : data540.Valid src540 dst540 Finset.univ := by decide +kernel

def src541 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst541 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle541_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle541_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle541_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle541_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle541_4 : CycleData E W := ⟨3,![10,11,16,22,14],![4,14,26,38,28]⟩
def cycle541_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data541 : PartitionData E W := ⟨6,![cycle541_0,cycle541_1,cycle541_2,cycle541_3,cycle541_4,cycle541_5]⟩
lemma valid_data541 : data541.Valid src541 dst541 Finset.univ := by decide +kernel

def src542 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst542 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle542_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle542_1 : CycleData E W := ⟨3,![1,14,20,3,2],![3,4,28,8,6]⟩
def cycle542_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle542_3 : CycleData E W := ⟨3,![6,11,16,22,7],![3,14,26,38,18]⟩
def cycle542_4 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle542_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data542 : PartitionData E W := ⟨6,![cycle542_0,cycle542_1,cycle542_2,cycle542_3,cycle542_4,cycle542_5]⟩
lemma valid_data542 : data542.Valid src542 dst542 Finset.univ := by decide +kernel

def src543 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst543 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle543_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle543_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle543_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle543_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle543_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,26,38,28]⟩
def cycle543_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data543 : PartitionData E W := ⟨6,![cycle543_0,cycle543_1,cycle543_2,cycle543_3,cycle543_4,cycle543_5]⟩
lemma valid_data543 : data543.Valid src543 dst543 Finset.univ := by decide +kernel

def src544 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst544 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle544_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle544_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle544_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle544_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle544_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,26,38,28]⟩
def cycle544_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data544 : PartitionData E W := ⟨6,![cycle544_0,cycle544_1,cycle544_2,cycle544_3,cycle544_4,cycle544_5]⟩
lemma valid_data544 : data544.Valid src544 dst544 Finset.univ := by decide +kernel

def src545 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst545 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle545_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle545_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,28,27,6]⟩
def cycle545_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle545_3 : CycleData E W := ⟨3,![4,20,21,8,9],![2,8,28,18,16]⟩
def cycle545_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,26,38,18]⟩
def cycle545_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data545 : PartitionData E W := ⟨6,![cycle545_0,cycle545_1,cycle545_2,cycle545_3,cycle545_4,cycle545_5]⟩
lemma valid_data545 : data545.Valid src545 dst545 Finset.univ := by decide +kernel

def src546 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst546 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle546_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle546_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,26,28,18]⟩
def cycle546_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle546_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle546_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle546_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data546 : PartitionData E W := ⟨6,![cycle546_0,cycle546_1,cycle546_2,cycle546_3,cycle546_4,cycle546_5]⟩
lemma valid_data546 : data546.Valid src546 dst546 Finset.univ := by decide +kernel

def src547 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst547 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle547_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle547_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle547_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle547_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle547_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle547_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data547 : PartitionData E W := ⟨6,![cycle547_0,cycle547_1,cycle547_2,cycle547_3,cycle547_4,cycle547_5]⟩
lemma valid_data547 : data547.Valid src547 dst547 Finset.univ := by decide +kernel

def src548 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst548 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle548_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle548_1 : CycleData E W := ⟨3,![1,14,17,8,7],![3,4,27,16,18]⟩
def cycle548_2 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle548_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle548_4 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle548_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data548 : PartitionData E W := ⟨6,![cycle548_0,cycle548_1,cycle548_2,cycle548_3,cycle548_4,cycle548_5]⟩
lemma valid_data548 : data548.Valid src548 dst548 Finset.univ := by decide +kernel

def src549 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst549 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle549_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle549_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle549_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle549_3 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle549_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle549_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data549 : PartitionData E W := ⟨6,![cycle549_0,cycle549_1,cycle549_2,cycle549_3,cycle549_4,cycle549_5]⟩
lemma valid_data549 : data549.Valid src549 dst549 Finset.univ := by decide +kernel

def src550 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst550 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle550_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle550_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle550_2 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle550_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle550_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle550_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data550 : PartitionData E W := ⟨6,![cycle550_0,cycle550_1,cycle550_2,cycle550_3,cycle550_4,cycle550_5]⟩
lemma valid_data550 : data550.Valid src550 dst550 Finset.univ := by decide +kernel

def src551 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst551 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle551_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle551_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle551_2 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle551_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,26,28,18]⟩
def cycle551_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle551_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data551 : PartitionData E W := ⟨6,![cycle551_0,cycle551_1,cycle551_2,cycle551_3,cycle551_4,cycle551_5]⟩
lemma valid_data551 : data551.Valid src551 dst551 Finset.univ := by decide +kernel

def src552 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst552 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle552_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle552_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle552_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle552_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle552_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle552_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data552 : PartitionData E W := ⟨6,![cycle552_0,cycle552_1,cycle552_2,cycle552_3,cycle552_4,cycle552_5]⟩
lemma valid_data552 : data552.Valid src552 dst552 Finset.univ := by decide +kernel

def src553 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst553 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle553_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle553_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle553_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle553_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle553_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle553_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data553 : PartitionData E W := ⟨6,![cycle553_0,cycle553_1,cycle553_2,cycle553_3,cycle553_4,cycle553_5]⟩
lemma valid_data553 : data553.Valid src553 dst553 Finset.univ := by decide +kernel

def src554 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst554 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle554_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle554_1 : CycleData E W := ⟨3,![1,14,18,8,7],![3,4,27,16,18]⟩
def cycle554_2 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle554_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle554_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle554_5 : CycleData E W := ⟨2,![21,12,16,22],![18,28,26,38]⟩
def data554 : PartitionData E W := ⟨6,![cycle554_0,cycle554_1,cycle554_2,cycle554_3,cycle554_4,cycle554_5]⟩
lemma valid_data554 : data554.Valid src554 dst554 Finset.univ := by decide +kernel

def src555 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst555 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle555_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle555_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle555_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle555_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle555_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle555_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data555 : PartitionData E W := ⟨6,![cycle555_0,cycle555_1,cycle555_2,cycle555_3,cycle555_4,cycle555_5]⟩
lemma valid_data555 : data555.Valid src555 dst555 Finset.univ := by decide +kernel

def src556 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst556 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle556_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle556_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle556_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle556_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle556_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle556_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data556 : PartitionData E W := ⟨6,![cycle556_0,cycle556_1,cycle556_2,cycle556_3,cycle556_4,cycle556_5]⟩
lemma valid_data556 : data556.Valid src556 dst556 Finset.univ := by decide +kernel

def src557 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst557 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle557_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle557_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,27,6]⟩
def cycle557_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle557_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle557_4 : CycleData E W := ⟨3,![6,11,17,8,7],![3,14,26,16,18]⟩
def cycle557_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,26,38]⟩
def data557 : PartitionData E W := ⟨6,![cycle557_0,cycle557_1,cycle557_2,cycle557_3,cycle557_4,cycle557_5]⟩
lemma valid_data557 : data557.Valid src557 dst557 Finset.univ := by decide +kernel

def src558 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst558 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle558_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle558_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle558_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle558_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle558_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle558_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data558 : PartitionData E W := ⟨6,![cycle558_0,cycle558_1,cycle558_2,cycle558_3,cycle558_4,cycle558_5]⟩
lemma valid_data558 : data558.Valid src558 dst558 Finset.univ := by decide +kernel

def src559 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst559 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle559_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle559_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle559_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle559_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle559_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle559_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data559 : PartitionData E W := ⟨6,![cycle559_0,cycle559_1,cycle559_2,cycle559_3,cycle559_4,cycle559_5]⟩
lemma valid_data559 : data559.Valid src559 dst559 Finset.univ := by decide +kernel

def src560 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst560 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle560_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle560_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,28,26,6]⟩
def cycle560_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle560_3 : CycleData E W := ⟨3,![4,20,21,8,9],![2,8,28,18,16]⟩
def cycle560_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,27,38,18]⟩
def cycle560_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data560 : PartitionData E W := ⟨6,![cycle560_0,cycle560_1,cycle560_2,cycle560_3,cycle560_4,cycle560_5]⟩
lemma valid_data560 : data560.Valid src560 dst560 Finset.univ := by decide +kernel

def src561 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst561 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle561_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle561_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle561_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle561_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle561_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle561_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data561 : PartitionData E W := ⟨6,![cycle561_0,cycle561_1,cycle561_2,cycle561_3,cycle561_4,cycle561_5]⟩
lemma valid_data561 : data561.Valid src561 dst561 Finset.univ := by decide +kernel

def src562 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst562 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle562_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle562_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle562_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle562_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle562_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle562_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data562 : PartitionData E W := ⟨6,![cycle562_0,cycle562_1,cycle562_2,cycle562_3,cycle562_4,cycle562_5]⟩
lemma valid_data562 : data562.Valid src562 dst562 Finset.univ := by decide +kernel

def src563 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst563 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle563_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle563_1 : CycleData E W := ⟨3,![1,14,20,3,2],![3,4,28,8,6]⟩
def cycle563_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle563_3 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,27,38,18]⟩
def cycle563_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle563_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data563 : PartitionData E W := ⟨6,![cycle563_0,cycle563_1,cycle563_2,cycle563_3,cycle563_4,cycle563_5]⟩
lemma valid_data563 : data563.Valid src563 dst563 Finset.univ := by decide +kernel

def src564 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst564 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle564_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle564_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle564_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle564_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle564_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle564_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data564 : PartitionData E W := ⟨6,![cycle564_0,cycle564_1,cycle564_2,cycle564_3,cycle564_4,cycle564_5]⟩
lemma valid_data564 : data564.Valid src564 dst564 Finset.univ := by decide +kernel

def src565 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst565 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle565_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle565_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle565_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle565_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle565_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle565_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data565 : PartitionData E W := ⟨6,![cycle565_0,cycle565_1,cycle565_2,cycle565_3,cycle565_4,cycle565_5]⟩
lemma valid_data565 : data565.Valid src565 dst565 Finset.univ := by decide +kernel

def src566 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst566 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle566_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle566_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle566_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle566_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle566_4 : CycleData E W := ⟨3,![6,11,17,8,7],![3,14,27,16,18]⟩
def cycle566_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data566 : PartitionData E W := ⟨6,![cycle566_0,cycle566_1,cycle566_2,cycle566_3,cycle566_4,cycle566_5]⟩
lemma valid_data566 : data566.Valid src566 dst566 Finset.univ := by decide +kernel

def src567 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst567 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle567_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle567_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle567_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle567_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle567_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle567_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data567 : PartitionData E W := ⟨6,![cycle567_0,cycle567_1,cycle567_2,cycle567_3,cycle567_4,cycle567_5]⟩
lemma valid_data567 : data567.Valid src567 dst567 Finset.univ := by decide +kernel

def src568 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst568 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle568_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle568_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle568_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle568_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle568_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle568_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data568 : PartitionData E W := ⟨6,![cycle568_0,cycle568_1,cycle568_2,cycle568_3,cycle568_4,cycle568_5]⟩
lemma valid_data568 : data568.Valid src568 dst568 Finset.univ := by decide +kernel

def src569 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst569 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle569_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle569_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle569_2 : CycleData E W := ⟨2,![3,20,12,19],![6,8,28,27]⟩
def cycle569_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle569_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,27,38,18]⟩
def cycle569_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data569 : PartitionData E W := ⟨6,![cycle569_0,cycle569_1,cycle569_2,cycle569_3,cycle569_4,cycle569_5]⟩
lemma valid_data569 : data569.Valid src569 dst569 Finset.univ := by decide +kernel

def src570 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst570 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle570_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle570_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle570_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle570_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle570_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle570_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data570 : PartitionData E W := ⟨6,![cycle570_0,cycle570_1,cycle570_2,cycle570_3,cycle570_4,cycle570_5]⟩
lemma valid_data570 : data570.Valid src570 dst570 Finset.univ := by decide +kernel

def src571 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst571 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle571_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle571_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle571_2 : CycleData E W := ⟨3,![4,23,12,18,9],![2,8,28,27,16]⟩
def cycle571_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle571_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle571_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data571 : PartitionData E W := ⟨6,![cycle571_0,cycle571_1,cycle571_2,cycle571_3,cycle571_4,cycle571_5]⟩
lemma valid_data571 : data571.Valid src571 dst571 Finset.univ := by decide +kernel

def src572 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst572 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle572_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle572_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle572_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle572_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,27,28,18]⟩
def cycle572_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle572_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data572 : PartitionData E W := ⟨6,![cycle572_0,cycle572_1,cycle572_2,cycle572_3,cycle572_4,cycle572_5]⟩
lemma valid_data572 : data572.Valid src572 dst572 Finset.univ := by decide +kernel

def src573 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst573 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle573_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle573_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,27,28,18]⟩
def cycle573_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle573_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle573_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle573_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data573 : PartitionData E W := ⟨6,![cycle573_0,cycle573_1,cycle573_2,cycle573_3,cycle573_4,cycle573_5]⟩
lemma valid_data573 : data573.Valid src573 dst573 Finset.univ := by decide +kernel

def src574 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst574 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle574_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle574_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle574_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle574_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle574_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle574_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data574 : PartitionData E W := ⟨6,![cycle574_0,cycle574_1,cycle574_2,cycle574_3,cycle574_4,cycle574_5]⟩
lemma valid_data574 : data574.Valid src574 dst574 Finset.univ := by decide +kernel

def src575 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst575 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle575_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle575_1 : CycleData E W := ⟨3,![1,14,17,8,7],![3,4,26,16,18]⟩
def cycle575_2 : CycleData E W := ⟨2,![2,15,11,6],![3,6,27,14]⟩
def cycle575_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle575_4 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,27,16]⟩
def cycle575_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data575 : PartitionData E W := ⟨6,![cycle575_0,cycle575_1,cycle575_2,cycle575_3,cycle575_4,cycle575_5]⟩
lemma valid_data575 : data575.Valid src575 dst575 Finset.univ := by decide +kernel

def src576 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst576 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle576_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle576_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,26,28,18]⟩
def cycle576_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle576_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle576_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle576_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data576 : PartitionData E W := ⟨6,![cycle576_0,cycle576_1,cycle576_2,cycle576_3,cycle576_4,cycle576_5]⟩
lemma valid_data576 : data576.Valid src576 dst576 Finset.univ := by decide +kernel

def src577 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst577 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle577_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle577_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle577_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle577_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle577_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle577_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data577 : PartitionData E W := ⟨6,![cycle577_0,cycle577_1,cycle577_2,cycle577_3,cycle577_4,cycle577_5]⟩
lemma valid_data577 : data577.Valid src577 dst577 Finset.univ := by decide +kernel

def src578 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst578 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle578_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle578_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,27,26,6]⟩
def cycle578_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle578_3 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle578_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle578_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data578 : PartitionData E W := ⟨6,![cycle578_0,cycle578_1,cycle578_2,cycle578_3,cycle578_4,cycle578_5]⟩
lemma valid_data578 : data578.Valid src578 dst578 Finset.univ := by decide +kernel

def src579 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst579 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle579_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle579_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle579_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle579_3 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle579_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle579_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data579 : PartitionData E W := ⟨6,![cycle579_0,cycle579_1,cycle579_2,cycle579_3,cycle579_4,cycle579_5]⟩
lemma valid_data579 : data579.Valid src579 dst579 Finset.univ := by decide +kernel

def src580 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst580 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle580_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle580_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle580_2 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle580_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle580_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle580_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data580 : PartitionData E W := ⟨6,![cycle580_0,cycle580_1,cycle580_2,cycle580_3,cycle580_4,cycle580_5]⟩
lemma valid_data580 : data580.Valid src580 dst580 Finset.univ := by decide +kernel

def src581 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst581 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle581_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle581_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,27,26,6]⟩
def cycle581_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle581_3 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle581_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle581_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data581 : PartitionData E W := ⟨6,![cycle581_0,cycle581_1,cycle581_2,cycle581_3,cycle581_4,cycle581_5]⟩
lemma valid_data581 : data581.Valid src581 dst581 Finset.univ := by decide +kernel

def src582 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst582 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle582_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle582_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle582_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle582_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle582_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle582_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data582 : PartitionData E W := ⟨6,![cycle582_0,cycle582_1,cycle582_2,cycle582_3,cycle582_4,cycle582_5]⟩
lemma valid_data582 : data582.Valid src582 dst582 Finset.univ := by decide +kernel

def src583 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst583 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle583_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle583_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle583_2 : CycleData E W := ⟨3,![4,23,12,18,9],![2,8,28,27,16]⟩
def cycle583_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle583_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle583_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data583 : PartitionData E W := ⟨6,![cycle583_0,cycle583_1,cycle583_2,cycle583_3,cycle583_4,cycle583_5]⟩
lemma valid_data583 : data583.Valid src583 dst583 Finset.univ := by decide +kernel

def src584 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst584 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle584_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle584_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle584_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle584_3 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle584_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle584_5 : CycleData E W := ⟨3,![20,12,13,16,23],![8,28,27,26,38]⟩
def data584 : PartitionData E W := ⟨6,![cycle584_0,cycle584_1,cycle584_2,cycle584_3,cycle584_4,cycle584_5]⟩
lemma valid_data584 : data584.Valid src584 dst584 Finset.univ := by decide +kernel

def src585 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst585 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle585_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle585_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,27,28,18]⟩
def cycle585_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle585_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle585_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle585_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data585 : PartitionData E W := ⟨6,![cycle585_0,cycle585_1,cycle585_2,cycle585_3,cycle585_4,cycle585_5]⟩
lemma valid_data585 : data585.Valid src585 dst585 Finset.univ := by decide +kernel

def src586 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst586 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle586_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle586_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle586_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle586_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle586_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle586_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data586 : PartitionData E W := ⟨6,![cycle586_0,cycle586_1,cycle586_2,cycle586_3,cycle586_4,cycle586_5]⟩
lemma valid_data586 : data586.Valid src586 dst586 Finset.univ := by decide +kernel

def src587 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst587 : E → W := ![4,3,6,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle587_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle587_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,26,27,6]⟩
def cycle587_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle587_3 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,27,16]⟩
def cycle587_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle587_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data587 : PartitionData E W := ⟨6,![cycle587_0,cycle587_1,cycle587_2,cycle587_3,cycle587_4,cycle587_5]⟩
lemma valid_data587 : data587.Valid src587 dst587 Finset.univ := by decide +kernel

def src588 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst588 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle588_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle588_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle588_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,27,14]⟩
def cycle588_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle588_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle588_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data588 : PartitionData E W := ⟨6,![cycle588_0,cycle588_1,cycle588_2,cycle588_3,cycle588_4,cycle588_5]⟩
lemma valid_data588 : data588.Valid src588 dst588 Finset.univ := by decide +kernel

def src589 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst589 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle589_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle589_1 : CycleData E W := ⟨3,![1,14,23,20,7],![3,4,28,8,18]⟩
def cycle589_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,27,14]⟩
def cycle589_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle589_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle589_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data589 : PartitionData E W := ⟨6,![cycle589_0,cycle589_1,cycle589_2,cycle589_3,cycle589_4,cycle589_5]⟩
lemma valid_data589 : data589.Valid src589 dst589 Finset.univ := by decide +kernel

def src590 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst590 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle590_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle590_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle590_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,27,14]⟩
def cycle590_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle590_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle590_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data590 : PartitionData E W := ⟨6,![cycle590_0,cycle590_1,cycle590_2,cycle590_3,cycle590_4,cycle590_5]⟩
lemma valid_data590 : data590.Valid src590 dst590 Finset.univ := by decide +kernel

def src591 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst591 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle591_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle591_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle591_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle591_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,27,16]⟩
def cycle591_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle591_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data591 : PartitionData E W := ⟨6,![cycle591_0,cycle591_1,cycle591_2,cycle591_3,cycle591_4,cycle591_5]⟩
lemma valid_data591 : data591.Valid src591 dst591 Finset.univ := by decide +kernel

def src592 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst592 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle592_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle592_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle592_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle592_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle592_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle592_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data592 : PartitionData E W := ⟨6,![cycle592_0,cycle592_1,cycle592_2,cycle592_3,cycle592_4,cycle592_5]⟩
lemma valid_data592 : data592.Valid src592 dst592 Finset.univ := by decide +kernel

def src593 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst593 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle593_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle593_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle593_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle593_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle593_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle593_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data593 : PartitionData E W := ⟨6,![cycle593_0,cycle593_1,cycle593_2,cycle593_3,cycle593_4,cycle593_5]⟩
lemma valid_data593 : data593.Valid src593 dst593 Finset.univ := by decide +kernel

def src594 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst594 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle594_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle594_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle594_2 : CycleData E W := ⟨3,![2,15,16,12,6],![3,6,16,27,14]⟩
def cycle594_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle594_4 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle594_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data594 : PartitionData E W := ⟨6,![cycle594_0,cycle594_1,cycle594_2,cycle594_3,cycle594_4,cycle594_5]⟩
lemma valid_data594 : data594.Valid src594 dst594 Finset.univ := by decide +kernel

def src595 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst595 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle595_0 : CycleData E W := ⟨2,![0,14,23,4],![2,4,28,8]⟩
def cycle595_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle595_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle595_3 : CycleData E W := ⟨3,![3,20,21,18,19],![6,8,18,38,26]⟩
def cycle595_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,27,16]⟩
def cycle595_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data595 : PartitionData E W := ⟨6,![cycle595_0,cycle595_1,cycle595_2,cycle595_3,cycle595_4,cycle595_5]⟩
lemma valid_data595 : data595.Valid src595 dst595 Finset.univ := by decide +kernel

def src596 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst596 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle596_0 : CycleData E W := ⟨2,![0,14,20,4],![2,4,28,8]⟩
def cycle596_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle596_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle596_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle596_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,27,16]⟩
def cycle596_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data596 : PartitionData E W := ⟨6,![cycle596_0,cycle596_1,cycle596_2,cycle596_3,cycle596_4,cycle596_5]⟩
lemma valid_data596 : data596.Valid src596 dst596 Finset.univ := by decide +kernel

def src597 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst597 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle597_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle597_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle597_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle597_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle597_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle597_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data597 : PartitionData E W := ⟨6,![cycle597_0,cycle597_1,cycle597_2,cycle597_3,cycle597_4,cycle597_5]⟩
lemma valid_data597 : data597.Valid src597 dst597 Finset.univ := by decide +kernel

def src598 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst598 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle598_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle598_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle598_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle598_3 : CycleData E W := ⟨3,![4,20,21,16,9],![2,8,18,38,16]⟩
def cycle598_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle598_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data598 : PartitionData E W := ⟨6,![cycle598_0,cycle598_1,cycle598_2,cycle598_3,cycle598_4,cycle598_5]⟩
lemma valid_data598 : data598.Valid src598 dst598 Finset.univ := by decide +kernel

def src599 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst599 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle599_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle599_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle599_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle599_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle599_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,26,38,18,28]⟩
def cycle599_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data599 : PartitionData E W := ⟨6,![cycle599_0,cycle599_1,cycle599_2,cycle599_3,cycle599_4,cycle599_5]⟩
lemma valid_data599 : data599.Valid src599 dst599 Finset.univ := by decide +kernel

def lookupB2 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data400 else (if j < 2 then data401 else data402)) else (if j < 4 then data403 else (if j < 5 then data404 else data405))) else (if j < 9 then (if j < 7 then data406 else (if j < 8 then data407 else data408)) else (if j < 10 then data409 else (if j < 11 then data410 else data411)))) else (if j < 18 then (if j < 15 then (if j < 13 then data412 else (if j < 14 then data413 else data414)) else (if j < 16 then data415 else (if j < 17 then data416 else data417))) else (if j < 21 then (if j < 19 then data418 else (if j < 20 then data419 else data420)) else (if j < 23 then (if j < 22 then data421 else data422) else (if j < 24 then data423 else data424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data425 else (if j < 27 then data426 else data427)) else (if j < 29 then data428 else (if j < 30 then data429 else data430))) else (if j < 34 then (if j < 32 then data431 else (if j < 33 then data432 else data433)) else (if j < 35 then data434 else (if j < 36 then data435 else data436)))) else (if j < 43 then (if j < 40 then (if j < 38 then data437 else (if j < 39 then data438 else data439)) else (if j < 41 then data440 else (if j < 42 then data441 else data442))) else (if j < 46 then (if j < 44 then data443 else (if j < 45 then data444 else data445)) else (if j < 48 then (if j < 47 then data446 else data447) else (if j < 49 then data448 else data449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data450 else (if j < 52 then data451 else data452)) else (if j < 54 then data453 else (if j < 55 then data454 else data455))) else (if j < 59 then (if j < 57 then data456 else (if j < 58 then data457 else data458)) else (if j < 60 then data459 else (if j < 61 then data460 else data461)))) else (if j < 68 then (if j < 65 then (if j < 63 then data462 else (if j < 64 then data463 else data464)) else (if j < 66 then data465 else (if j < 67 then data466 else data467))) else (if j < 71 then (if j < 69 then data468 else (if j < 70 then data469 else data470)) else (if j < 73 then (if j < 72 then data471 else data472) else (if j < 74 then data473 else data474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data475 else (if j < 77 then data476 else data477)) else (if j < 79 then data478 else (if j < 80 then data479 else data480))) else (if j < 84 then (if j < 82 then data481 else (if j < 83 then data482 else data483)) else (if j < 85 then data484 else (if j < 86 then data485 else data486)))) else (if j < 93 then (if j < 90 then (if j < 88 then data487 else (if j < 89 then data488 else data489)) else (if j < 91 then data490 else (if j < 92 then data491 else data492))) else (if j < 96 then (if j < 94 then data493 else (if j < 95 then data494 else data495)) else (if j < 98 then (if j < 97 then data496 else data497) else (if j < 99 then data498 else data499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data500 else (if j < 102 then data501 else data502)) else (if j < 104 then data503 else (if j < 105 then data504 else data505))) else (if j < 109 then (if j < 107 then data506 else (if j < 108 then data507 else data508)) else (if j < 110 then data509 else (if j < 111 then data510 else data511)))) else (if j < 118 then (if j < 115 then (if j < 113 then data512 else (if j < 114 then data513 else data514)) else (if j < 116 then data515 else (if j < 117 then data516 else data517))) else (if j < 121 then (if j < 119 then data518 else (if j < 120 then data519 else data520)) else (if j < 123 then (if j < 122 then data521 else data522) else (if j < 124 then data523 else data524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data525 else (if j < 127 then data526 else data527)) else (if j < 129 then data528 else (if j < 130 then data529 else data530))) else (if j < 134 then (if j < 132 then data531 else (if j < 133 then data532 else data533)) else (if j < 135 then data534 else (if j < 136 then data535 else data536)))) else (if j < 143 then (if j < 140 then (if j < 138 then data537 else (if j < 139 then data538 else data539)) else (if j < 141 then data540 else (if j < 142 then data541 else data542))) else (if j < 146 then (if j < 144 then data543 else (if j < 145 then data544 else data545)) else (if j < 148 then (if j < 147 then data546 else data547) else (if j < 149 then data548 else data549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data550 else (if j < 152 then data551 else data552)) else (if j < 154 then data553 else (if j < 155 then data554 else data555))) else (if j < 159 then (if j < 157 then data556 else (if j < 158 then data557 else data558)) else (if j < 160 then data559 else (if j < 161 then data560 else data561)))) else (if j < 168 then (if j < 165 then (if j < 163 then data562 else (if j < 164 then data563 else data564)) else (if j < 166 then data565 else (if j < 167 then data566 else data567))) else (if j < 171 then (if j < 169 then data568 else (if j < 170 then data569 else data570)) else (if j < 173 then (if j < 172 then data571 else data572) else (if j < 174 then data573 else data574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data575 else (if j < 177 then data576 else data577)) else (if j < 179 then data578 else (if j < 180 then data579 else data580))) else (if j < 184 then (if j < 182 then data581 else (if j < 183 then data582 else data583)) else (if j < 185 then data584 else (if j < 186 then data585 else data586)))) else (if j < 193 then (if j < 190 then (if j < 188 then data587 else (if j < 189 then data588 else data589)) else (if j < 191 then data590 else (if j < 192 then data591 else data592))) else (if j < 196 then (if j < 194 then data593 else (if j < 195 then data594 else data595)) else (if j < 198 then (if j < 197 then data596 else data597) else (if j < 199 then data598 else data599))))))))

def srcTableB2 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src400 else (if j < 2 then src401 else src402)) else (if j < 4 then src403 else (if j < 5 then src404 else src405))) else (if j < 9 then (if j < 7 then src406 else (if j < 8 then src407 else src408)) else (if j < 10 then src409 else (if j < 11 then src410 else src411)))) else (if j < 18 then (if j < 15 then (if j < 13 then src412 else (if j < 14 then src413 else src414)) else (if j < 16 then src415 else (if j < 17 then src416 else src417))) else (if j < 21 then (if j < 19 then src418 else (if j < 20 then src419 else src420)) else (if j < 23 then (if j < 22 then src421 else src422) else (if j < 24 then src423 else src424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src425 else (if j < 27 then src426 else src427)) else (if j < 29 then src428 else (if j < 30 then src429 else src430))) else (if j < 34 then (if j < 32 then src431 else (if j < 33 then src432 else src433)) else (if j < 35 then src434 else (if j < 36 then src435 else src436)))) else (if j < 43 then (if j < 40 then (if j < 38 then src437 else (if j < 39 then src438 else src439)) else (if j < 41 then src440 else (if j < 42 then src441 else src442))) else (if j < 46 then (if j < 44 then src443 else (if j < 45 then src444 else src445)) else (if j < 48 then (if j < 47 then src446 else src447) else (if j < 49 then src448 else src449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src450 else (if j < 52 then src451 else src452)) else (if j < 54 then src453 else (if j < 55 then src454 else src455))) else (if j < 59 then (if j < 57 then src456 else (if j < 58 then src457 else src458)) else (if j < 60 then src459 else (if j < 61 then src460 else src461)))) else (if j < 68 then (if j < 65 then (if j < 63 then src462 else (if j < 64 then src463 else src464)) else (if j < 66 then src465 else (if j < 67 then src466 else src467))) else (if j < 71 then (if j < 69 then src468 else (if j < 70 then src469 else src470)) else (if j < 73 then (if j < 72 then src471 else src472) else (if j < 74 then src473 else src474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src475 else (if j < 77 then src476 else src477)) else (if j < 79 then src478 else (if j < 80 then src479 else src480))) else (if j < 84 then (if j < 82 then src481 else (if j < 83 then src482 else src483)) else (if j < 85 then src484 else (if j < 86 then src485 else src486)))) else (if j < 93 then (if j < 90 then (if j < 88 then src487 else (if j < 89 then src488 else src489)) else (if j < 91 then src490 else (if j < 92 then src491 else src492))) else (if j < 96 then (if j < 94 then src493 else (if j < 95 then src494 else src495)) else (if j < 98 then (if j < 97 then src496 else src497) else (if j < 99 then src498 else src499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src500 else (if j < 102 then src501 else src502)) else (if j < 104 then src503 else (if j < 105 then src504 else src505))) else (if j < 109 then (if j < 107 then src506 else (if j < 108 then src507 else src508)) else (if j < 110 then src509 else (if j < 111 then src510 else src511)))) else (if j < 118 then (if j < 115 then (if j < 113 then src512 else (if j < 114 then src513 else src514)) else (if j < 116 then src515 else (if j < 117 then src516 else src517))) else (if j < 121 then (if j < 119 then src518 else (if j < 120 then src519 else src520)) else (if j < 123 then (if j < 122 then src521 else src522) else (if j < 124 then src523 else src524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src525 else (if j < 127 then src526 else src527)) else (if j < 129 then src528 else (if j < 130 then src529 else src530))) else (if j < 134 then (if j < 132 then src531 else (if j < 133 then src532 else src533)) else (if j < 135 then src534 else (if j < 136 then src535 else src536)))) else (if j < 143 then (if j < 140 then (if j < 138 then src537 else (if j < 139 then src538 else src539)) else (if j < 141 then src540 else (if j < 142 then src541 else src542))) else (if j < 146 then (if j < 144 then src543 else (if j < 145 then src544 else src545)) else (if j < 148 then (if j < 147 then src546 else src547) else (if j < 149 then src548 else src549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src550 else (if j < 152 then src551 else src552)) else (if j < 154 then src553 else (if j < 155 then src554 else src555))) else (if j < 159 then (if j < 157 then src556 else (if j < 158 then src557 else src558)) else (if j < 160 then src559 else (if j < 161 then src560 else src561)))) else (if j < 168 then (if j < 165 then (if j < 163 then src562 else (if j < 164 then src563 else src564)) else (if j < 166 then src565 else (if j < 167 then src566 else src567))) else (if j < 171 then (if j < 169 then src568 else (if j < 170 then src569 else src570)) else (if j < 173 then (if j < 172 then src571 else src572) else (if j < 174 then src573 else src574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src575 else (if j < 177 then src576 else src577)) else (if j < 179 then src578 else (if j < 180 then src579 else src580))) else (if j < 184 then (if j < 182 then src581 else (if j < 183 then src582 else src583)) else (if j < 185 then src584 else (if j < 186 then src585 else src586)))) else (if j < 193 then (if j < 190 then (if j < 188 then src587 else (if j < 189 then src588 else src589)) else (if j < 191 then src590 else (if j < 192 then src591 else src592))) else (if j < 196 then (if j < 194 then src593 else (if j < 195 then src594 else src595)) else (if j < 198 then (if j < 197 then src596 else src597) else (if j < 199 then src598 else src599))))))))

def dstTableB2 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst400 else (if j < 2 then dst401 else dst402)) else (if j < 4 then dst403 else (if j < 5 then dst404 else dst405))) else (if j < 9 then (if j < 7 then dst406 else (if j < 8 then dst407 else dst408)) else (if j < 10 then dst409 else (if j < 11 then dst410 else dst411)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst412 else (if j < 14 then dst413 else dst414)) else (if j < 16 then dst415 else (if j < 17 then dst416 else dst417))) else (if j < 21 then (if j < 19 then dst418 else (if j < 20 then dst419 else dst420)) else (if j < 23 then (if j < 22 then dst421 else dst422) else (if j < 24 then dst423 else dst424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst425 else (if j < 27 then dst426 else dst427)) else (if j < 29 then dst428 else (if j < 30 then dst429 else dst430))) else (if j < 34 then (if j < 32 then dst431 else (if j < 33 then dst432 else dst433)) else (if j < 35 then dst434 else (if j < 36 then dst435 else dst436)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst437 else (if j < 39 then dst438 else dst439)) else (if j < 41 then dst440 else (if j < 42 then dst441 else dst442))) else (if j < 46 then (if j < 44 then dst443 else (if j < 45 then dst444 else dst445)) else (if j < 48 then (if j < 47 then dst446 else dst447) else (if j < 49 then dst448 else dst449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst450 else (if j < 52 then dst451 else dst452)) else (if j < 54 then dst453 else (if j < 55 then dst454 else dst455))) else (if j < 59 then (if j < 57 then dst456 else (if j < 58 then dst457 else dst458)) else (if j < 60 then dst459 else (if j < 61 then dst460 else dst461)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst462 else (if j < 64 then dst463 else dst464)) else (if j < 66 then dst465 else (if j < 67 then dst466 else dst467))) else (if j < 71 then (if j < 69 then dst468 else (if j < 70 then dst469 else dst470)) else (if j < 73 then (if j < 72 then dst471 else dst472) else (if j < 74 then dst473 else dst474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst475 else (if j < 77 then dst476 else dst477)) else (if j < 79 then dst478 else (if j < 80 then dst479 else dst480))) else (if j < 84 then (if j < 82 then dst481 else (if j < 83 then dst482 else dst483)) else (if j < 85 then dst484 else (if j < 86 then dst485 else dst486)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst487 else (if j < 89 then dst488 else dst489)) else (if j < 91 then dst490 else (if j < 92 then dst491 else dst492))) else (if j < 96 then (if j < 94 then dst493 else (if j < 95 then dst494 else dst495)) else (if j < 98 then (if j < 97 then dst496 else dst497) else (if j < 99 then dst498 else dst499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst500 else (if j < 102 then dst501 else dst502)) else (if j < 104 then dst503 else (if j < 105 then dst504 else dst505))) else (if j < 109 then (if j < 107 then dst506 else (if j < 108 then dst507 else dst508)) else (if j < 110 then dst509 else (if j < 111 then dst510 else dst511)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst512 else (if j < 114 then dst513 else dst514)) else (if j < 116 then dst515 else (if j < 117 then dst516 else dst517))) else (if j < 121 then (if j < 119 then dst518 else (if j < 120 then dst519 else dst520)) else (if j < 123 then (if j < 122 then dst521 else dst522) else (if j < 124 then dst523 else dst524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst525 else (if j < 127 then dst526 else dst527)) else (if j < 129 then dst528 else (if j < 130 then dst529 else dst530))) else (if j < 134 then (if j < 132 then dst531 else (if j < 133 then dst532 else dst533)) else (if j < 135 then dst534 else (if j < 136 then dst535 else dst536)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst537 else (if j < 139 then dst538 else dst539)) else (if j < 141 then dst540 else (if j < 142 then dst541 else dst542))) else (if j < 146 then (if j < 144 then dst543 else (if j < 145 then dst544 else dst545)) else (if j < 148 then (if j < 147 then dst546 else dst547) else (if j < 149 then dst548 else dst549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst550 else (if j < 152 then dst551 else dst552)) else (if j < 154 then dst553 else (if j < 155 then dst554 else dst555))) else (if j < 159 then (if j < 157 then dst556 else (if j < 158 then dst557 else dst558)) else (if j < 160 then dst559 else (if j < 161 then dst560 else dst561)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst562 else (if j < 164 then dst563 else dst564)) else (if j < 166 then dst565 else (if j < 167 then dst566 else dst567))) else (if j < 171 then (if j < 169 then dst568 else (if j < 170 then dst569 else dst570)) else (if j < 173 then (if j < 172 then dst571 else dst572) else (if j < 174 then dst573 else dst574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst575 else (if j < 177 then dst576 else dst577)) else (if j < 179 then dst578 else (if j < 180 then dst579 else dst580))) else (if j < 184 then (if j < 182 then dst581 else (if j < 183 then dst582 else dst583)) else (if j < 185 then dst584 else (if j < 186 then dst585 else dst586)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst587 else (if j < 189 then dst588 else dst589)) else (if j < 191 then dst590 else (if j < 192 then dst591 else dst592))) else (if j < 196 then (if j < 194 then dst593 else (if j < 195 then dst594 else dst595)) else (if j < 198 then (if j < 197 then dst596 else dst597) else (if j < 199 then dst598 else dst599))))))))

def caseB2 (i : Fin 200) : Cases := ⟨400 + i.val,by have := i.isLt; omega⟩
lemma tableB2_valid (i : Fin 200) :
    (lookupB2 i.val).Valid (srcTableB2 i.val) (dstTableB2 i.val) Finset.univ := by
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
  · exact valid_data450
  · exact valid_data451
  · exact valid_data452
  · exact valid_data453
  · exact valid_data454
  · exact valid_data455
  · exact valid_data456
  · exact valid_data457
  · exact valid_data458
  · exact valid_data459
  · exact valid_data460
  · exact valid_data461
  · exact valid_data462
  · exact valid_data463
  · exact valid_data464
  · exact valid_data465
  · exact valid_data466
  · exact valid_data467
  · exact valid_data468
  · exact valid_data469
  · exact valid_data470
  · exact valid_data471
  · exact valid_data472
  · exact valid_data473
  · exact valid_data474
  · exact valid_data475
  · exact valid_data476
  · exact valid_data477
  · exact valid_data478
  · exact valid_data479
  · exact valid_data480
  · exact valid_data481
  · exact valid_data482
  · exact valid_data483
  · exact valid_data484
  · exact valid_data485
  · exact valid_data486
  · exact valid_data487
  · exact valid_data488
  · exact valid_data489
  · exact valid_data490
  · exact valid_data491
  · exact valid_data492
  · exact valid_data493
  · exact valid_data494
  · exact valid_data495
  · exact valid_data496
  · exact valid_data497
  · exact valid_data498
  · exact valid_data499
  · exact valid_data500
  · exact valid_data501
  · exact valid_data502
  · exact valid_data503
  · exact valid_data504
  · exact valid_data505
  · exact valid_data506
  · exact valid_data507
  · exact valid_data508
  · exact valid_data509
  · exact valid_data510
  · exact valid_data511
  · exact valid_data512
  · exact valid_data513
  · exact valid_data514
  · exact valid_data515
  · exact valid_data516
  · exact valid_data517
  · exact valid_data518
  · exact valid_data519
  · exact valid_data520
  · exact valid_data521
  · exact valid_data522
  · exact valid_data523
  · exact valid_data524
  · exact valid_data525
  · exact valid_data526
  · exact valid_data527
  · exact valid_data528
  · exact valid_data529
  · exact valid_data530
  · exact valid_data531
  · exact valid_data532
  · exact valid_data533
  · exact valid_data534
  · exact valid_data535
  · exact valid_data536
  · exact valid_data537
  · exact valid_data538
  · exact valid_data539
  · exact valid_data540
  · exact valid_data541
  · exact valid_data542
  · exact valid_data543
  · exact valid_data544
  · exact valid_data545
  · exact valid_data546
  · exact valid_data547
  · exact valid_data548
  · exact valid_data549
  · exact valid_data550
  · exact valid_data551
  · exact valid_data552
  · exact valid_data553
  · exact valid_data554
  · exact valid_data555
  · exact valid_data556
  · exact valid_data557
  · exact valid_data558
  · exact valid_data559
  · exact valid_data560
  · exact valid_data561
  · exact valid_data562
  · exact valid_data563
  · exact valid_data564
  · exact valid_data565
  · exact valid_data566
  · exact valid_data567
  · exact valid_data568
  · exact valid_data569
  · exact valid_data570
  · exact valid_data571
  · exact valid_data572
  · exact valid_data573
  · exact valid_data574
  · exact valid_data575
  · exact valid_data576
  · exact valid_data577
  · exact valid_data578
  · exact valid_data579
  · exact valid_data580
  · exact valid_data581
  · exact valid_data582
  · exact valid_data583
  · exact valid_data584
  · exact valid_data585
  · exact valid_data586
  · exact valid_data587
  · exact valid_data588
  · exact valid_data589
  · exact valid_data590
  · exact valid_data591
  · exact valid_data592
  · exact valid_data593
  · exact valid_data594
  · exact valid_data595
  · exact valid_data596
  · exact valid_data597
  · exact valid_data598
  · exact valid_data599

lemma srcB2_row : ∀ (i : Fin 200) (e : E),
    srcTableB2 i.val e = caseSource (caseB2 i) e := by decide +kernel

lemma dstB2_row : ∀ (i : Fin 200) (e : E),
    dstTableB2 i.val e = caseTarget (caseB2 i) e := by decide +kernel

lemma sizeB2 : ∀ i : Fin 200, (lookupB2 i.val).size ≤ 5 →
    (lookupB2 i.val).size = 2 ∧
      (⟨caseKey (caseB2 i),caseKey_lt (caseB2 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB2 (i : Fin 200) : Certificate (caseB2 i) := by
  refine ⟨lookupB2 i.val,?_,sizeB2 i⟩
  have hv := tableB2_valid i
  rw [funext (srcB2_row i),funext (dstB2_row i)] at hv
  exact hv
lemma certificateInterval2 : FiniteIntervals.Covers CertificateAt 400 600 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 400 200 (fun i _ => certificateB2 i)
#print axioms certificateInterval2
end Erdos184Work.FiveRows3

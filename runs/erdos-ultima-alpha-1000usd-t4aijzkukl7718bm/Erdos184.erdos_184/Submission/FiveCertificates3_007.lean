import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1400 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst1400 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1400_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1400_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1400_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1400_3 : CycleData E W := ⟨4,![4,15,13,14,10,5],![2,6,26,28,4,14]⟩
def cycle1400_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle1400_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1400 : PartitionData E W := ⟨6,![cycle1400_0,cycle1400_1,cycle1400_2,cycle1400_3,cycle1400_4,cycle1400_5]⟩
lemma valid_data1400 : data1400.Valid src1400 dst1400 Finset.univ := by decide +kernel

def src1401 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst1401 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1401_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1401_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1401_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1401_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1401_4 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1401_5 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data1401 : PartitionData E W := ⟨6,![cycle1401_0,cycle1401_1,cycle1401_2,cycle1401_3,cycle1401_4,cycle1401_5]⟩
lemma valid_data1401 : data1401.Valid src1401 dst1401 Finset.univ := by decide +kernel

def src1402 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst1402 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1402_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1402_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1402_2 : CycleData E W := ⟨4,![4,3,23,14,10,5],![2,6,8,28,4,14]⟩
def cycle1402_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def cycle1402_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1402_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data1402 : PartitionData E W := ⟨6,![cycle1402_0,cycle1402_1,cycle1402_2,cycle1402_3,cycle1402_4,cycle1402_5]⟩
lemma valid_data1402 : data1402.Valid src1402 dst1402 Finset.univ := by decide +kernel

def src1403 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst1403 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1403_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1403_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1403_2 : CycleData E W := ⟨2,![3,20,13,15],![6,8,28,26]⟩
def cycle1403_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1403_4 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle1403_5 : CycleData E W := ⟨2,![16,12,18,17],![16,26,27,38]⟩
def data1403 : PartitionData E W := ⟨6,![cycle1403_0,cycle1403_1,cycle1403_2,cycle1403_3,cycle1403_4,cycle1403_5]⟩
lemma valid_data1403 : data1403.Valid src1403 dst1403 Finset.univ := by decide +kernel

def src1404 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst1404 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle1404_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1404_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1404_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1404_3 : CycleData E W := ⟨3,![4,15,14,10,5],![2,6,26,4,14]⟩
def cycle1404_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle1404_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data1404 : PartitionData E W := ⟨6,![cycle1404_0,cycle1404_1,cycle1404_2,cycle1404_3,cycle1404_4,cycle1404_5]⟩
lemma valid_data1404 : data1404.Valid src1404 dst1404 Finset.univ := by decide +kernel

def src1405 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst1405 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle1405_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1405_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1405_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1405_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1405_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle1405_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1405 : PartitionData E W := ⟨6,![cycle1405_0,cycle1405_1,cycle1405_2,cycle1405_3,cycle1405_4,cycle1405_5]⟩
lemma valid_data1405 : data1405.Valid src1405 dst1405 Finset.univ := by decide +kernel

def src1406 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst1406 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle1406_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1406_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1406_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1406_3 : CycleData E W := ⟨3,![4,15,14,10,5],![2,6,26,4,14]⟩
def cycle1406_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle1406_5 : CycleData E W := ⟨2,![16,13,12,17],![16,26,28,27]⟩
def data1406 : PartitionData E W := ⟨6,![cycle1406_0,cycle1406_1,cycle1406_2,cycle1406_3,cycle1406_4,cycle1406_5]⟩
lemma valid_data1406 : data1406.Valid src1406 dst1406 Finset.univ := by decide +kernel

def src1407 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst1407 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle1407_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1407_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1407_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1407_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1407_4 : CycleData E W := ⟨3,![10,6,21,13,14],![4,14,18,28,26]⟩
def cycle1407_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1407 : PartitionData E W := ⟨6,![cycle1407_0,cycle1407_1,cycle1407_2,cycle1407_3,cycle1407_4,cycle1407_5]⟩
lemma valid_data1407 : data1407.Valid src1407 dst1407 Finset.univ := by decide +kernel

def src1408 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst1408 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle1408_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1408_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1408_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1408_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1408_4 : CycleData E W := ⟨4,![10,6,21,17,16,14],![4,14,18,38,16,26]⟩
def cycle1408_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1408 : PartitionData E W := ⟨6,![cycle1408_0,cycle1408_1,cycle1408_2,cycle1408_3,cycle1408_4,cycle1408_5]⟩
lemma valid_data1408 : data1408.Valid src1408 dst1408 Finset.univ := by decide +kernel

def src1409 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst1409 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle1409_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1409_1 : CycleData E W := ⟨2,![1,14,16,8],![3,4,26,16]⟩
def cycle1409_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1409_3 : CycleData E W := ⟨3,![4,3,23,17,9],![2,6,8,38,16]⟩
def cycle1409_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle1409_5 : CycleData E W := ⟨2,![15,13,12,19],![6,26,28,27]⟩
def data1409 : PartitionData E W := ⟨6,![cycle1409_0,cycle1409_1,cycle1409_2,cycle1409_3,cycle1409_4,cycle1409_5]⟩
lemma valid_data1409 : data1409.Valid src1409 dst1409 Finset.univ := by decide +kernel

def src1410 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst1410 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle1410_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1410_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1410_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1410_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1410_4 : CycleData E W := ⟨3,![10,6,21,13,14],![4,14,18,28,26]⟩
def cycle1410_5 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def data1410 : PartitionData E W := ⟨6,![cycle1410_0,cycle1410_1,cycle1410_2,cycle1410_3,cycle1410_4,cycle1410_5]⟩
lemma valid_data1410 : data1410.Valid src1410 dst1410 Finset.univ := by decide +kernel

def src1411 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst1411 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle1411_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1411_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1411_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1411_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1411_4 : CycleData E W := ⟨3,![10,6,21,16,14],![4,14,18,38,26]⟩
def cycle1411_5 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def data1411 : PartitionData E W := ⟨6,![cycle1411_0,cycle1411_1,cycle1411_2,cycle1411_3,cycle1411_4,cycle1411_5]⟩
lemma valid_data1411 : data1411.Valid src1411 dst1411 Finset.univ := by decide +kernel

def src1412 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst1412 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle1412_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1412_1 : CycleData E W := ⟨3,![1,14,15,3,2],![3,4,26,6,8]⟩
def cycle1412_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle1412_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle1412_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle1412_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data1412 : PartitionData E W := ⟨6,![cycle1412_0,cycle1412_1,cycle1412_2,cycle1412_3,cycle1412_4,cycle1412_5]⟩
lemma valid_data1412 : data1412.Valid src1412 dst1412 Finset.univ := by decide +kernel

def src1413 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst1413 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle1413_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1413_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,26,16]⟩
def cycle1413_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1413_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1413_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle1413_5 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle1413_6 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1413 : PartitionData E W := ⟨7,![cycle1413_0,cycle1413_1,cycle1413_2,cycle1413_3,cycle1413_4,cycle1413_5,cycle1413_6]⟩
lemma valid_data1413 : data1413.Valid src1413 dst1413 Finset.univ := by decide +kernel

def src1414 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst1414 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle1414_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1414_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1414_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle1414_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1414_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle1414_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1414 : PartitionData E W := ⟨6,![cycle1414_0,cycle1414_1,cycle1414_2,cycle1414_3,cycle1414_4,cycle1414_5]⟩
lemma valid_data1414 : data1414.Valid src1414 dst1414 Finset.univ := by decide +kernel

def src1415 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst1415 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle1415_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1415_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1415_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1415_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,27,14]⟩
def cycle1415_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,26]⟩
def cycle1415_5 : CycleData E W := ⟨2,![16,12,13,17],![16,27,28,26]⟩
def data1415 : PartitionData E W := ⟨6,![cycle1415_0,cycle1415_1,cycle1415_2,cycle1415_3,cycle1415_4,cycle1415_5]⟩
lemma valid_data1415 : data1415.Valid src1415 dst1415 Finset.univ := by decide +kernel

def src1416 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst1416 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle1416_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1416_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,27,16]⟩
def cycle1416_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1416_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1416_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle1416_5 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1416_6 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data1416 : PartitionData E W := ⟨7,![cycle1416_0,cycle1416_1,cycle1416_2,cycle1416_3,cycle1416_4,cycle1416_5,cycle1416_6]⟩
lemma valid_data1416 : data1416.Valid src1416 dst1416 Finset.univ := by decide +kernel

def src1417 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst1417 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle1417_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1417_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1417_2 : CycleData E W := ⟨3,![4,3,23,11,5],![2,6,8,28,14]⟩
def cycle1417_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,27]⟩
def cycle1417_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle1417_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1417 : PartitionData E W := ⟨6,![cycle1417_0,cycle1417_1,cycle1417_2,cycle1417_3,cycle1417_4,cycle1417_5]⟩
lemma valid_data1417 : data1417.Valid src1417 dst1417 Finset.univ := by decide +kernel

def src1418 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst1418 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle1418_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1418_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1418_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1418_3 : CycleData E W := ⟨3,![4,15,12,11,5],![2,6,26,28,14]⟩
def cycle1418_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,27]⟩
def cycle1418_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1418 : PartitionData E W := ⟨6,![cycle1418_0,cycle1418_1,cycle1418_2,cycle1418_3,cycle1418_4,cycle1418_5]⟩
lemma valid_data1418 : data1418.Valid src1418 dst1418 Finset.univ := by decide +kernel

def src1419 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst1419 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle1419_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1419_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1419_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1419_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1419_4 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1419_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data1419 : PartitionData E W := ⟨6,![cycle1419_0,cycle1419_1,cycle1419_2,cycle1419_3,cycle1419_4,cycle1419_5]⟩
lemma valid_data1419 : data1419.Valid src1419 dst1419 Finset.univ := by decide +kernel

def src1420 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst1420 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle1420_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1420_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1420_2 : CycleData E W := ⟨3,![4,3,23,11,5],![2,6,8,28,14]⟩
def cycle1420_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,27]⟩
def cycle1420_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle1420_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1420 : PartitionData E W := ⟨6,![cycle1420_0,cycle1420_1,cycle1420_2,cycle1420_3,cycle1420_4,cycle1420_5]⟩
lemma valid_data1420 : data1420.Valid src1420 dst1420 Finset.univ := by decide +kernel

def src1421 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst1421 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle1421_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1421_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1421_2 : CycleData E W := ⟨2,![3,20,12,15],![6,8,28,26]⟩
def cycle1421_3 : CycleData E W := ⟨3,![4,19,14,10,5],![2,6,27,4,14]⟩
def cycle1421_4 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1421_5 : CycleData E W := ⟨2,![16,13,18,17],![16,26,27,38]⟩
def data1421 : PartitionData E W := ⟨6,![cycle1421_0,cycle1421_1,cycle1421_2,cycle1421_3,cycle1421_4,cycle1421_5]⟩
lemma valid_data1421 : data1421.Valid src1421 dst1421 Finset.univ := by decide +kernel

def src1422 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst1422 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle1422_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1422_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1422_2 : CycleData E W := ⟨5,![4,3,23,16,14,10,5],![2,6,8,38,26,4,14]⟩
def cycle1422_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1422_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle1422_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1422 : PartitionData E W := ⟨6,![cycle1422_0,cycle1422_1,cycle1422_2,cycle1422_3,cycle1422_4,cycle1422_5]⟩
lemma valid_data1422 : data1422.Valid src1422 dst1422 Finset.univ := by decide +kernel

def src1423 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst1423 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle1423_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1423_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1423_2 : CycleData E W := ⟨3,![4,3,23,11,5],![2,6,8,28,14]⟩
def cycle1423_3 : CycleData E W := ⟨3,![10,6,21,16,14],![4,14,18,38,26]⟩
def cycle1423_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle1423_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1423 : PartitionData E W := ⟨6,![cycle1423_0,cycle1423_1,cycle1423_2,cycle1423_3,cycle1423_4,cycle1423_5]⟩
lemma valid_data1423 : data1423.Valid src1423 dst1423 Finset.univ := by decide +kernel

def src1424 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst1424 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle1424_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1424_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1424_2 : CycleData E W := ⟨2,![3,20,12,19],![6,8,28,27]⟩
def cycle1424_3 : CycleData E W := ⟨3,![4,15,14,10,5],![2,6,26,4,14]⟩
def cycle1424_4 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1424_5 : CycleData E W := ⟨2,![17,16,13,18],![16,38,26,27]⟩
def data1424 : PartitionData E W := ⟨6,![cycle1424_0,cycle1424_1,cycle1424_2,cycle1424_3,cycle1424_4,cycle1424_5]⟩
lemma valid_data1424 : data1424.Valid src1424 dst1424 Finset.univ := by decide +kernel

def src1425 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst1425 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle1425_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle1425_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,26,16]⟩
def cycle1425_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1425_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1425_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle1425_5 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle1425_6 : CycleData E W := ⟨2,![13,12,22,18],![26,27,28,38]⟩
def data1425 : PartitionData E W := ⟨7,![cycle1425_0,cycle1425_1,cycle1425_2,cycle1425_3,cycle1425_4,cycle1425_5,cycle1425_6]⟩
lemma valid_data1425 : data1425.Valid src1425 dst1425 Finset.univ := by decide +kernel

def src1426 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst1426 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle1426_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1426_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1426_2 : CycleData E W := ⟨3,![4,3,23,11,5],![2,6,8,28,14]⟩
def cycle1426_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,26]⟩
def cycle1426_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle1426_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1426 : PartitionData E W := ⟨6,![cycle1426_0,cycle1426_1,cycle1426_2,cycle1426_3,cycle1426_4,cycle1426_5]⟩
lemma valid_data1426 : data1426.Valid src1426 dst1426 Finset.univ := by decide +kernel

def src1427 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst1427 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle1427_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1427_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1427_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1427_3 : CycleData E W := ⟨3,![4,15,12,11,5],![2,6,27,28,14]⟩
def cycle1427_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,26]⟩
def cycle1427_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1427 : PartitionData E W := ⟨6,![cycle1427_0,cycle1427_1,cycle1427_2,cycle1427_3,cycle1427_4,cycle1427_5]⟩
lemma valid_data1427 : data1427.Valid src1427 dst1427 Finset.univ := by decide +kernel

def src1428 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst1428 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle1428_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1428_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1428_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,26,16]⟩
def cycle1428_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1428_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,26,14,18,28]⟩
def cycle1428_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1428 : PartitionData E W := ⟨6,![cycle1428_0,cycle1428_1,cycle1428_2,cycle1428_3,cycle1428_4,cycle1428_5]⟩
lemma valid_data1428 : data1428.Valid src1428 dst1428 Finset.univ := by decide +kernel

def src1429 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst1429 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle1429_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1429_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1429_2 : CycleData E W := ⟨4,![10,16,15,3,23,14],![4,26,16,6,8,28]⟩
def cycle1429_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1429_4 : CycleData E W := ⟨2,![6,21,17,11],![14,18,38,26]⟩
def cycle1429_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1429 : PartitionData E W := ⟨6,![cycle1429_0,cycle1429_1,cycle1429_2,cycle1429_3,cycle1429_4,cycle1429_5]⟩
lemma valid_data1429 : data1429.Valid src1429 dst1429 Finset.univ := by decide +kernel

def src1430 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst1430 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle1430_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1430_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1430_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1430_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1430_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def cycle1430_5 : CycleData E W := ⟨3,![7,22,17,16,8],![3,18,38,26,16]⟩
def data1430 : PartitionData E W := ⟨6,![cycle1430_0,cycle1430_1,cycle1430_2,cycle1430_3,cycle1430_4,cycle1430_5]⟩
lemma valid_data1430 : data1430.Valid src1430 dst1430 Finset.univ := by decide +kernel

def src1431 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst1431 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle1431_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1431_1 : CycleData E W := ⟨4,![2,20,21,13,16,8],![3,8,18,28,27,16]⟩
def cycle1431_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1431_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1431_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1431_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1431 : PartitionData E W := ⟨6,![cycle1431_0,cycle1431_1,cycle1431_2,cycle1431_3,cycle1431_4,cycle1431_5]⟩
lemma valid_data1431 : data1431.Valid src1431 dst1431 Finset.univ := by decide +kernel

def src1432 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst1432 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle1432_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1432_1 : CycleData E W := ⟨3,![2,23,13,16,8],![3,8,28,27,16]⟩
def cycle1432_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle1432_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1432_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1432_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1432 : PartitionData E W := ⟨6,![cycle1432_0,cycle1432_1,cycle1432_2,cycle1432_3,cycle1432_4,cycle1432_5]⟩
lemma valid_data1432 : data1432.Valid src1432 dst1432 Finset.univ := by decide +kernel

def src1433 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst1433 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle1433_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1433_1 : CycleData E W := ⟨3,![2,20,13,16,8],![3,8,28,27,16]⟩
def cycle1433_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1433_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1433_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle1433_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1433 : PartitionData E W := ⟨6,![cycle1433_0,cycle1433_1,cycle1433_2,cycle1433_3,cycle1433_4,cycle1433_5]⟩
lemma valid_data1433 : data1433.Valid src1433 dst1433 Finset.univ := by decide +kernel

def src1434 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst1434 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle1434_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1434_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1434_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,27,16]⟩
def cycle1434_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,26,14]⟩
def cycle1434_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def cycle1434_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data1434 : PartitionData E W := ⟨6,![cycle1434_0,cycle1434_1,cycle1434_2,cycle1434_3,cycle1434_4,cycle1434_5]⟩
lemma valid_data1434 : data1434.Valid src1434 dst1434 Finset.univ := by decide +kernel

def src1435 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst1435 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle1435_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1435_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1435_2 : CycleData E W := ⟨3,![3,23,13,16,15],![6,8,28,27,16]⟩
def cycle1435_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,26,14]⟩
def cycle1435_4 : CycleData E W := ⟨2,![6,21,17,12],![14,18,38,27]⟩
def cycle1435_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data1435 : PartitionData E W := ⟨6,![cycle1435_0,cycle1435_1,cycle1435_2,cycle1435_3,cycle1435_4,cycle1435_5]⟩
lemma valid_data1435 : data1435.Valid src1435 dst1435 Finset.univ := by decide +kernel

def src1436 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst1436 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle1436_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1436_1 : CycleData E W := ⟨3,![1,14,13,16,8],![3,4,28,27,16]⟩
def cycle1436_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1436_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1436_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1436_5 : CycleData E W := ⟨2,![6,22,17,12],![14,18,38,27]⟩
def data1436 : PartitionData E W := ⟨6,![cycle1436_0,cycle1436_1,cycle1436_2,cycle1436_3,cycle1436_4,cycle1436_5]⟩
lemma valid_data1436 : data1436.Valid src1436 dst1436 Finset.univ := by decide +kernel

def src1437 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst1437 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle1437_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1437_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1437_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle1437_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1437_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1437_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1437 : PartitionData E W := ⟨6,![cycle1437_0,cycle1437_1,cycle1437_2,cycle1437_3,cycle1437_4,cycle1437_5]⟩
lemma valid_data1437 : data1437.Valid src1437 dst1437 Finset.univ := by decide +kernel

def src1438 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst1438 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle1438_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1438_1 : CycleData E W := ⟨3,![2,20,21,16,8],![3,8,18,38,16]⟩
def cycle1438_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1438_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1438_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1438_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1438 : PartitionData E W := ⟨6,![cycle1438_0,cycle1438_1,cycle1438_2,cycle1438_3,cycle1438_4,cycle1438_5]⟩
lemma valid_data1438 : data1438.Valid src1438 dst1438 Finset.univ := by decide +kernel

def src1439 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst1439 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle1439_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1439_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1439_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1439_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1439_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,26,38,18,28]⟩
def cycle1439_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1439 : PartitionData E W := ⟨6,![cycle1439_0,cycle1439_1,cycle1439_2,cycle1439_3,cycle1439_4,cycle1439_5]⟩
lemma valid_data1439 : data1439.Valid src1439 dst1439 Finset.univ := by decide +kernel

def src1440 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst1440 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle1440_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1440_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1440_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1440_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1440_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,26,14,18,28]⟩
def cycle1440_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1440 : PartitionData E W := ⟨6,![cycle1440_0,cycle1440_1,cycle1440_2,cycle1440_3,cycle1440_4,cycle1440_5]⟩
lemma valid_data1440 : data1440.Valid src1440 dst1440 Finset.univ := by decide +kernel

def src1441 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst1441 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle1441_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1441_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1441_2 : CycleData E W := ⟨3,![10,15,3,23,14],![4,26,6,8,28]⟩
def cycle1441_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1441_4 : CycleData E W := ⟨3,![6,21,17,16,11],![14,18,38,16,26]⟩
def cycle1441_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1441 : PartitionData E W := ⟨6,![cycle1441_0,cycle1441_1,cycle1441_2,cycle1441_3,cycle1441_4,cycle1441_5]⟩
lemma valid_data1441 : data1441.Valid src1441 dst1441 Finset.univ := by decide +kernel

def src1442 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst1442 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle1442_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1442_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1442_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1442_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle1442_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def cycle1442_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data1442 : PartitionData E W := ⟨6,![cycle1442_0,cycle1442_1,cycle1442_2,cycle1442_3,cycle1442_4,cycle1442_5]⟩
lemma valid_data1442 : data1442.Valid src1442 dst1442 Finset.univ := by decide +kernel

def src1443 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst1443 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1443_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1443_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1443_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1443_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1443_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,26,14,18,28]⟩
def cycle1443_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1443 : PartitionData E W := ⟨6,![cycle1443_0,cycle1443_1,cycle1443_2,cycle1443_3,cycle1443_4,cycle1443_5]⟩
lemma valid_data1443 : data1443.Valid src1443 dst1443 Finset.univ := by decide +kernel

def src1444 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst1444 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle1444_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1444_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1444_2 : CycleData E W := ⟨3,![10,15,3,23,14],![4,26,6,8,28]⟩
def cycle1444_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1444_4 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle1444_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1444 : PartitionData E W := ⟨6,![cycle1444_0,cycle1444_1,cycle1444_2,cycle1444_3,cycle1444_4,cycle1444_5]⟩
lemma valid_data1444 : data1444.Valid src1444 dst1444 Finset.univ := by decide +kernel

def src1445 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst1445 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle1445_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1445_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1445_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1445_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle1445_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,27]⟩
def cycle1445_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data1445 : PartitionData E W := ⟨6,![cycle1445_0,cycle1445_1,cycle1445_2,cycle1445_3,cycle1445_4,cycle1445_5]⟩
lemma valid_data1445 : data1445.Valid src1445 dst1445 Finset.univ := by decide +kernel

def src1446 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst1446 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle1446_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1446_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1446_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1446_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1446_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,26,14,18,28]⟩
def cycle1446_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data1446 : PartitionData E W := ⟨6,![cycle1446_0,cycle1446_1,cycle1446_2,cycle1446_3,cycle1446_4,cycle1446_5]⟩
lemma valid_data1446 : data1446.Valid src1446 dst1446 Finset.univ := by decide +kernel

def src1447 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst1447 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle1447_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1447_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1447_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1447_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1447_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1447_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data1447 : PartitionData E W := ⟨6,![cycle1447_0,cycle1447_1,cycle1447_2,cycle1447_3,cycle1447_4,cycle1447_5]⟩
lemma valid_data1447 : data1447.Valid src1447 dst1447 Finset.univ := by decide +kernel

def src1448 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst1448 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle1448_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1448_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1448_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1448_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1448_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle1448_5 : CycleData E W := ⟨3,![10,17,16,13,14],![4,26,16,27,28]⟩
def data1448 : PartitionData E W := ⟨6,![cycle1448_0,cycle1448_1,cycle1448_2,cycle1448_3,cycle1448_4,cycle1448_5]⟩
lemma valid_data1448 : data1448.Valid src1448 dst1448 Finset.univ := by decide +kernel

def src1449 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst1449 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle1449_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1449_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1449_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1449_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1449_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,26,14,18,28]⟩
def cycle1449_5 : CycleData E W := ⟨3,![17,16,13,22,18],![16,26,27,28,38]⟩
def data1449 : PartitionData E W := ⟨6,![cycle1449_0,cycle1449_1,cycle1449_2,cycle1449_3,cycle1449_4,cycle1449_5]⟩
lemma valid_data1449 : data1449.Valid src1449 dst1449 Finset.univ := by decide +kernel

def src1450 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst1450 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle1450_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1450_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1450_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1450_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1450_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,26,16,38,28]⟩
def cycle1450_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data1450 : PartitionData E W := ⟨6,![cycle1450_0,cycle1450_1,cycle1450_2,cycle1450_3,cycle1450_4,cycle1450_5]⟩
lemma valid_data1450 : data1450.Valid src1450 dst1450 Finset.univ := by decide +kernel

def src1451 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst1451 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle1451_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1451_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1451_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1451_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1451_4 : CycleData E W := ⟨3,![6,22,18,17,11],![14,18,38,16,26]⟩
def cycle1451_5 : CycleData E W := ⟨2,![10,16,13,14],![4,26,27,28]⟩
def data1451 : PartitionData E W := ⟨6,![cycle1451_0,cycle1451_1,cycle1451_2,cycle1451_3,cycle1451_4,cycle1451_5]⟩
lemma valid_data1451 : data1451.Valid src1451 dst1451 Finset.univ := by decide +kernel

def src1452 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst1452 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle1452_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1452_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1452_2 : CycleData E W := ⟨4,![4,3,23,17,11,5],![2,6,8,38,26,14]⟩
def cycle1452_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1452_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle1452_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1452 : PartitionData E W := ⟨6,![cycle1452_0,cycle1452_1,cycle1452_2,cycle1452_3,cycle1452_4,cycle1452_5]⟩
lemma valid_data1452 : data1452.Valid src1452 dst1452 Finset.univ := by decide +kernel

def src1453 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst1453 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle1453_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1453_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1453_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1453_3 : CycleData E W := ⟨2,![6,21,17,11],![14,18,38,26]⟩
def cycle1453_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle1453_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1453 : PartitionData E W := ⟨6,![cycle1453_0,cycle1453_1,cycle1453_2,cycle1453_3,cycle1453_4,cycle1453_5]⟩
lemma valid_data1453 : data1453.Valid src1453 dst1453 Finset.univ := by decide +kernel

def src1454 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst1454 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle1454_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1454_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1454_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1454_3 : CycleData E W := ⟨3,![4,15,16,11,5],![2,6,16,26,14]⟩
def cycle1454_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1454_5 : CycleData E W := ⟨2,![10,17,18,14],![4,26,38,27]⟩
def data1454 : PartitionData E W := ⟨6,![cycle1454_0,cycle1454_1,cycle1454_2,cycle1454_3,cycle1454_4,cycle1454_5]⟩
lemma valid_data1454 : data1454.Valid src1454 dst1454 Finset.univ := by decide +kernel

def src1455 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst1455 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle1455_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1455_1 : CycleData E W := ⟨2,![1,14,16,8],![3,4,27,16]⟩
def cycle1455_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1455_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1455_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1455_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1455_6 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data1455 : PartitionData E W := ⟨7,![cycle1455_0,cycle1455_1,cycle1455_2,cycle1455_3,cycle1455_4,cycle1455_5,cycle1455_6]⟩
lemma valid_data1455 : data1455.Valid src1455 dst1455 Finset.univ := by decide +kernel

def src1456 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst1456 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle1456_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1456_1 : CycleData E W := ⟨3,![2,23,13,16,8],![3,8,28,27,16]⟩
def cycle1456_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle1456_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1456_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1456_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data1456 : PartitionData E W := ⟨6,![cycle1456_0,cycle1456_1,cycle1456_2,cycle1456_3,cycle1456_4,cycle1456_5]⟩
lemma valid_data1456 : data1456.Valid src1456 dst1456 Finset.univ := by decide +kernel

def src1457 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst1457 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle1457_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1457_1 : CycleData E W := ⟨3,![2,20,13,16,8],![3,8,28,27,16]⟩
def cycle1457_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1457_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1457_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1457_5 : CycleData E W := ⟨3,![11,18,22,21,12],![14,26,38,18,28]⟩
def data1457 : PartitionData E W := ⟨6,![cycle1457_0,cycle1457_1,cycle1457_2,cycle1457_3,cycle1457_4,cycle1457_5]⟩
lemma valid_data1457 : data1457.Valid src1457 dst1457 Finset.univ := by decide +kernel

def src1458 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst1458 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle1458_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle1458_1 : CycleData E W := ⟨2,![1,14,16,8],![3,4,27,16]⟩
def cycle1458_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1458_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1458_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1458_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1458_6 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1458 : PartitionData E W := ⟨7,![cycle1458_0,cycle1458_1,cycle1458_2,cycle1458_3,cycle1458_4,cycle1458_5,cycle1458_6]⟩
lemma valid_data1458 : data1458.Valid src1458 dst1458 Finset.univ := by decide +kernel

def src1459 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst1459 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle1459_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1459_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1459_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1459_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle1459_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle1459_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1459 : PartitionData E W := ⟨6,![cycle1459_0,cycle1459_1,cycle1459_2,cycle1459_3,cycle1459_4,cycle1459_5]⟩
lemma valid_data1459 : data1459.Valid src1459 dst1459 Finset.univ := by decide +kernel

def src1460 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst1460 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle1460_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1460_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1460_2 : CycleData E W := ⟨3,![3,20,13,16,15],![6,8,28,27,16]⟩
def cycle1460_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,26,14]⟩
def cycle1460_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1460_5 : CycleData E W := ⟨2,![10,18,17,14],![4,26,38,27]⟩
def data1460 : PartitionData E W := ⟨6,![cycle1460_0,cycle1460_1,cycle1460_2,cycle1460_3,cycle1460_4,cycle1460_5]⟩
lemma valid_data1460 : data1460.Valid src1460 dst1460 Finset.univ := by decide +kernel

def src1461 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst1461 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle1461_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1461_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1461_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle1461_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1461_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1461_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data1461 : PartitionData E W := ⟨6,![cycle1461_0,cycle1461_1,cycle1461_2,cycle1461_3,cycle1461_4,cycle1461_5]⟩
lemma valid_data1461 : data1461.Valid src1461 dst1461 Finset.univ := by decide +kernel

def src1462 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst1462 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle1462_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1462_1 : CycleData E W := ⟨3,![2,20,21,16,8],![3,8,18,38,16]⟩
def cycle1462_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1462_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1462_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1462_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data1462 : PartitionData E W := ⟨6,![cycle1462_0,cycle1462_1,cycle1462_2,cycle1462_3,cycle1462_4,cycle1462_5]⟩
lemma valid_data1462 : data1462.Valid src1462 dst1462 Finset.univ := by decide +kernel

def src1463 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst1463 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle1463_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1463_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1463_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1463_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1463_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1463_5 : CycleData E W := ⟨3,![11,17,22,21,12],![14,26,38,18,28]⟩
def data1463 : PartitionData E W := ⟨6,![cycle1463_0,cycle1463_1,cycle1463_2,cycle1463_3,cycle1463_4,cycle1463_5]⟩
lemma valid_data1463 : data1463.Valid src1463 dst1463 Finset.univ := by decide +kernel

def src1464 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst1464 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle1464_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1464_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1464_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1464_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1464_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1464_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1464_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1464 : PartitionData E W := ⟨7,![cycle1464_0,cycle1464_1,cycle1464_2,cycle1464_3,cycle1464_4,cycle1464_5,cycle1464_6]⟩
lemma valid_data1464 : data1464.Valid src1464 dst1464 Finset.univ := by decide +kernel

def src1465 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst1465 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle1465_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1465_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1465_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1465_3 : CycleData E W := ⟨3,![15,11,6,21,19],![6,26,14,18,38]⟩
def cycle1465_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1465_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1465 : PartitionData E W := ⟨6,![cycle1465_0,cycle1465_1,cycle1465_2,cycle1465_3,cycle1465_4,cycle1465_5]⟩
lemma valid_data1465 : data1465.Valid src1465 dst1465 Finset.univ := by decide +kernel

def src1466 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst1466 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle1466_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1466_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,18]⟩
def cycle1466_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1466_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1466_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1466_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data1466 : PartitionData E W := ⟨6,![cycle1466_0,cycle1466_1,cycle1466_2,cycle1466_3,cycle1466_4,cycle1466_5]⟩
lemma valid_data1466 : data1466.Valid src1466 dst1466 Finset.univ := by decide +kernel

def src1467 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst1467 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle1467_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1467_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1467_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1467_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1467_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1467_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1467_6 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data1467 : PartitionData E W := ⟨7,![cycle1467_0,cycle1467_1,cycle1467_2,cycle1467_3,cycle1467_4,cycle1467_5,cycle1467_6]⟩
lemma valid_data1467 : data1467.Valid src1467 dst1467 Finset.univ := by decide +kernel

def src1468 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst1468 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle1468_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1468_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1468_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1468_3 : CycleData E W := ⟨3,![15,11,6,21,19],![6,26,14,18,38]⟩
def cycle1468_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1468_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data1468 : PartitionData E W := ⟨6,![cycle1468_0,cycle1468_1,cycle1468_2,cycle1468_3,cycle1468_4,cycle1468_5]⟩
lemma valid_data1468 : data1468.Valid src1468 dst1468 Finset.univ := by decide +kernel

def src1469 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst1469 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle1469_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1469_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,18]⟩
def cycle1469_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1469_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1469_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1469_5 : CycleData E W := ⟨3,![17,13,21,22,18],![16,27,28,18,38]⟩
def data1469 : PartitionData E W := ⟨6,![cycle1469_0,cycle1469_1,cycle1469_2,cycle1469_3,cycle1469_4,cycle1469_5]⟩
lemma valid_data1469 : data1469.Valid src1469 dst1469 Finset.univ := by decide +kernel

def src1470 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst1470 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1470_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1470_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1470_2 : CycleData E W := ⟨4,![4,3,23,16,11,5],![2,6,8,38,26,14]⟩
def cycle1470_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1470_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1470_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1470 : PartitionData E W := ⟨6,![cycle1470_0,cycle1470_1,cycle1470_2,cycle1470_3,cycle1470_4,cycle1470_5]⟩
lemma valid_data1470 : data1470.Valid src1470 dst1470 Finset.univ := by decide +kernel

def src1471 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst1471 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1471_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1471_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1471_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1471_3 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle1471_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1471_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1471 : PartitionData E W := ⟨6,![cycle1471_0,cycle1471_1,cycle1471_2,cycle1471_3,cycle1471_4,cycle1471_5]⟩
lemma valid_data1471 : data1471.Valid src1471 dst1471 Finset.univ := by decide +kernel

def src1472 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst1472 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1472_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1472_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1472_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1472_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle1472_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1472_5 : CycleData E W := ⟨3,![10,16,17,18,14],![4,26,38,16,27]⟩
def data1472 : PartitionData E W := ⟨6,![cycle1472_0,cycle1472_1,cycle1472_2,cycle1472_3,cycle1472_4,cycle1472_5]⟩
lemma valid_data1472 : data1472.Valid src1472 dst1472 Finset.univ := by decide +kernel

def src1473 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst1473 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1473_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1473_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1473_2 : CycleData E W := ⟨4,![4,3,23,18,11,5],![2,6,8,38,26,14]⟩
def cycle1473_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1473_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1473_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data1473 : PartitionData E W := ⟨6,![cycle1473_0,cycle1473_1,cycle1473_2,cycle1473_3,cycle1473_4,cycle1473_5]⟩
lemma valid_data1473 : data1473.Valid src1473 dst1473 Finset.univ := by decide +kernel

def src1474 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst1474 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1474_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1474_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1474_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1474_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle1474_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1474_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data1474 : PartitionData E W := ⟨6,![cycle1474_0,cycle1474_1,cycle1474_2,cycle1474_3,cycle1474_4,cycle1474_5]⟩
lemma valid_data1474 : data1474.Valid src1474 dst1474 Finset.univ := by decide +kernel

def src1475 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst1475 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1475_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1475_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1475_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1475_3 : CycleData E W := ⟨3,![4,15,13,12,5],![2,6,27,28,14]⟩
def cycle1475_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle1475_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def data1475 : PartitionData E W := ⟨6,![cycle1475_0,cycle1475_1,cycle1475_2,cycle1475_3,cycle1475_4,cycle1475_5]⟩
lemma valid_data1475 : data1475.Valid src1475 dst1475 Finset.univ := by decide +kernel

def src1476 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst1476 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle1476_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1476_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1476_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1476_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1476_4 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1476_5 : CycleData E W := ⟨3,![10,11,18,22,14],![4,26,27,38,28]⟩
def data1476 : PartitionData E W := ⟨6,![cycle1476_0,cycle1476_1,cycle1476_2,cycle1476_3,cycle1476_4,cycle1476_5]⟩
lemma valid_data1476 : data1476.Valid src1476 dst1476 Finset.univ := by decide +kernel

def src1477 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst1477 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle1477_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1477_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1477_2 : CycleData E W := ⟨3,![4,3,23,13,5],![2,6,8,28,14]⟩
def cycle1477_3 : CycleData E W := ⟨2,![6,21,18,12],![14,18,38,27]⟩
def cycle1477_4 : CycleData E W := ⟨3,![10,16,17,22,14],![4,26,16,38,28]⟩
def cycle1477_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data1477 : PartitionData E W := ⟨6,![cycle1477_0,cycle1477_1,cycle1477_2,cycle1477_3,cycle1477_4,cycle1477_5]⟩
lemma valid_data1477 : data1477.Valid src1477 dst1477 Finset.univ := by decide +kernel

def src1478 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst1478 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle1478_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1478_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1478_2 : CycleData E W := ⟨3,![10,15,3,20,14],![4,26,6,8,28]⟩
def cycle1478_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,27,14]⟩
def cycle1478_4 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1478_5 : CycleData E W := ⟨2,![16,11,18,17],![16,26,27,38]⟩
def data1478 : PartitionData E W := ⟨6,![cycle1478_0,cycle1478_1,cycle1478_2,cycle1478_3,cycle1478_4,cycle1478_5]⟩
lemma valid_data1478 : data1478.Valid src1478 dst1478 Finset.univ := by decide +kernel

def src1479 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst1479 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle1479_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1479_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1479_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1479_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1479_4 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1479_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1479_6 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1479 : PartitionData E W := ⟨7,![cycle1479_0,cycle1479_1,cycle1479_2,cycle1479_3,cycle1479_4,cycle1479_5,cycle1479_6]⟩
lemma valid_data1479 : data1479.Valid src1479 dst1479 Finset.univ := by decide +kernel

def src1480 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst1480 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle1480_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1480_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1480_2 : CycleData E W := ⟨3,![4,3,23,13,5],![2,6,8,28,14]⟩
def cycle1480_3 : CycleData E W := ⟨3,![15,12,6,21,19],![6,27,14,18,38]⟩
def cycle1480_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1480_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1480 : PartitionData E W := ⟨6,![cycle1480_0,cycle1480_1,cycle1480_2,cycle1480_3,cycle1480_4,cycle1480_5]⟩
lemma valid_data1480 : data1480.Valid src1480 dst1480 Finset.univ := by decide +kernel

def src1481 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst1481 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle1481_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1481_1 : CycleData E W := ⟨3,![2,20,13,6,7],![3,8,28,14,18]⟩
def cycle1481_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1481_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle1481_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle1481_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data1481 : PartitionData E W := ⟨6,![cycle1481_0,cycle1481_1,cycle1481_2,cycle1481_3,cycle1481_4,cycle1481_5]⟩
lemma valid_data1481 : data1481.Valid src1481 dst1481 Finset.univ := by decide +kernel

def src1482 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst1482 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle1482_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1482_1 : CycleData E W := ⟨2,![1,10,16,8],![3,4,26,16]⟩
def cycle1482_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1482_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1482_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1482_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1482_6 : CycleData E W := ⟨2,![11,22,18,17],![26,28,38,27]⟩
def data1482 : PartitionData E W := ⟨7,![cycle1482_0,cycle1482_1,cycle1482_2,cycle1482_3,cycle1482_4,cycle1482_5,cycle1482_6]⟩
lemma valid_data1482 : data1482.Valid src1482 dst1482 Finset.univ := by decide +kernel

def src1483 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst1483 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle1483_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1483_1 : CycleData E W := ⟨3,![2,23,11,16,8],![3,8,28,26,16]⟩
def cycle1483_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle1483_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1483_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1483_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data1483 : PartitionData E W := ⟨6,![cycle1483_0,cycle1483_1,cycle1483_2,cycle1483_3,cycle1483_4,cycle1483_5]⟩
lemma valid_data1483 : data1483.Valid src1483 dst1483 Finset.univ := by decide +kernel

def src1484 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst1484 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle1484_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1484_1 : CycleData E W := ⟨3,![2,20,11,16,8],![3,8,28,26,16]⟩
def cycle1484_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1484_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1484_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle1484_5 : CycleData E W := ⟨3,![12,21,22,18,13],![14,28,18,38,27]⟩
def data1484 : PartitionData E W := ⟨6,![cycle1484_0,cycle1484_1,cycle1484_2,cycle1484_3,cycle1484_4,cycle1484_5]⟩
lemma valid_data1484 : data1484.Valid src1484 dst1484 Finset.univ := by decide +kernel

def src1485 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst1485 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle1485_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle1485_1 : CycleData E W := ⟨2,![1,10,16,8],![3,4,26,16]⟩
def cycle1485_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1485_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1485_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1485_5 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1485_6 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data1485 : PartitionData E W := ⟨7,![cycle1485_0,cycle1485_1,cycle1485_2,cycle1485_3,cycle1485_4,cycle1485_5,cycle1485_6]⟩
lemma valid_data1485 : data1485.Valid src1485 dst1485 Finset.univ := by decide +kernel

def src1486 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst1486 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle1486_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1486_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1486_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1486_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle1486_4 : CycleData E W := ⟨3,![10,16,15,19,14],![4,26,16,6,27]⟩
def cycle1486_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data1486 : PartitionData E W := ⟨6,![cycle1486_0,cycle1486_1,cycle1486_2,cycle1486_3,cycle1486_4,cycle1486_5]⟩
lemma valid_data1486 : data1486.Valid src1486 dst1486 Finset.univ := by decide +kernel

def src1487 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst1487 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle1487_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1487_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1487_2 : CycleData E W := ⟨3,![3,20,11,16,15],![6,8,28,26,16]⟩
def cycle1487_3 : CycleData E W := ⟨2,![4,19,13,5],![2,6,27,14]⟩
def cycle1487_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1487_5 : CycleData E W := ⟨2,![10,17,18,14],![4,26,38,27]⟩
def data1487 : PartitionData E W := ⟨6,![cycle1487_0,cycle1487_1,cycle1487_2,cycle1487_3,cycle1487_4,cycle1487_5]⟩
lemma valid_data1487 : data1487.Valid src1487 dst1487 Finset.univ := by decide +kernel

def src1488 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst1488 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle1488_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1488_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1488_2 : CycleData E W := ⟨4,![4,3,23,17,13,5],![2,6,8,38,27,14]⟩
def cycle1488_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1488_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle1488_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1488 : PartitionData E W := ⟨6,![cycle1488_0,cycle1488_1,cycle1488_2,cycle1488_3,cycle1488_4,cycle1488_5]⟩
lemma valid_data1488 : data1488.Valid src1488 dst1488 Finset.univ := by decide +kernel

def src1489 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst1489 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle1489_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1489_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1489_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1489_3 : CycleData E W := ⟨2,![6,21,17,13],![14,18,38,27]⟩
def cycle1489_4 : CycleData E W := ⟨3,![10,19,15,16,14],![4,26,6,16,27]⟩
def cycle1489_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1489 : PartitionData E W := ⟨6,![cycle1489_0,cycle1489_1,cycle1489_2,cycle1489_3,cycle1489_4,cycle1489_5]⟩
lemma valid_data1489 : data1489.Valid src1489 dst1489 Finset.univ := by decide +kernel

def src1490 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst1490 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle1490_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1490_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1490_2 : CycleData E W := ⟨2,![3,20,11,19],![6,8,28,26]⟩
def cycle1490_3 : CycleData E W := ⟨3,![4,15,16,13,5],![2,6,16,27,14]⟩
def cycle1490_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1490_5 : CycleData E W := ⟨2,![10,18,17,14],![4,26,38,27]⟩
def data1490 : PartitionData E W := ⟨6,![cycle1490_0,cycle1490_1,cycle1490_2,cycle1490_3,cycle1490_4,cycle1490_5]⟩
lemma valid_data1490 : data1490.Valid src1490 dst1490 Finset.univ := by decide +kernel

def src1491 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst1491 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle1491_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1491_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1491_2 : CycleData E W := ⟨3,![3,20,21,11,19],![6,8,18,28,26]⟩
def cycle1491_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1491_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1491_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data1491 : PartitionData E W := ⟨6,![cycle1491_0,cycle1491_1,cycle1491_2,cycle1491_3,cycle1491_4,cycle1491_5]⟩
lemma valid_data1491 : data1491.Valid src1491 dst1491 Finset.univ := by decide +kernel

def src1492 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst1492 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle1492_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1492_1 : CycleData E W := ⟨3,![2,20,21,16,8],![3,8,18,38,16]⟩
def cycle1492_2 : CycleData E W := ⟨2,![3,23,11,19],![6,8,28,26]⟩
def cycle1492_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1492_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1492_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data1492 : PartitionData E W := ⟨6,![cycle1492_0,cycle1492_1,cycle1492_2,cycle1492_3,cycle1492_4,cycle1492_5]⟩
lemma valid_data1492 : data1492.Valid src1492 dst1492 Finset.univ := by decide +kernel

def src1493 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst1493 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle1493_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1493_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1493_2 : CycleData E W := ⟨2,![3,20,11,19],![6,8,28,26]⟩
def cycle1493_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1493_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle1493_5 : CycleData E W := ⟨3,![12,21,22,17,13],![14,28,18,38,27]⟩
def data1493 : PartitionData E W := ⟨6,![cycle1493_0,cycle1493_1,cycle1493_2,cycle1493_3,cycle1493_4,cycle1493_5]⟩
lemma valid_data1493 : data1493.Valid src1493 dst1493 Finset.univ := by decide +kernel

def src1494 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst1494 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle1494_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1494_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1494_2 : CycleData E W := ⟨4,![4,3,23,18,13,5],![2,6,8,38,27,14]⟩
def cycle1494_3 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1494_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1494_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data1494 : PartitionData E W := ⟨6,![cycle1494_0,cycle1494_1,cycle1494_2,cycle1494_3,cycle1494_4,cycle1494_5]⟩
lemma valid_data1494 : data1494.Valid src1494 dst1494 Finset.univ := by decide +kernel

def src1495 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst1495 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle1495_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1495_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1495_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1495_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle1495_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle1495_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data1495 : PartitionData E W := ⟨6,![cycle1495_0,cycle1495_1,cycle1495_2,cycle1495_3,cycle1495_4,cycle1495_5]⟩
lemma valid_data1495 : data1495.Valid src1495 dst1495 Finset.univ := by decide +kernel

def src1496 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst1496 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle1496_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1496_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1496_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1496_3 : CycleData E W := ⟨3,![4,15,11,12,5],![2,6,26,28,14]⟩
def cycle1496_4 : CycleData E W := ⟨2,![6,22,18,13],![14,18,38,27]⟩
def cycle1496_5 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def data1496 : PartitionData E W := ⟨6,![cycle1496_0,cycle1496_1,cycle1496_2,cycle1496_3,cycle1496_4,cycle1496_5]⟩
lemma valid_data1496 : data1496.Valid src1496 dst1496 Finset.univ := by decide +kernel

def src1497 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst1497 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle1497_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1497_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1497_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1497_3 : CycleData E W := ⟨2,![4,19,13,5],![2,6,27,14]⟩
def cycle1497_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1497_5 : CycleData E W := ⟨3,![10,11,22,18,14],![4,26,28,38,27]⟩
def data1497 : PartitionData E W := ⟨6,![cycle1497_0,cycle1497_1,cycle1497_2,cycle1497_3,cycle1497_4,cycle1497_5]⟩
lemma valid_data1497 : data1497.Valid src1497 dst1497 Finset.univ := by decide +kernel

def src1498 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst1498 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle1498_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1498_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1498_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1498_3 : CycleData E W := ⟨2,![6,21,18,13],![14,18,38,27]⟩
def cycle1498_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle1498_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data1498 : PartitionData E W := ⟨6,![cycle1498_0,cycle1498_1,cycle1498_2,cycle1498_3,cycle1498_4,cycle1498_5]⟩
lemma valid_data1498 : data1498.Valid src1498 dst1498 Finset.univ := by decide +kernel

def src1499 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst1499 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle1499_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1499_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1499_2 : CycleData E W := ⟨2,![3,20,11,15],![6,8,28,26]⟩
def cycle1499_3 : CycleData E W := ⟨2,![4,19,13,5],![2,6,27,14]⟩
def cycle1499_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1499_5 : CycleData E W := ⟨3,![10,16,17,18,14],![4,26,16,38,27]⟩
def data1499 : PartitionData E W := ⟨6,![cycle1499_0,cycle1499_1,cycle1499_2,cycle1499_3,cycle1499_4,cycle1499_5]⟩
lemma valid_data1499 : data1499.Valid src1499 dst1499 Finset.univ := by decide +kernel

def src1500 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst1500 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle1500_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1500_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1500_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1500_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1500_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1500_5 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1500_6 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1500 : PartitionData E W := ⟨7,![cycle1500_0,cycle1500_1,cycle1500_2,cycle1500_3,cycle1500_4,cycle1500_5,cycle1500_6]⟩
lemma valid_data1500 : data1500.Valid src1500 dst1500 Finset.univ := by decide +kernel

def src1501 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst1501 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle1501_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1501_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1501_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1501_3 : CycleData E W := ⟨3,![15,13,6,21,19],![6,27,14,18,38]⟩
def cycle1501_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1501_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data1501 : PartitionData E W := ⟨6,![cycle1501_0,cycle1501_1,cycle1501_2,cycle1501_3,cycle1501_4,cycle1501_5]⟩
lemma valid_data1501 : data1501.Valid src1501 dst1501 Finset.univ := by decide +kernel

def src1502 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst1502 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle1502_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1502_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,18]⟩
def cycle1502_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1502_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1502_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle1502_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data1502 : PartitionData E W := ⟨6,![cycle1502_0,cycle1502_1,cycle1502_2,cycle1502_3,cycle1502_4,cycle1502_5]⟩
lemma valid_data1502 : data1502.Valid src1502 dst1502 Finset.univ := by decide +kernel

def src1503 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst1503 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle1503_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1503_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1503_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1503_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1503_4 : CycleData E W := ⟨1,![6,21,12],![14,18,28]⟩
def cycle1503_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1503_6 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data1503 : PartitionData E W := ⟨7,![cycle1503_0,cycle1503_1,cycle1503_2,cycle1503_3,cycle1503_4,cycle1503_5,cycle1503_6]⟩
lemma valid_data1503 : data1503.Valid src1503 dst1503 Finset.univ := by decide +kernel

def src1504 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst1504 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle1504_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1504_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1504_2 : CycleData E W := ⟨3,![4,3,23,12,5],![2,6,8,28,14]⟩
def cycle1504_3 : CycleData E W := ⟨3,![15,13,6,21,19],![6,27,14,18,38]⟩
def cycle1504_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1504_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data1504 : PartitionData E W := ⟨6,![cycle1504_0,cycle1504_1,cycle1504_2,cycle1504_3,cycle1504_4,cycle1504_5]⟩
lemma valid_data1504 : data1504.Valid src1504 dst1504 Finset.univ := by decide +kernel

def src1505 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst1505 : E → W := ![4,3,8,6,2,14,18,3,16,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle1505_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1505_1 : CycleData E W := ⟨3,![2,20,12,6,7],![3,8,28,14,18]⟩
def cycle1505_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1505_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle1505_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle1505_5 : CycleData E W := ⟨3,![17,11,21,22,18],![16,26,28,18,38]⟩
def data1505 : PartitionData E W := ⟨6,![cycle1505_0,cycle1505_1,cycle1505_2,cycle1505_3,cycle1505_4,cycle1505_5]⟩
lemma valid_data1505 : data1505.Valid src1505 dst1505 Finset.univ := by decide +kernel

def src1506 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst1506 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle1506_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1506_1 : CycleData E W := ⟨4,![2,20,21,13,16,8],![3,8,18,28,26,16]⟩
def cycle1506_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1506_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1506_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1506_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1506 : PartitionData E W := ⟨6,![cycle1506_0,cycle1506_1,cycle1506_2,cycle1506_3,cycle1506_4,cycle1506_5]⟩
lemma valid_data1506 : data1506.Valid src1506 dst1506 Finset.univ := by decide +kernel

def src1507 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst1507 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle1507_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1507_1 : CycleData E W := ⟨3,![2,23,13,16,8],![3,8,28,26,16]⟩
def cycle1507_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle1507_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1507_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1507_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1507 : PartitionData E W := ⟨6,![cycle1507_0,cycle1507_1,cycle1507_2,cycle1507_3,cycle1507_4,cycle1507_5]⟩
lemma valid_data1507 : data1507.Valid src1507 dst1507 Finset.univ := by decide +kernel

def src1508 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst1508 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle1508_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1508_1 : CycleData E W := ⟨3,![2,20,13,16,8],![3,8,28,26,16]⟩
def cycle1508_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1508_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1508_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def cycle1508_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data1508 : PartitionData E W := ⟨6,![cycle1508_0,cycle1508_1,cycle1508_2,cycle1508_3,cycle1508_4,cycle1508_5]⟩
lemma valid_data1508 : data1508.Valid src1508 dst1508 Finset.univ := by decide +kernel

def src1509 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst1509 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle1509_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1509_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1509_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,26,16]⟩
def cycle1509_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1509_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1509_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1509 : PartitionData E W := ⟨6,![cycle1509_0,cycle1509_1,cycle1509_2,cycle1509_3,cycle1509_4,cycle1509_5]⟩
lemma valid_data1509 : data1509.Valid src1509 dst1509 Finset.univ := by decide +kernel

def src1510 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst1510 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle1510_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1510_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1510_2 : CycleData E W := ⟨3,![3,23,13,16,15],![6,8,28,26,16]⟩
def cycle1510_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1510_4 : CycleData E W := ⟨2,![6,21,17,12],![14,18,38,26]⟩
def cycle1510_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1510 : PartitionData E W := ⟨6,![cycle1510_0,cycle1510_1,cycle1510_2,cycle1510_3,cycle1510_4,cycle1510_5]⟩
lemma valid_data1510 : data1510.Valid src1510 dst1510 Finset.univ := by decide +kernel

def src1511 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst1511 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle1511_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1511_1 : CycleData E W := ⟨3,![1,14,13,16,8],![3,4,28,26,16]⟩
def cycle1511_2 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1511_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1511_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1511_5 : CycleData E W := ⟨2,![6,22,17,12],![14,18,38,26]⟩
def data1511 : PartitionData E W := ⟨6,![cycle1511_0,cycle1511_1,cycle1511_2,cycle1511_3,cycle1511_4,cycle1511_5]⟩
lemma valid_data1511 : data1511.Valid src1511 dst1511 Finset.univ := by decide +kernel

def src1512 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst1512 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle1512_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1512_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1512_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,27,16]⟩
def cycle1512_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,26,14]⟩
def cycle1512_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,27,14,18,28]⟩
def cycle1512_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1512 : PartitionData E W := ⟨6,![cycle1512_0,cycle1512_1,cycle1512_2,cycle1512_3,cycle1512_4,cycle1512_5]⟩
lemma valid_data1512 : data1512.Valid src1512 dst1512 Finset.univ := by decide +kernel

def src1513 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst1513 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle1513_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1513_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1513_2 : CycleData E W := ⟨4,![10,16,15,3,23,14],![4,27,16,6,8,28]⟩
def cycle1513_3 : CycleData E W := ⟨2,![4,19,12,5],![2,6,26,14]⟩
def cycle1513_4 : CycleData E W := ⟨2,![6,21,17,11],![14,18,38,27]⟩
def cycle1513_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1513 : PartitionData E W := ⟨6,![cycle1513_0,cycle1513_1,cycle1513_2,cycle1513_3,cycle1513_4,cycle1513_5]⟩
lemma valid_data1513 : data1513.Valid src1513 dst1513 Finset.univ := by decide +kernel

def src1514 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst1514 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle1514_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1514_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1514_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1514_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1514_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1514_5 : CycleData E W := ⟨3,![7,22,17,16,8],![3,18,38,27,16]⟩
def data1514 : PartitionData E W := ⟨6,![cycle1514_0,cycle1514_1,cycle1514_2,cycle1514_3,cycle1514_4,cycle1514_5]⟩
lemma valid_data1514 : data1514.Valid src1514 dst1514 Finset.univ := by decide +kernel

def src1515 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst1515 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle1515_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1515_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1515_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,26]⟩
def cycle1515_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1515_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle1515_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1515 : PartitionData E W := ⟨6,![cycle1515_0,cycle1515_1,cycle1515_2,cycle1515_3,cycle1515_4,cycle1515_5]⟩
lemma valid_data1515 : data1515.Valid src1515 dst1515 Finset.univ := by decide +kernel

def src1516 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst1516 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle1516_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1516_1 : CycleData E W := ⟨3,![2,20,21,16,8],![3,8,18,38,16]⟩
def cycle1516_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,26]⟩
def cycle1516_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1516_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle1516_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1516 : PartitionData E W := ⟨6,![cycle1516_0,cycle1516_1,cycle1516_2,cycle1516_3,cycle1516_4,cycle1516_5]⟩
lemma valid_data1516 : data1516.Valid src1516 dst1516 Finset.univ := by decide +kernel

def src1517 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst1517 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle1517_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle1517_1 : CycleData E W := ⟨2,![2,23,16,8],![3,8,38,16]⟩
def cycle1517_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,26]⟩
def cycle1517_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle1517_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,27,38,18,28]⟩
def cycle1517_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data1517 : PartitionData E W := ⟨6,![cycle1517_0,cycle1517_1,cycle1517_2,cycle1517_3,cycle1517_4,cycle1517_5]⟩
lemma valid_data1517 : data1517.Valid src1517 dst1517 Finset.univ := by decide +kernel

def src1518 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst1518 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1518_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1518_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1518_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1518_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1518_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,27,14,18,28]⟩
def cycle1518_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data1518 : PartitionData E W := ⟨6,![cycle1518_0,cycle1518_1,cycle1518_2,cycle1518_3,cycle1518_4,cycle1518_5]⟩
lemma valid_data1518 : data1518.Valid src1518 dst1518 Finset.univ := by decide +kernel

def src1519 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst1519 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1519_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1519_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1519_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1519_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1519_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1519_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data1519 : PartitionData E W := ⟨6,![cycle1519_0,cycle1519_1,cycle1519_2,cycle1519_3,cycle1519_4,cycle1519_5]⟩
lemma valid_data1519 : data1519.Valid src1519 dst1519 Finset.univ := by decide +kernel

def src1520 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst1520 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1520_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1520_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1520_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1520_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1520_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle1520_5 : CycleData E W := ⟨3,![10,17,16,13,14],![4,27,16,26,28]⟩
def data1520 : PartitionData E W := ⟨6,![cycle1520_0,cycle1520_1,cycle1520_2,cycle1520_3,cycle1520_4,cycle1520_5]⟩
lemma valid_data1520 : data1520.Valid src1520 dst1520 Finset.univ := by decide +kernel

def src1521 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst1521 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1521_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1521_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1521_2 : CycleData E W := ⟨3,![3,23,17,16,15],![6,8,38,16,26]⟩
def cycle1521_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1521_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1521_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1521 : PartitionData E W := ⟨6,![cycle1521_0,cycle1521_1,cycle1521_2,cycle1521_3,cycle1521_4,cycle1521_5]⟩
lemma valid_data1521 : data1521.Valid src1521 dst1521 Finset.univ := by decide +kernel

def src1522 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst1522 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1522_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1522_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1522_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1522_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1522_4 : CycleData E W := ⟨3,![6,21,17,16,12],![14,18,38,16,26]⟩
def cycle1522_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data1522 : PartitionData E W := ⟨6,![cycle1522_0,cycle1522_1,cycle1522_2,cycle1522_3,cycle1522_4,cycle1522_5]⟩
lemma valid_data1522 : data1522.Valid src1522 dst1522 Finset.univ := by decide +kernel

def src1523 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst1523 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1523_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1523_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1523_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1523_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle1523_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1523_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data1523 : PartitionData E W := ⟨6,![cycle1523_0,cycle1523_1,cycle1523_2,cycle1523_3,cycle1523_4,cycle1523_5]⟩
lemma valid_data1523 : data1523.Valid src1523 dst1523 Finset.univ := by decide +kernel

def src1524 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst1524 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle1524_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1524_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1524_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1524_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1524_4 : CycleData E W := ⟨3,![10,11,6,21,14],![4,27,14,18,28]⟩
def cycle1524_5 : CycleData E W := ⟨3,![17,16,13,22,18],![16,27,26,28,38]⟩
def data1524 : PartitionData E W := ⟨6,![cycle1524_0,cycle1524_1,cycle1524_2,cycle1524_3,cycle1524_4,cycle1524_5]⟩
lemma valid_data1524 : data1524.Valid src1524 dst1524 Finset.univ := by decide +kernel

def src1525 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst1525 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle1525_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1525_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1525_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1525_3 : CycleData E W := ⟨3,![4,19,21,6,5],![2,6,38,18,14]⟩
def cycle1525_4 : CycleData E W := ⟨3,![10,17,18,22,14],![4,27,16,38,28]⟩
def cycle1525_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data1525 : PartitionData E W := ⟨6,![cycle1525_0,cycle1525_1,cycle1525_2,cycle1525_3,cycle1525_4,cycle1525_5]⟩
lemma valid_data1525 : data1525.Valid src1525 dst1525 Finset.univ := by decide +kernel

def src1526 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst1526 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle1526_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1526_1 : CycleData E W := ⟨2,![2,20,21,7],![3,8,28,18]⟩
def cycle1526_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1526_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1526_4 : CycleData E W := ⟨3,![6,22,18,17,11],![14,18,38,16,27]⟩
def cycle1526_5 : CycleData E W := ⟨2,![10,16,13,14],![4,27,26,28]⟩
def data1526 : PartitionData E W := ⟨6,![cycle1526_0,cycle1526_1,cycle1526_2,cycle1526_3,cycle1526_4,cycle1526_5]⟩
lemma valid_data1526 : data1526.Valid src1526 dst1526 Finset.univ := by decide +kernel

def src1527 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst1527 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle1527_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1527_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1527_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1527_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1527_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1527_5 : CycleData E W := ⟨3,![10,18,17,22,14],![4,27,16,38,28]⟩
def data1527 : PartitionData E W := ⟨6,![cycle1527_0,cycle1527_1,cycle1527_2,cycle1527_3,cycle1527_4,cycle1527_5]⟩
lemma valid_data1527 : data1527.Valid src1527 dst1527 Finset.univ := by decide +kernel

def src1528 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst1528 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle1528_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1528_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1528_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1528_3 : CycleData E W := ⟨2,![4,19,11,5],![2,6,27,14]⟩
def cycle1528_4 : CycleData E W := ⟨2,![6,21,16,12],![14,18,38,26]⟩
def cycle1528_5 : CycleData E W := ⟨3,![10,18,17,22,14],![4,27,16,38,28]⟩
def data1528 : PartitionData E W := ⟨6,![cycle1528_0,cycle1528_1,cycle1528_2,cycle1528_3,cycle1528_4,cycle1528_5]⟩
lemma valid_data1528 : data1528.Valid src1528 dst1528 Finset.univ := by decide +kernel

def src1529 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst1529 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle1529_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle1529_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1529_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle1529_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle1529_4 : CycleData E W := ⟨2,![6,21,13,12],![14,18,28,26]⟩
def cycle1529_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data1529 : PartitionData E W := ⟨6,![cycle1529_0,cycle1529_1,cycle1529_2,cycle1529_3,cycle1529_4,cycle1529_5]⟩
lemma valid_data1529 : data1529.Valid src1529 dst1529 Finset.univ := by decide +kernel

def src1530 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst1530 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle1530_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1530_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1530_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1530_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1530_4 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1530_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1530_6 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1530 : PartitionData E W := ⟨7,![cycle1530_0,cycle1530_1,cycle1530_2,cycle1530_3,cycle1530_4,cycle1530_5,cycle1530_6]⟩
lemma valid_data1530 : data1530.Valid src1530 dst1530 Finset.univ := by decide +kernel

def src1531 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst1531 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle1531_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1531_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1531_2 : CycleData E W := ⟨3,![4,3,23,13,5],![2,6,8,28,14]⟩
def cycle1531_3 : CycleData E W := ⟨3,![15,12,6,21,19],![6,26,14,18,38]⟩
def cycle1531_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle1531_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1531 : PartitionData E W := ⟨6,![cycle1531_0,cycle1531_1,cycle1531_2,cycle1531_3,cycle1531_4,cycle1531_5]⟩
lemma valid_data1531 : data1531.Valid src1531 dst1531 Finset.univ := by decide +kernel

def src1532 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst1532 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle1532_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1532_1 : CycleData E W := ⟨3,![2,20,13,6,7],![3,8,28,14,18]⟩
def cycle1532_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1532_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1532_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def cycle1532_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data1532 : PartitionData E W := ⟨6,![cycle1532_0,cycle1532_1,cycle1532_2,cycle1532_3,cycle1532_4,cycle1532_5]⟩
lemma valid_data1532 : data1532.Valid src1532 dst1532 Finset.univ := by decide +kernel

def src1533 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst1533 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle1533_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1533_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1533_2 : CycleData E W := ⟨4,![4,3,23,16,12,5],![2,6,8,38,26,14]⟩
def cycle1533_3 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1533_4 : CycleData E W := ⟨3,![10,18,17,22,14],![4,27,16,38,28]⟩
def cycle1533_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data1533 : PartitionData E W := ⟨6,![cycle1533_0,cycle1533_1,cycle1533_2,cycle1533_3,cycle1533_4,cycle1533_5]⟩
lemma valid_data1533 : data1533.Valid src1533 dst1533 Finset.univ := by decide +kernel

def src1534 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst1534 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle1534_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1534_1 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle1534_2 : CycleData E W := ⟨3,![4,3,23,13,5],![2,6,8,28,14]⟩
def cycle1534_3 : CycleData E W := ⟨2,![6,21,16,12],![14,18,38,26]⟩
def cycle1534_4 : CycleData E W := ⟨3,![10,18,17,22,14],![4,27,16,38,28]⟩
def cycle1534_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data1534 : PartitionData E W := ⟨6,![cycle1534_0,cycle1534_1,cycle1534_2,cycle1534_3,cycle1534_4,cycle1534_5]⟩
lemma valid_data1534 : data1534.Valid src1534 dst1534 Finset.univ := by decide +kernel

def src1535 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst1535 : E → W := ![4,3,8,6,2,14,18,3,16,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle1535_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle1535_1 : CycleData E W := ⟨2,![2,23,22,7],![3,8,38,18]⟩
def cycle1535_2 : CycleData E W := ⟨3,![10,19,3,20,14],![4,27,6,8,28]⟩
def cycle1535_3 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle1535_4 : CycleData E W := ⟨1,![6,21,13],![14,18,28]⟩
def cycle1535_5 : CycleData E W := ⟨2,![17,16,11,18],![16,38,26,27]⟩
def data1535 : PartitionData E W := ⟨6,![cycle1535_0,cycle1535_1,cycle1535_2,cycle1535_3,cycle1535_4,cycle1535_5]⟩
lemma valid_data1535 : data1535.Valid src1535 dst1535 Finset.univ := by decide +kernel

def src1536 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst1536 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1536_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1536_1 : CycleData E W := ⟨3,![2,23,16,11,7],![3,8,38,26,14]⟩
def cycle1536_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1536_3 : CycleData E W := ⟨2,![10,8,21,14],![4,14,18,28]⟩
def cycle1536_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1536_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1536 : PartitionData E W := ⟨6,![cycle1536_0,cycle1536_1,cycle1536_2,cycle1536_3,cycle1536_4,cycle1536_5]⟩
lemma valid_data1536 : data1536.Valid src1536 dst1536 Finset.univ := by decide +kernel

def src1537 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst1537 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle1537_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1537_1 : CycleData E W := ⟨3,![2,23,14,10,7],![3,8,28,4,14]⟩
def cycle1537_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1537_3 : CycleData E W := ⟨2,![8,21,16,11],![14,18,38,26]⟩
def cycle1537_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1537_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data1537 : PartitionData E W := ⟨6,![cycle1537_0,cycle1537_1,cycle1537_2,cycle1537_3,cycle1537_4,cycle1537_5]⟩
lemma valid_data1537 : data1537.Valid src1537 dst1537 Finset.univ := by decide +kernel

def src1538 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst1538 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle1538_0 : CycleData E W := ⟨3,![0,14,13,18,5],![2,4,28,27,16]⟩
def cycle1538_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1538_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle1538_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,6,8,28,18]⟩
def cycle1538_4 : CycleData E W := ⟨2,![8,22,16,11],![14,18,38,26]⟩
def cycle1538_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data1538 : PartitionData E W := ⟨6,![cycle1538_0,cycle1538_1,cycle1538_2,cycle1538_3,cycle1538_4,cycle1538_5]⟩
lemma valid_data1538 : data1538.Valid src1538 dst1538 Finset.univ := by decide +kernel

def src1539 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst1539 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle1539_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1539_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1539_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1539_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1539_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,26,38,28]⟩
def cycle1539_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data1539 : PartitionData E W := ⟨6,![cycle1539_0,cycle1539_1,cycle1539_2,cycle1539_3,cycle1539_4,cycle1539_5]⟩
lemma valid_data1539 : data1539.Valid src1539 dst1539 Finset.univ := by decide +kernel

def src1540 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst1540 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle1540_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1540_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1540_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1540_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1540_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,26,38,28]⟩
def cycle1540_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data1540 : PartitionData E W := ⟨6,![cycle1540_0,cycle1540_1,cycle1540_2,cycle1540_3,cycle1540_4,cycle1540_5]⟩
lemma valid_data1540 : data1540.Valid src1540 dst1540 Finset.univ := by decide +kernel

def src1541 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst1541 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle1541_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1541_1 : CycleData E W := ⟨3,![2,20,14,10,7],![3,8,28,4,14]⟩
def cycle1541_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1541_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1541_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,26]⟩
def cycle1541_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data1541 : PartitionData E W := ⟨6,![cycle1541_0,cycle1541_1,cycle1541_2,cycle1541_3,cycle1541_4,cycle1541_5]⟩
lemma valid_data1541 : data1541.Valid src1541 dst1541 Finset.univ := by decide +kernel

def src1542 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst1542 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle1542_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1542_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1542_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1542_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1542_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle1542_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1542 : PartitionData E W := ⟨6,![cycle1542_0,cycle1542_1,cycle1542_2,cycle1542_3,cycle1542_4,cycle1542_5]⟩
lemma valid_data1542 : data1542.Valid src1542 dst1542 Finset.univ := by decide +kernel

def src1543 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst1543 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle1543_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1543_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1543_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1543_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1543_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle1543_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1543 : PartitionData E W := ⟨6,![cycle1543_0,cycle1543_1,cycle1543_2,cycle1543_3,cycle1543_4,cycle1543_5]⟩
lemma valid_data1543 : data1543.Valid src1543 dst1543 Finset.univ := by decide +kernel

def src1544 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst1544 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle1544_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1544_1 : CycleData E W := ⟨2,![1,14,17,6],![3,4,27,16]⟩
def cycle1544_2 : CycleData E W := ⟨3,![2,20,12,11,7],![3,8,28,26,14]⟩
def cycle1544_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1544_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle1544_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data1544 : PartitionData E W := ⟨6,![cycle1544_0,cycle1544_1,cycle1544_2,cycle1544_3,cycle1544_4,cycle1544_5]⟩
lemma valid_data1544 : data1544.Valid src1544 dst1544 Finset.univ := by decide +kernel

def src1545 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst1545 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle1545_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1545_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1545_2 : CycleData E W := ⟨3,![2,3,15,16,6],![3,8,6,26,16]⟩
def cycle1545_3 : CycleData E W := ⟨3,![5,17,23,20,9],![2,16,38,8,18]⟩
def cycle1545_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle1545_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1545 : PartitionData E W := ⟨6,![cycle1545_0,cycle1545_1,cycle1545_2,cycle1545_3,cycle1545_4,cycle1545_5]⟩
lemma valid_data1545 : data1545.Valid src1545 dst1545 Finset.univ := by decide +kernel

def src1546 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst1546 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle1546_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1546_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1546_2 : CycleData E W := ⟨3,![2,3,15,16,6],![3,8,6,26,16]⟩
def cycle1546_3 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle1546_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,26,28]⟩
def cycle1546_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1546 : PartitionData E W := ⟨6,![cycle1546_0,cycle1546_1,cycle1546_2,cycle1546_3,cycle1546_4,cycle1546_5]⟩
lemma valid_data1546 : data1546.Valid src1546 dst1546 Finset.univ := by decide +kernel

def src1547 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst1547 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle1547_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle1547_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1547_2 : CycleData E W := ⟨3,![2,3,15,16,6],![3,8,6,26,16]⟩
def cycle1547_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1547_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle1547_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data1547 : PartitionData E W := ⟨6,![cycle1547_0,cycle1547_1,cycle1547_2,cycle1547_3,cycle1547_4,cycle1547_5]⟩
lemma valid_data1547 : data1547.Valid src1547 dst1547 Finset.univ := by decide +kernel

def src1548 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst1548 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle1548_0 : CycleData E W := ⟨2,![0,14,18,5],![2,4,27,16]⟩
def cycle1548_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1548_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle1548_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1548_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,26]⟩
def cycle1548_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data1548 : PartitionData E W := ⟨6,![cycle1548_0,cycle1548_1,cycle1548_2,cycle1548_3,cycle1548_4,cycle1548_5]⟩
lemma valid_data1548 : data1548.Valid src1548 dst1548 Finset.univ := by decide +kernel

def src1549 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst1549 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle1549_0 : CycleData E W := ⟨3,![0,10,11,15,4],![2,4,14,26,6]⟩
def cycle1549_1 : CycleData E W := ⟨2,![1,14,18,6],![3,4,27,16]⟩
def cycle1549_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1549_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1549_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle1549_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data1549 : PartitionData E W := ⟨6,![cycle1549_0,cycle1549_1,cycle1549_2,cycle1549_3,cycle1549_4,cycle1549_5]⟩
lemma valid_data1549 : data1549.Valid src1549 dst1549 Finset.univ := by decide +kernel

def src1550 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst1550 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle1550_0 : CycleData E W := ⟨2,![0,14,18,5],![2,4,27,16]⟩
def cycle1550_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1550_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle1550_3 : CycleData E W := ⟨2,![3,20,12,15],![6,8,28,26]⟩
def cycle1550_4 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1550_5 : CycleData E W := ⟨2,![8,22,16,11],![14,18,38,26]⟩
def data1550 : PartitionData E W := ⟨6,![cycle1550_0,cycle1550_1,cycle1550_2,cycle1550_3,cycle1550_4,cycle1550_5]⟩
lemma valid_data1550 : data1550.Valid src1550 dst1550 Finset.univ := by decide +kernel

def src1551 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst1551 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle1551_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1551_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1551_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1551_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,27,28,18]⟩
def cycle1551_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle1551_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data1551 : PartitionData E W := ⟨6,![cycle1551_0,cycle1551_1,cycle1551_2,cycle1551_3,cycle1551_4,cycle1551_5]⟩
lemma valid_data1551 : data1551.Valid src1551 dst1551 Finset.univ := by decide +kernel

def src1552 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst1552 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle1552_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1552_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1552_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle1552_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1552_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle1552_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data1552 : PartitionData E W := ⟨6,![cycle1552_0,cycle1552_1,cycle1552_2,cycle1552_3,cycle1552_4,cycle1552_5]⟩
lemma valid_data1552 : data1552.Valid src1552 dst1552 Finset.univ := by decide +kernel

def src1553 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst1553 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle1553_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1553_1 : CycleData E W := ⟨3,![1,14,13,20,2],![3,4,27,28,8]⟩
def cycle1553_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1553_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle1553_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle1553_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,26,38]⟩
def data1553 : PartitionData E W := ⟨6,![cycle1553_0,cycle1553_1,cycle1553_2,cycle1553_3,cycle1553_4,cycle1553_5]⟩
lemma valid_data1553 : data1553.Valid src1553 dst1553 Finset.univ := by decide +kernel

def src1554 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst1554 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle1554_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1554_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1554_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1554_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1554_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1554_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1554 : PartitionData E W := ⟨6,![cycle1554_0,cycle1554_1,cycle1554_2,cycle1554_3,cycle1554_4,cycle1554_5]⟩
lemma valid_data1554 : data1554.Valid src1554 dst1554 Finset.univ := by decide +kernel

def src1555 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst1555 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle1555_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1555_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1555_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1555_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1555_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle1555_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1555 : PartitionData E W := ⟨6,![cycle1555_0,cycle1555_1,cycle1555_2,cycle1555_3,cycle1555_4,cycle1555_5]⟩
lemma valid_data1555 : data1555.Valid src1555 dst1555 Finset.univ := by decide +kernel

def src1556 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst1556 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle1556_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1556_1 : CycleData E W := ⟨3,![2,20,14,10,7],![3,8,28,4,14]⟩
def cycle1556_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1556_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1556_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def cycle1556_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data1556 : PartitionData E W := ⟨6,![cycle1556_0,cycle1556_1,cycle1556_2,cycle1556_3,cycle1556_4,cycle1556_5]⟩
lemma valid_data1556 : data1556.Valid src1556 dst1556 Finset.univ := by decide +kernel

def src1557 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst1557 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle1557_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1557_1 : CycleData E W := ⟨3,![2,23,18,11,7],![3,8,38,27,14]⟩
def cycle1557_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1557_3 : CycleData E W := ⟨2,![10,8,21,14],![4,14,18,28]⟩
def cycle1557_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1557_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data1557 : PartitionData E W := ⟨6,![cycle1557_0,cycle1557_1,cycle1557_2,cycle1557_3,cycle1557_4,cycle1557_5]⟩
lemma valid_data1557 : data1557.Valid src1557 dst1557 Finset.univ := by decide +kernel

def src1558 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst1558 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle1558_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1558_1 : CycleData E W := ⟨3,![2,23,14,10,7],![3,8,28,4,14]⟩
def cycle1558_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1558_3 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle1558_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle1558_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data1558 : PartitionData E W := ⟨6,![cycle1558_0,cycle1558_1,cycle1558_2,cycle1558_3,cycle1558_4,cycle1558_5]⟩
lemma valid_data1558 : data1558.Valid src1558 dst1558 Finset.univ := by decide +kernel

def src1559 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst1559 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle1559_0 : CycleData E W := ⟨3,![0,14,13,16,5],![2,4,28,26,16]⟩
def cycle1559_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1559_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle1559_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,6,8,28,18]⟩
def cycle1559_4 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def cycle1559_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data1559 : PartitionData E W := ⟨6,![cycle1559_0,cycle1559_1,cycle1559_2,cycle1559_3,cycle1559_4,cycle1559_5]⟩
lemma valid_data1559 : data1559.Valid src1559 dst1559 Finset.univ := by decide +kernel

def src1560 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst1560 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle1560_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1560_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1560_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1560_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle1560_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle1560_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1560 : PartitionData E W := ⟨6,![cycle1560_0,cycle1560_1,cycle1560_2,cycle1560_3,cycle1560_4,cycle1560_5]⟩
lemma valid_data1560 : data1560.Valid src1560 dst1560 Finset.univ := by decide +kernel

def src1561 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst1561 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle1561_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1561_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1561_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle1561_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1561_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle1561_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data1561 : PartitionData E W := ⟨6,![cycle1561_0,cycle1561_1,cycle1561_2,cycle1561_3,cycle1561_4,cycle1561_5]⟩
lemma valid_data1561 : data1561.Valid src1561 dst1561 Finset.univ := by decide +kernel

def src1562 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst1562 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle1562_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1562_1 : CycleData E W := ⟨3,![1,14,13,20,2],![3,4,26,28,8]⟩
def cycle1562_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1562_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle1562_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle1562_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data1562 : PartitionData E W := ⟨6,![cycle1562_0,cycle1562_1,cycle1562_2,cycle1562_3,cycle1562_4,cycle1562_5]⟩
lemma valid_data1562 : data1562.Valid src1562 dst1562 Finset.univ := by decide +kernel

def src1563 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst1563 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle1563_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1563_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1563_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle1563_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1563_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle1563_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data1563 : PartitionData E W := ⟨6,![cycle1563_0,cycle1563_1,cycle1563_2,cycle1563_3,cycle1563_4,cycle1563_5]⟩
lemma valid_data1563 : data1563.Valid src1563 dst1563 Finset.univ := by decide +kernel

def src1564 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst1564 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle1564_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1564_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1564_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle1564_3 : CycleData E W := ⟨2,![3,23,12,19],![6,8,28,27]⟩
def cycle1564_4 : CycleData E W := ⟨2,![8,21,18,11],![14,18,38,27]⟩
def cycle1564_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data1564 : PartitionData E W := ⟨6,![cycle1564_0,cycle1564_1,cycle1564_2,cycle1564_3,cycle1564_4,cycle1564_5]⟩
lemma valid_data1564 : data1564.Valid src1564 dst1564 Finset.univ := by decide +kernel

def src1565 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst1565 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle1565_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1565_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1565_2 : CycleData E W := ⟨3,![2,20,13,16,6],![3,8,28,26,16]⟩
def cycle1565_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1565_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1565_5 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def data1565 : PartitionData E W := ⟨6,![cycle1565_0,cycle1565_1,cycle1565_2,cycle1565_3,cycle1565_4,cycle1565_5]⟩
lemma valid_data1565 : data1565.Valid src1565 dst1565 Finset.univ := by decide +kernel

def src1566 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst1566 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle1566_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1566_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1566_2 : CycleData E W := ⟨3,![2,3,19,18,6],![3,8,6,27,16]⟩
def cycle1566_3 : CycleData E W := ⟨3,![5,17,23,20,9],![2,16,38,8,18]⟩
def cycle1566_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle1566_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1566 : PartitionData E W := ⟨6,![cycle1566_0,cycle1566_1,cycle1566_2,cycle1566_3,cycle1566_4,cycle1566_5]⟩
lemma valid_data1566 : data1566.Valid src1566 dst1566 Finset.univ := by decide +kernel

def src1567 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst1567 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle1567_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1567_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1567_2 : CycleData E W := ⟨3,![2,3,19,18,6],![3,8,6,27,16]⟩
def cycle1567_3 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle1567_4 : CycleData E W := ⟨3,![20,8,11,12,23],![8,18,14,27,28]⟩
def cycle1567_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data1567 : PartitionData E W := ⟨6,![cycle1567_0,cycle1567_1,cycle1567_2,cycle1567_3,cycle1567_4,cycle1567_5]⟩
lemma valid_data1567 : data1567.Valid src1567 dst1567 Finset.univ := by decide +kernel

def src1568 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst1568 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle1568_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1568_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1568_2 : CycleData E W := ⟨3,![2,3,19,18,6],![3,8,6,27,16]⟩
def cycle1568_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1568_4 : CycleData E W := ⟨2,![8,21,12,11],![14,18,28,27]⟩
def cycle1568_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data1568 : PartitionData E W := ⟨6,![cycle1568_0,cycle1568_1,cycle1568_2,cycle1568_3,cycle1568_4,cycle1568_5]⟩
lemma valid_data1568 : data1568.Valid src1568 dst1568 Finset.univ := by decide +kernel

def src1569 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst1569 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle1569_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1569_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1569_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1569_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1569_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle1569_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1569 : PartitionData E W := ⟨6,![cycle1569_0,cycle1569_1,cycle1569_2,cycle1569_3,cycle1569_4,cycle1569_5]⟩
lemma valid_data1569 : data1569.Valid src1569 dst1569 Finset.univ := by decide +kernel

def src1570 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst1570 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle1570_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1570_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1570_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle1570_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1570_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle1570_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data1570 : PartitionData E W := ⟨6,![cycle1570_0,cycle1570_1,cycle1570_2,cycle1570_3,cycle1570_4,cycle1570_5]⟩
lemma valid_data1570 : data1570.Valid src1570 dst1570 Finset.univ := by decide +kernel

def src1571 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst1571 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle1571_0 : CycleData E W := ⟨2,![0,10,8,9],![2,4,14,18]⟩
def cycle1571_1 : CycleData E W := ⟨2,![1,14,17,6],![3,4,26,16]⟩
def cycle1571_2 : CycleData E W := ⟨3,![2,20,12,11,7],![3,8,28,27,14]⟩
def cycle1571_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1571_4 : CycleData E W := ⟨2,![4,15,16,5],![2,6,27,16]⟩
def cycle1571_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data1571 : PartitionData E W := ⟨6,![cycle1571_0,cycle1571_1,cycle1571_2,cycle1571_3,cycle1571_4,cycle1571_5]⟩
lemma valid_data1571 : data1571.Valid src1571 dst1571 Finset.univ := by decide +kernel

def src1572 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst1572 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle1572_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1572_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1572_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1572_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1572_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1572_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1572 : PartitionData E W := ⟨6,![cycle1572_0,cycle1572_1,cycle1572_2,cycle1572_3,cycle1572_4,cycle1572_5]⟩
lemma valid_data1572 : data1572.Valid src1572 dst1572 Finset.univ := by decide +kernel

def src1573 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst1573 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle1573_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1573_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1573_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle1573_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1573_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle1573_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1573 : PartitionData E W := ⟨6,![cycle1573_0,cycle1573_1,cycle1573_2,cycle1573_3,cycle1573_4,cycle1573_5]⟩
lemma valid_data1573 : data1573.Valid src1573 dst1573 Finset.univ := by decide +kernel

def src1574 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst1574 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle1574_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1574_1 : CycleData E W := ⟨2,![2,20,11,7],![3,8,28,14]⟩
def cycle1574_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1574_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,26,28,18]⟩
def cycle1574_4 : CycleData E W := ⟨3,![10,8,22,18,14],![4,14,18,38,27]⟩
def cycle1574_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data1574 : PartitionData E W := ⟨6,![cycle1574_0,cycle1574_1,cycle1574_2,cycle1574_3,cycle1574_4,cycle1574_5]⟩
lemma valid_data1574 : data1574.Valid src1574 dst1574 Finset.univ := by decide +kernel

def src1575 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst1575 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle1575_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1575_1 : CycleData E W := ⟨4,![2,23,18,14,10,7],![3,8,38,27,4,14]⟩
def cycle1575_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1575_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle1575_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle1575_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1575 : PartitionData E W := ⟨6,![cycle1575_0,cycle1575_1,cycle1575_2,cycle1575_3,cycle1575_4,cycle1575_5]⟩
lemma valid_data1575 : data1575.Valid src1575 dst1575 Finset.univ := by decide +kernel

def src1576 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst1576 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle1576_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1576_1 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle1576_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1576_3 : CycleData E W := ⟨3,![10,8,21,18,14],![4,14,18,38,27]⟩
def cycle1576_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle1576_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1576 : PartitionData E W := ⟨6,![cycle1576_0,cycle1576_1,cycle1576_2,cycle1576_3,cycle1576_4,cycle1576_5]⟩
lemma valid_data1576 : data1576.Valid src1576 dst1576 Finset.univ := by decide +kernel

def src1577 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst1577 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle1577_0 : CycleData E W := ⟨3,![0,14,13,15,4],![2,4,27,26,6]⟩
def cycle1577_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1577_2 : CycleData E W := ⟨3,![2,20,12,16,6],![3,8,28,26,16]⟩
def cycle1577_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1577_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1577_5 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def data1577 : PartitionData E W := ⟨6,![cycle1577_0,cycle1577_1,cycle1577_2,cycle1577_3,cycle1577_4,cycle1577_5]⟩
lemma valid_data1577 : data1577.Valid src1577 dst1577 Finset.univ := by decide +kernel

def src1578 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst1578 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle1578_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1578_1 : CycleData E W := ⟨4,![2,23,16,14,10,7],![3,8,38,26,4,14]⟩
def cycle1578_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1578_3 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle1578_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle1578_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1578 : PartitionData E W := ⟨6,![cycle1578_0,cycle1578_1,cycle1578_2,cycle1578_3,cycle1578_4,cycle1578_5]⟩
lemma valid_data1578 : data1578.Valid src1578 dst1578 Finset.univ := by decide +kernel

def src1579 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst1579 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle1579_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1579_1 : CycleData E W := ⟨2,![2,23,11,7],![3,8,28,14]⟩
def cycle1579_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1579_3 : CycleData E W := ⟨3,![10,8,21,16,14],![4,14,18,38,26]⟩
def cycle1579_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle1579_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data1579 : PartitionData E W := ⟨6,![cycle1579_0,cycle1579_1,cycle1579_2,cycle1579_3,cycle1579_4,cycle1579_5]⟩
lemma valid_data1579 : data1579.Valid src1579 dst1579 Finset.univ := by decide +kernel

def src1580 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst1580 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle1580_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,26,6]⟩
def cycle1580_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle1580_2 : CycleData E W := ⟨3,![2,3,19,18,6],![3,8,6,27,16]⟩
def cycle1580_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1580_4 : CycleData E W := ⟨1,![8,21,11],![14,18,28]⟩
def cycle1580_5 : CycleData E W := ⟨3,![20,12,13,16,23],![8,28,27,26,38]⟩
def data1580 : PartitionData E W := ⟨6,![cycle1580_0,cycle1580_1,cycle1580_2,cycle1580_3,cycle1580_4,cycle1580_5]⟩
lemma valid_data1580 : data1580.Valid src1580 dst1580 Finset.univ := by decide +kernel

def src1581 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst1581 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle1581_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1581_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1581_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1581_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1581_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle1581_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1581 : PartitionData E W := ⟨6,![cycle1581_0,cycle1581_1,cycle1581_2,cycle1581_3,cycle1581_4,cycle1581_5]⟩
lemma valid_data1581 : data1581.Valid src1581 dst1581 Finset.univ := by decide +kernel

def src1582 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst1582 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle1582_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1582_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1582_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle1582_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1582_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,26]⟩
def cycle1582_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1582 : PartitionData E W := ⟨6,![cycle1582_0,cycle1582_1,cycle1582_2,cycle1582_3,cycle1582_4,cycle1582_5]⟩
lemma valid_data1582 : data1582.Valid src1582 dst1582 Finset.univ := by decide +kernel

def src1583 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst1583 : E → W := ![4,3,8,6,2,16,3,14,18,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle1583_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1583_1 : CycleData E W := ⟨2,![2,20,11,7],![3,8,28,14]⟩
def cycle1583_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1583_3 : CycleData E W := ⟨3,![4,15,12,21,9],![2,6,27,28,18]⟩
def cycle1583_4 : CycleData E W := ⟨3,![10,8,22,18,14],![4,14,18,38,26]⟩
def cycle1583_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data1583 : PartitionData E W := ⟨6,![cycle1583_0,cycle1583_1,cycle1583_2,cycle1583_3,cycle1583_4,cycle1583_5]⟩
lemma valid_data1583 : data1583.Valid src1583 dst1583 Finset.univ := by decide +kernel

def src1584 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst1584 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle1584_0 : CycleData E W := ⟨3,![0,1,2,20,9],![2,4,3,8,18]⟩
def cycle1584_1 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1584_2 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1584_3 : CycleData E W := ⟨2,![6,16,11,7],![3,16,26,14]⟩
def cycle1584_4 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def cycle1584_5 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def data1584 : PartitionData E W := ⟨6,![cycle1584_0,cycle1584_1,cycle1584_2,cycle1584_3,cycle1584_4,cycle1584_5]⟩
lemma valid_data1584 : data1584.Valid src1584 dst1584 Finset.univ := by decide +kernel

def src1585 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst1585 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle1585_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle1585_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1585_2 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1585_3 : CycleData E W := ⟨3,![6,15,19,12,7],![3,16,6,27,14]⟩
def cycle1585_4 : CycleData E W := ⟨2,![8,21,17,11],![14,18,38,26]⟩
def cycle1585_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1585 : PartitionData E W := ⟨6,![cycle1585_0,cycle1585_1,cycle1585_2,cycle1585_3,cycle1585_4,cycle1585_5]⟩
lemma valid_data1585 : data1585.Valid src1585 dst1585 Finset.univ := by decide +kernel

def src1586 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst1586 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle1586_0 : CycleData E W := ⟨2,![0,14,21,9],![2,4,28,18]⟩
def cycle1586_1 : CycleData E W := ⟨2,![1,10,11,7],![3,4,26,14]⟩
def cycle1586_2 : CycleData E W := ⟨3,![2,23,17,16,6],![3,8,38,26,16]⟩
def cycle1586_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1586_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1586_5 : CycleData E W := ⟨2,![8,22,18,12],![14,18,38,27]⟩
def data1586 : PartitionData E W := ⟨6,![cycle1586_0,cycle1586_1,cycle1586_2,cycle1586_3,cycle1586_4,cycle1586_5]⟩
lemma valid_data1586 : data1586.Valid src1586 dst1586 Finset.univ := by decide +kernel

def src1587 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst1587 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle1587_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1587_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1587_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1587_3 : CycleData E W := ⟨4,![4,15,16,13,21,9],![2,6,16,27,28,18]⟩
def cycle1587_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1587_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1587 : PartitionData E W := ⟨6,![cycle1587_0,cycle1587_1,cycle1587_2,cycle1587_3,cycle1587_4,cycle1587_5]⟩
lemma valid_data1587 : data1587.Valid src1587 dst1587 Finset.univ := by decide +kernel

def src1588 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst1588 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle1588_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1588_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1588_2 : CycleData E W := ⟨3,![3,23,13,16,15],![6,8,28,27,16]⟩
def cycle1588_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle1588_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle1588_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1588 : PartitionData E W := ⟨6,![cycle1588_0,cycle1588_1,cycle1588_2,cycle1588_3,cycle1588_4,cycle1588_5]⟩
lemma valid_data1588 : data1588.Valid src1588 dst1588 Finset.univ := by decide +kernel

def src1589 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst1589 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle1589_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,14,18]⟩
def cycle1589_1 : CycleData E W := ⟨3,![2,20,13,16,6],![3,8,28,27,16]⟩
def cycle1589_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle1589_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1589_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle1589_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data1589 : PartitionData E W := ⟨6,![cycle1589_0,cycle1589_1,cycle1589_2,cycle1589_3,cycle1589_4,cycle1589_5]⟩
lemma valid_data1589 : data1589.Valid src1589 dst1589 Finset.univ := by decide +kernel

def src1590 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst1590 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle1590_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle1590_1 : CycleData E W := ⟨3,![1,14,21,20,2],![3,4,28,18,8]⟩
def cycle1590_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1590_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1590_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle1590_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1590 : PartitionData E W := ⟨6,![cycle1590_0,cycle1590_1,cycle1590_2,cycle1590_3,cycle1590_4,cycle1590_5]⟩
lemma valid_data1590 : data1590.Valid src1590 dst1590 Finset.univ := by decide +kernel

def src1591 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst1591 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle1591_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle1591_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1591_2 : CycleData E W := ⟨3,![3,20,21,18,19],![6,8,18,38,26]⟩
def cycle1591_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1591_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle1591_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data1591 : PartitionData E W := ⟨6,![cycle1591_0,cycle1591_1,cycle1591_2,cycle1591_3,cycle1591_4,cycle1591_5]⟩
lemma valid_data1591 : data1591.Valid src1591 dst1591 Finset.univ := by decide +kernel

def src1592 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst1592 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle1592_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,26,14,18]⟩
def cycle1592_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1592_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle1592_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1592_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,27,14]⟩
def cycle1592_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data1592 : PartitionData E W := ⟨6,![cycle1592_0,cycle1592_1,cycle1592_2,cycle1592_3,cycle1592_4,cycle1592_5]⟩
lemma valid_data1592 : data1592.Valid src1592 dst1592 Finset.univ := by decide +kernel

def src1593 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst1593 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle1593_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1593_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1593_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,16]⟩
def cycle1593_3 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle1593_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1593_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1593 : PartitionData E W := ⟨6,![cycle1593_0,cycle1593_1,cycle1593_2,cycle1593_3,cycle1593_4,cycle1593_5]⟩
lemma valid_data1593 : data1593.Valid src1593 dst1593 Finset.univ := by decide +kernel

def src1594 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst1594 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle1594_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle1594_1 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle1594_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle1594_3 : CycleData E W := ⟨3,![4,15,16,21,9],![2,6,16,38,18]⟩
def cycle1594_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle1594_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1594 : PartitionData E W := ⟨6,![cycle1594_0,cycle1594_1,cycle1594_2,cycle1594_3,cycle1594_4,cycle1594_5]⟩
lemma valid_data1594 : data1594.Valid src1594 dst1594 Finset.univ := by decide +kernel

def src1595 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst1595 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle1595_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,14,18]⟩
def cycle1595_1 : CycleData E W := ⟨2,![2,23,16,6],![3,8,38,16]⟩
def cycle1595_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle1595_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle1595_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,26,38,18,28]⟩
def cycle1595_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data1595 : PartitionData E W := ⟨6,![cycle1595_0,cycle1595_1,cycle1595_2,cycle1595_3,cycle1595_4,cycle1595_5]⟩
lemma valid_data1595 : data1595.Valid src1595 dst1595 Finset.univ := by decide +kernel

def src1596 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst1596 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle1596_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle1596_1 : CycleData E W := ⟨3,![1,14,21,8,7],![3,4,28,18,14]⟩
def cycle1596_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle1596_3 : CycleData E W := ⟨2,![4,3,20,9],![2,6,8,18]⟩
def cycle1596_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle1596_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1596 : PartitionData E W := ⟨6,![cycle1596_0,cycle1596_1,cycle1596_2,cycle1596_3,cycle1596_4,cycle1596_5]⟩
lemma valid_data1596 : data1596.Valid src1596 dst1596 Finset.univ := by decide +kernel

def src1597 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst1597 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle1597_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1597_1 : CycleData E W := ⟨2,![1,14,23,2],![3,4,28,8]⟩
def cycle1597_2 : CycleData E W := ⟨3,![3,20,8,12,19],![6,8,18,14,27]⟩
def cycle1597_3 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle1597_4 : CycleData E W := ⟨2,![6,16,11,7],![3,16,26,14]⟩
def cycle1597_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data1597 : PartitionData E W := ⟨6,![cycle1597_0,cycle1597_1,cycle1597_2,cycle1597_3,cycle1597_4,cycle1597_5]⟩
lemma valid_data1597 : data1597.Valid src1597 dst1597 Finset.univ := by decide +kernel

def src1598 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst1598 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle1598_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle1598_1 : CycleData E W := ⟨2,![1,14,20,2],![3,4,28,8]⟩
def cycle1598_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle1598_3 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle1598_4 : CycleData E W := ⟨2,![6,16,11,7],![3,16,26,14]⟩
def cycle1598_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,27]⟩
def data1598 : PartitionData E W := ⟨6,![cycle1598_0,cycle1598_1,cycle1598_2,cycle1598_3,cycle1598_4,cycle1598_5]⟩
lemma valid_data1598 : data1598.Valid src1598 dst1598 Finset.univ := by decide +kernel

def src1599 : E → W := ![2,4,3,8,6,2,16,3,14,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst1599 : E → W := ![4,3,8,6,2,16,3,14,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle1599_0 : CycleData E W := ⟨10,![4,3,20,21,13,12,7,1,10,16,17,5],![2,6,8,18,28,27,14,3,4,26,38,16]⟩
def cycle1599_1 : CycleData E W := ⟨10,![0,14,22,23,2,6,18,19,15,11,8,9],![2,4,28,38,8,3,16,27,6,26,14,18]⟩
def data1599 : PartitionData E W := ⟨2,![cycle1599_0,cycle1599_1]⟩
lemma valid_data1599 : data1599.Valid src1599 dst1599 Finset.univ := by decide +kernel

def lookupB7 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data1400 else (if j < 2 then data1401 else data1402)) else (if j < 4 then data1403 else (if j < 5 then data1404 else data1405))) else (if j < 9 then (if j < 7 then data1406 else (if j < 8 then data1407 else data1408)) else (if j < 10 then data1409 else (if j < 11 then data1410 else data1411)))) else (if j < 18 then (if j < 15 then (if j < 13 then data1412 else (if j < 14 then data1413 else data1414)) else (if j < 16 then data1415 else (if j < 17 then data1416 else data1417))) else (if j < 21 then (if j < 19 then data1418 else (if j < 20 then data1419 else data1420)) else (if j < 23 then (if j < 22 then data1421 else data1422) else (if j < 24 then data1423 else data1424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data1425 else (if j < 27 then data1426 else data1427)) else (if j < 29 then data1428 else (if j < 30 then data1429 else data1430))) else (if j < 34 then (if j < 32 then data1431 else (if j < 33 then data1432 else data1433)) else (if j < 35 then data1434 else (if j < 36 then data1435 else data1436)))) else (if j < 43 then (if j < 40 then (if j < 38 then data1437 else (if j < 39 then data1438 else data1439)) else (if j < 41 then data1440 else (if j < 42 then data1441 else data1442))) else (if j < 46 then (if j < 44 then data1443 else (if j < 45 then data1444 else data1445)) else (if j < 48 then (if j < 47 then data1446 else data1447) else (if j < 49 then data1448 else data1449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data1450 else (if j < 52 then data1451 else data1452)) else (if j < 54 then data1453 else (if j < 55 then data1454 else data1455))) else (if j < 59 then (if j < 57 then data1456 else (if j < 58 then data1457 else data1458)) else (if j < 60 then data1459 else (if j < 61 then data1460 else data1461)))) else (if j < 68 then (if j < 65 then (if j < 63 then data1462 else (if j < 64 then data1463 else data1464)) else (if j < 66 then data1465 else (if j < 67 then data1466 else data1467))) else (if j < 71 then (if j < 69 then data1468 else (if j < 70 then data1469 else data1470)) else (if j < 73 then (if j < 72 then data1471 else data1472) else (if j < 74 then data1473 else data1474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data1475 else (if j < 77 then data1476 else data1477)) else (if j < 79 then data1478 else (if j < 80 then data1479 else data1480))) else (if j < 84 then (if j < 82 then data1481 else (if j < 83 then data1482 else data1483)) else (if j < 85 then data1484 else (if j < 86 then data1485 else data1486)))) else (if j < 93 then (if j < 90 then (if j < 88 then data1487 else (if j < 89 then data1488 else data1489)) else (if j < 91 then data1490 else (if j < 92 then data1491 else data1492))) else (if j < 96 then (if j < 94 then data1493 else (if j < 95 then data1494 else data1495)) else (if j < 98 then (if j < 97 then data1496 else data1497) else (if j < 99 then data1498 else data1499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data1500 else (if j < 102 then data1501 else data1502)) else (if j < 104 then data1503 else (if j < 105 then data1504 else data1505))) else (if j < 109 then (if j < 107 then data1506 else (if j < 108 then data1507 else data1508)) else (if j < 110 then data1509 else (if j < 111 then data1510 else data1511)))) else (if j < 118 then (if j < 115 then (if j < 113 then data1512 else (if j < 114 then data1513 else data1514)) else (if j < 116 then data1515 else (if j < 117 then data1516 else data1517))) else (if j < 121 then (if j < 119 then data1518 else (if j < 120 then data1519 else data1520)) else (if j < 123 then (if j < 122 then data1521 else data1522) else (if j < 124 then data1523 else data1524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data1525 else (if j < 127 then data1526 else data1527)) else (if j < 129 then data1528 else (if j < 130 then data1529 else data1530))) else (if j < 134 then (if j < 132 then data1531 else (if j < 133 then data1532 else data1533)) else (if j < 135 then data1534 else (if j < 136 then data1535 else data1536)))) else (if j < 143 then (if j < 140 then (if j < 138 then data1537 else (if j < 139 then data1538 else data1539)) else (if j < 141 then data1540 else (if j < 142 then data1541 else data1542))) else (if j < 146 then (if j < 144 then data1543 else (if j < 145 then data1544 else data1545)) else (if j < 148 then (if j < 147 then data1546 else data1547) else (if j < 149 then data1548 else data1549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data1550 else (if j < 152 then data1551 else data1552)) else (if j < 154 then data1553 else (if j < 155 then data1554 else data1555))) else (if j < 159 then (if j < 157 then data1556 else (if j < 158 then data1557 else data1558)) else (if j < 160 then data1559 else (if j < 161 then data1560 else data1561)))) else (if j < 168 then (if j < 165 then (if j < 163 then data1562 else (if j < 164 then data1563 else data1564)) else (if j < 166 then data1565 else (if j < 167 then data1566 else data1567))) else (if j < 171 then (if j < 169 then data1568 else (if j < 170 then data1569 else data1570)) else (if j < 173 then (if j < 172 then data1571 else data1572) else (if j < 174 then data1573 else data1574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data1575 else (if j < 177 then data1576 else data1577)) else (if j < 179 then data1578 else (if j < 180 then data1579 else data1580))) else (if j < 184 then (if j < 182 then data1581 else (if j < 183 then data1582 else data1583)) else (if j < 185 then data1584 else (if j < 186 then data1585 else data1586)))) else (if j < 193 then (if j < 190 then (if j < 188 then data1587 else (if j < 189 then data1588 else data1589)) else (if j < 191 then data1590 else (if j < 192 then data1591 else data1592))) else (if j < 196 then (if j < 194 then data1593 else (if j < 195 then data1594 else data1595)) else (if j < 198 then (if j < 197 then data1596 else data1597) else (if j < 199 then data1598 else data1599))))))))

def srcTableB7 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src1400 else (if j < 2 then src1401 else src1402)) else (if j < 4 then src1403 else (if j < 5 then src1404 else src1405))) else (if j < 9 then (if j < 7 then src1406 else (if j < 8 then src1407 else src1408)) else (if j < 10 then src1409 else (if j < 11 then src1410 else src1411)))) else (if j < 18 then (if j < 15 then (if j < 13 then src1412 else (if j < 14 then src1413 else src1414)) else (if j < 16 then src1415 else (if j < 17 then src1416 else src1417))) else (if j < 21 then (if j < 19 then src1418 else (if j < 20 then src1419 else src1420)) else (if j < 23 then (if j < 22 then src1421 else src1422) else (if j < 24 then src1423 else src1424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src1425 else (if j < 27 then src1426 else src1427)) else (if j < 29 then src1428 else (if j < 30 then src1429 else src1430))) else (if j < 34 then (if j < 32 then src1431 else (if j < 33 then src1432 else src1433)) else (if j < 35 then src1434 else (if j < 36 then src1435 else src1436)))) else (if j < 43 then (if j < 40 then (if j < 38 then src1437 else (if j < 39 then src1438 else src1439)) else (if j < 41 then src1440 else (if j < 42 then src1441 else src1442))) else (if j < 46 then (if j < 44 then src1443 else (if j < 45 then src1444 else src1445)) else (if j < 48 then (if j < 47 then src1446 else src1447) else (if j < 49 then src1448 else src1449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src1450 else (if j < 52 then src1451 else src1452)) else (if j < 54 then src1453 else (if j < 55 then src1454 else src1455))) else (if j < 59 then (if j < 57 then src1456 else (if j < 58 then src1457 else src1458)) else (if j < 60 then src1459 else (if j < 61 then src1460 else src1461)))) else (if j < 68 then (if j < 65 then (if j < 63 then src1462 else (if j < 64 then src1463 else src1464)) else (if j < 66 then src1465 else (if j < 67 then src1466 else src1467))) else (if j < 71 then (if j < 69 then src1468 else (if j < 70 then src1469 else src1470)) else (if j < 73 then (if j < 72 then src1471 else src1472) else (if j < 74 then src1473 else src1474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src1475 else (if j < 77 then src1476 else src1477)) else (if j < 79 then src1478 else (if j < 80 then src1479 else src1480))) else (if j < 84 then (if j < 82 then src1481 else (if j < 83 then src1482 else src1483)) else (if j < 85 then src1484 else (if j < 86 then src1485 else src1486)))) else (if j < 93 then (if j < 90 then (if j < 88 then src1487 else (if j < 89 then src1488 else src1489)) else (if j < 91 then src1490 else (if j < 92 then src1491 else src1492))) else (if j < 96 then (if j < 94 then src1493 else (if j < 95 then src1494 else src1495)) else (if j < 98 then (if j < 97 then src1496 else src1497) else (if j < 99 then src1498 else src1499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src1500 else (if j < 102 then src1501 else src1502)) else (if j < 104 then src1503 else (if j < 105 then src1504 else src1505))) else (if j < 109 then (if j < 107 then src1506 else (if j < 108 then src1507 else src1508)) else (if j < 110 then src1509 else (if j < 111 then src1510 else src1511)))) else (if j < 118 then (if j < 115 then (if j < 113 then src1512 else (if j < 114 then src1513 else src1514)) else (if j < 116 then src1515 else (if j < 117 then src1516 else src1517))) else (if j < 121 then (if j < 119 then src1518 else (if j < 120 then src1519 else src1520)) else (if j < 123 then (if j < 122 then src1521 else src1522) else (if j < 124 then src1523 else src1524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src1525 else (if j < 127 then src1526 else src1527)) else (if j < 129 then src1528 else (if j < 130 then src1529 else src1530))) else (if j < 134 then (if j < 132 then src1531 else (if j < 133 then src1532 else src1533)) else (if j < 135 then src1534 else (if j < 136 then src1535 else src1536)))) else (if j < 143 then (if j < 140 then (if j < 138 then src1537 else (if j < 139 then src1538 else src1539)) else (if j < 141 then src1540 else (if j < 142 then src1541 else src1542))) else (if j < 146 then (if j < 144 then src1543 else (if j < 145 then src1544 else src1545)) else (if j < 148 then (if j < 147 then src1546 else src1547) else (if j < 149 then src1548 else src1549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src1550 else (if j < 152 then src1551 else src1552)) else (if j < 154 then src1553 else (if j < 155 then src1554 else src1555))) else (if j < 159 then (if j < 157 then src1556 else (if j < 158 then src1557 else src1558)) else (if j < 160 then src1559 else (if j < 161 then src1560 else src1561)))) else (if j < 168 then (if j < 165 then (if j < 163 then src1562 else (if j < 164 then src1563 else src1564)) else (if j < 166 then src1565 else (if j < 167 then src1566 else src1567))) else (if j < 171 then (if j < 169 then src1568 else (if j < 170 then src1569 else src1570)) else (if j < 173 then (if j < 172 then src1571 else src1572) else (if j < 174 then src1573 else src1574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src1575 else (if j < 177 then src1576 else src1577)) else (if j < 179 then src1578 else (if j < 180 then src1579 else src1580))) else (if j < 184 then (if j < 182 then src1581 else (if j < 183 then src1582 else src1583)) else (if j < 185 then src1584 else (if j < 186 then src1585 else src1586)))) else (if j < 193 then (if j < 190 then (if j < 188 then src1587 else (if j < 189 then src1588 else src1589)) else (if j < 191 then src1590 else (if j < 192 then src1591 else src1592))) else (if j < 196 then (if j < 194 then src1593 else (if j < 195 then src1594 else src1595)) else (if j < 198 then (if j < 197 then src1596 else src1597) else (if j < 199 then src1598 else src1599))))))))

def dstTableB7 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst1400 else (if j < 2 then dst1401 else dst1402)) else (if j < 4 then dst1403 else (if j < 5 then dst1404 else dst1405))) else (if j < 9 then (if j < 7 then dst1406 else (if j < 8 then dst1407 else dst1408)) else (if j < 10 then dst1409 else (if j < 11 then dst1410 else dst1411)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst1412 else (if j < 14 then dst1413 else dst1414)) else (if j < 16 then dst1415 else (if j < 17 then dst1416 else dst1417))) else (if j < 21 then (if j < 19 then dst1418 else (if j < 20 then dst1419 else dst1420)) else (if j < 23 then (if j < 22 then dst1421 else dst1422) else (if j < 24 then dst1423 else dst1424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst1425 else (if j < 27 then dst1426 else dst1427)) else (if j < 29 then dst1428 else (if j < 30 then dst1429 else dst1430))) else (if j < 34 then (if j < 32 then dst1431 else (if j < 33 then dst1432 else dst1433)) else (if j < 35 then dst1434 else (if j < 36 then dst1435 else dst1436)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst1437 else (if j < 39 then dst1438 else dst1439)) else (if j < 41 then dst1440 else (if j < 42 then dst1441 else dst1442))) else (if j < 46 then (if j < 44 then dst1443 else (if j < 45 then dst1444 else dst1445)) else (if j < 48 then (if j < 47 then dst1446 else dst1447) else (if j < 49 then dst1448 else dst1449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst1450 else (if j < 52 then dst1451 else dst1452)) else (if j < 54 then dst1453 else (if j < 55 then dst1454 else dst1455))) else (if j < 59 then (if j < 57 then dst1456 else (if j < 58 then dst1457 else dst1458)) else (if j < 60 then dst1459 else (if j < 61 then dst1460 else dst1461)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst1462 else (if j < 64 then dst1463 else dst1464)) else (if j < 66 then dst1465 else (if j < 67 then dst1466 else dst1467))) else (if j < 71 then (if j < 69 then dst1468 else (if j < 70 then dst1469 else dst1470)) else (if j < 73 then (if j < 72 then dst1471 else dst1472) else (if j < 74 then dst1473 else dst1474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst1475 else (if j < 77 then dst1476 else dst1477)) else (if j < 79 then dst1478 else (if j < 80 then dst1479 else dst1480))) else (if j < 84 then (if j < 82 then dst1481 else (if j < 83 then dst1482 else dst1483)) else (if j < 85 then dst1484 else (if j < 86 then dst1485 else dst1486)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst1487 else (if j < 89 then dst1488 else dst1489)) else (if j < 91 then dst1490 else (if j < 92 then dst1491 else dst1492))) else (if j < 96 then (if j < 94 then dst1493 else (if j < 95 then dst1494 else dst1495)) else (if j < 98 then (if j < 97 then dst1496 else dst1497) else (if j < 99 then dst1498 else dst1499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst1500 else (if j < 102 then dst1501 else dst1502)) else (if j < 104 then dst1503 else (if j < 105 then dst1504 else dst1505))) else (if j < 109 then (if j < 107 then dst1506 else (if j < 108 then dst1507 else dst1508)) else (if j < 110 then dst1509 else (if j < 111 then dst1510 else dst1511)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst1512 else (if j < 114 then dst1513 else dst1514)) else (if j < 116 then dst1515 else (if j < 117 then dst1516 else dst1517))) else (if j < 121 then (if j < 119 then dst1518 else (if j < 120 then dst1519 else dst1520)) else (if j < 123 then (if j < 122 then dst1521 else dst1522) else (if j < 124 then dst1523 else dst1524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst1525 else (if j < 127 then dst1526 else dst1527)) else (if j < 129 then dst1528 else (if j < 130 then dst1529 else dst1530))) else (if j < 134 then (if j < 132 then dst1531 else (if j < 133 then dst1532 else dst1533)) else (if j < 135 then dst1534 else (if j < 136 then dst1535 else dst1536)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst1537 else (if j < 139 then dst1538 else dst1539)) else (if j < 141 then dst1540 else (if j < 142 then dst1541 else dst1542))) else (if j < 146 then (if j < 144 then dst1543 else (if j < 145 then dst1544 else dst1545)) else (if j < 148 then (if j < 147 then dst1546 else dst1547) else (if j < 149 then dst1548 else dst1549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst1550 else (if j < 152 then dst1551 else dst1552)) else (if j < 154 then dst1553 else (if j < 155 then dst1554 else dst1555))) else (if j < 159 then (if j < 157 then dst1556 else (if j < 158 then dst1557 else dst1558)) else (if j < 160 then dst1559 else (if j < 161 then dst1560 else dst1561)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst1562 else (if j < 164 then dst1563 else dst1564)) else (if j < 166 then dst1565 else (if j < 167 then dst1566 else dst1567))) else (if j < 171 then (if j < 169 then dst1568 else (if j < 170 then dst1569 else dst1570)) else (if j < 173 then (if j < 172 then dst1571 else dst1572) else (if j < 174 then dst1573 else dst1574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst1575 else (if j < 177 then dst1576 else dst1577)) else (if j < 179 then dst1578 else (if j < 180 then dst1579 else dst1580))) else (if j < 184 then (if j < 182 then dst1581 else (if j < 183 then dst1582 else dst1583)) else (if j < 185 then dst1584 else (if j < 186 then dst1585 else dst1586)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst1587 else (if j < 189 then dst1588 else dst1589)) else (if j < 191 then dst1590 else (if j < 192 then dst1591 else dst1592))) else (if j < 196 then (if j < 194 then dst1593 else (if j < 195 then dst1594 else dst1595)) else (if j < 198 then (if j < 197 then dst1596 else dst1597) else (if j < 199 then dst1598 else dst1599))))))))

def caseB7 (i : Fin 200) : Cases := ⟨1400 + i.val,by have := i.isLt; omega⟩
lemma tableB7_valid (i : Fin 200) :
    (lookupB7 i.val).Valid (srcTableB7 i.val) (dstTableB7 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data1400
  · exact valid_data1401
  · exact valid_data1402
  · exact valid_data1403
  · exact valid_data1404
  · exact valid_data1405
  · exact valid_data1406
  · exact valid_data1407
  · exact valid_data1408
  · exact valid_data1409
  · exact valid_data1410
  · exact valid_data1411
  · exact valid_data1412
  · exact valid_data1413
  · exact valid_data1414
  · exact valid_data1415
  · exact valid_data1416
  · exact valid_data1417
  · exact valid_data1418
  · exact valid_data1419
  · exact valid_data1420
  · exact valid_data1421
  · exact valid_data1422
  · exact valid_data1423
  · exact valid_data1424
  · exact valid_data1425
  · exact valid_data1426
  · exact valid_data1427
  · exact valid_data1428
  · exact valid_data1429
  · exact valid_data1430
  · exact valid_data1431
  · exact valid_data1432
  · exact valid_data1433
  · exact valid_data1434
  · exact valid_data1435
  · exact valid_data1436
  · exact valid_data1437
  · exact valid_data1438
  · exact valid_data1439
  · exact valid_data1440
  · exact valid_data1441
  · exact valid_data1442
  · exact valid_data1443
  · exact valid_data1444
  · exact valid_data1445
  · exact valid_data1446
  · exact valid_data1447
  · exact valid_data1448
  · exact valid_data1449
  · exact valid_data1450
  · exact valid_data1451
  · exact valid_data1452
  · exact valid_data1453
  · exact valid_data1454
  · exact valid_data1455
  · exact valid_data1456
  · exact valid_data1457
  · exact valid_data1458
  · exact valid_data1459
  · exact valid_data1460
  · exact valid_data1461
  · exact valid_data1462
  · exact valid_data1463
  · exact valid_data1464
  · exact valid_data1465
  · exact valid_data1466
  · exact valid_data1467
  · exact valid_data1468
  · exact valid_data1469
  · exact valid_data1470
  · exact valid_data1471
  · exact valid_data1472
  · exact valid_data1473
  · exact valid_data1474
  · exact valid_data1475
  · exact valid_data1476
  · exact valid_data1477
  · exact valid_data1478
  · exact valid_data1479
  · exact valid_data1480
  · exact valid_data1481
  · exact valid_data1482
  · exact valid_data1483
  · exact valid_data1484
  · exact valid_data1485
  · exact valid_data1486
  · exact valid_data1487
  · exact valid_data1488
  · exact valid_data1489
  · exact valid_data1490
  · exact valid_data1491
  · exact valid_data1492
  · exact valid_data1493
  · exact valid_data1494
  · exact valid_data1495
  · exact valid_data1496
  · exact valid_data1497
  · exact valid_data1498
  · exact valid_data1499
  · exact valid_data1500
  · exact valid_data1501
  · exact valid_data1502
  · exact valid_data1503
  · exact valid_data1504
  · exact valid_data1505
  · exact valid_data1506
  · exact valid_data1507
  · exact valid_data1508
  · exact valid_data1509
  · exact valid_data1510
  · exact valid_data1511
  · exact valid_data1512
  · exact valid_data1513
  · exact valid_data1514
  · exact valid_data1515
  · exact valid_data1516
  · exact valid_data1517
  · exact valid_data1518
  · exact valid_data1519
  · exact valid_data1520
  · exact valid_data1521
  · exact valid_data1522
  · exact valid_data1523
  · exact valid_data1524
  · exact valid_data1525
  · exact valid_data1526
  · exact valid_data1527
  · exact valid_data1528
  · exact valid_data1529
  · exact valid_data1530
  · exact valid_data1531
  · exact valid_data1532
  · exact valid_data1533
  · exact valid_data1534
  · exact valid_data1535
  · exact valid_data1536
  · exact valid_data1537
  · exact valid_data1538
  · exact valid_data1539
  · exact valid_data1540
  · exact valid_data1541
  · exact valid_data1542
  · exact valid_data1543
  · exact valid_data1544
  · exact valid_data1545
  · exact valid_data1546
  · exact valid_data1547
  · exact valid_data1548
  · exact valid_data1549
  · exact valid_data1550
  · exact valid_data1551
  · exact valid_data1552
  · exact valid_data1553
  · exact valid_data1554
  · exact valid_data1555
  · exact valid_data1556
  · exact valid_data1557
  · exact valid_data1558
  · exact valid_data1559
  · exact valid_data1560
  · exact valid_data1561
  · exact valid_data1562
  · exact valid_data1563
  · exact valid_data1564
  · exact valid_data1565
  · exact valid_data1566
  · exact valid_data1567
  · exact valid_data1568
  · exact valid_data1569
  · exact valid_data1570
  · exact valid_data1571
  · exact valid_data1572
  · exact valid_data1573
  · exact valid_data1574
  · exact valid_data1575
  · exact valid_data1576
  · exact valid_data1577
  · exact valid_data1578
  · exact valid_data1579
  · exact valid_data1580
  · exact valid_data1581
  · exact valid_data1582
  · exact valid_data1583
  · exact valid_data1584
  · exact valid_data1585
  · exact valid_data1586
  · exact valid_data1587
  · exact valid_data1588
  · exact valid_data1589
  · exact valid_data1590
  · exact valid_data1591
  · exact valid_data1592
  · exact valid_data1593
  · exact valid_data1594
  · exact valid_data1595
  · exact valid_data1596
  · exact valid_data1597
  · exact valid_data1598
  · exact valid_data1599

lemma srcB7_row : ∀ (i : Fin 200) (e : E),
    srcTableB7 i.val e = caseSource (caseB7 i) e := by decide +kernel

lemma dstB7_row : ∀ (i : Fin 200) (e : E),
    dstTableB7 i.val e = caseTarget (caseB7 i) e := by decide +kernel

lemma sizeB7 : ∀ i : Fin 200, (lookupB7 i.val).size ≤ 5 →
    (lookupB7 i.val).size = 2 ∧
      (⟨caseKey (caseB7 i),caseKey_lt (caseB7 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB7 (i : Fin 200) : Certificate (caseB7 i) := by
  refine ⟨lookupB7 i.val,?_,sizeB7 i⟩
  have hv := tableB7_valid i
  rw [funext (srcB7_row i),funext (dstB7_row i)] at hv
  exact hv
lemma certificateInterval7 : FiniteIntervals.Covers CertificateAt 1400 1600 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1400 200 (fun i _ => certificateB7 i)
#print axioms certificateInterval7
end Erdos184Work.FiveRows3
